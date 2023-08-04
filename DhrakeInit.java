// Uses metadata from an IDR-generated IDC script to rename symbols
// and fix certain calls in Delphi programs
//@category Delphi
//@author Jesko Huettenhain

import ghidra.app.decompiler.DecompInterface;
import ghidra.app.decompiler.DecompileResults;
import ghidra.app.script.GhidraScript;
import ghidra.program.model.address.Address;
import ghidra.program.model.address.AddressSet;
import ghidra.program.model.data.*;
import ghidra.program.model.lang.Register;
import ghidra.program.model.listing.*;
import ghidra.program.model.listing.Function.FunctionUpdateType;
import ghidra.program.model.pcode.*;
import ghidra.program.model.scalar.Scalar;
import ghidra.program.model.symbol.RefType;
import ghidra.program.model.symbol.Reference;
import ghidra.program.model.symbol.SourceType;
import ghidra.program.model.symbol.SymbolTable;
import ghidra.program.model.util.CodeUnitInsertionException;
import ghidra.util.exception.CancelledException;
import ghidra.util.exception.DuplicateNameException;
import ghidra.util.exception.InvalidInputException;

import java.io.BufferedInputStream;
import java.io.File;
import java.io.FileInputStream;
import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.util.*;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

public class DhrakeInit extends GhidraScript {

	static DataType CHAR = CharDataType.dataType;
	static DataType BYTE = ByteDataType.dataType;
	static DataType WCHAR = WideCharDataType.dataType;
	static DataType LPCSTR = PointerDataType.getPointer(CHAR, 4);
	static DataType LPWSTR = PointerDataType.getPointer(WCHAR, 4);
	static DataType LPBYTE = PointerDataType.getPointer(BYTE, 4);
	static DataType LPPCSTR = PointerDataType.getPointer(LPCSTR, 4);
	static DataType LPPWSTR = PointerDataType.getPointer(LPWSTR, 4);
	static DataType UINT = UnsignedIntegerDataType.dataType;
	static DataType BOOL = BooleanDataType.dataType;

	static SourceType DhrakeSource = SourceType.ANALYSIS;

	private void renameSymbol(Address entryPoint, String name) throws InvalidInputException {
		this.renameSymbol(entryPoint, name, DhrakeSource);
	}

	private void renameSymbol(Address entryPoint, String name, SourceType type) throws InvalidInputException {
		Function f = this.getFunctionAt(entryPoint);
		SymbolTable symbolTable = currentProgram.getSymbolTable();
		String finalName = name;

		for (int counter = 0; counter < 100; counter++) {
			try {
				if (f != null) {
					f.setName(finalName, type);
				} else {
					symbolTable.createLabel(entryPoint, finalName, type);
				}
				break;
			} catch (DuplicateNameException d) {
				finalName = String.format("%s_%02d", name, counter);
			}
		}
	}

	private void logMsg(String message, Object... args) {
		this.println(String.format("[Dhrake] %s", String.format(message, args)));
	}

	private long getConstantCallArgument(Function caller, Address addr, int index) throws IllegalStateException {
		// This is a very reliable and slow fallback to determine the value of a constant argument
		// to a function call at a given address within a given function.
		monitor.setMessage("obtaining decompiler interface");
		DecompInterface decompInterface = new DecompInterface();
		decompInterface.openProgram(currentProgram);
		monitor.setMessage("decompiling");
		DecompileResults decompileResults = decompInterface.decompileFunction(caller, 120, monitor);
		if (!decompileResults.decompileCompleted())
			throw new IllegalStateException();
		monitor.setMessage("searching for call argument");
		HighFunction highFunction = decompileResults.getHighFunction();
		Iterator<PcodeOpAST> pCodes = highFunction.getPcodeOps(addr);
		while (pCodes.hasNext()) {
			PcodeOpAST instruction = pCodes.next();
			if (instruction.getOpcode() == PcodeOp.CALL) {
				Varnode argument = instruction.getInput(index);
				if (!argument.isConstant())
					throw new IllegalStateException();
				return argument.getOffset();
			}
		}
		throw new IllegalStateException();
	}

	private long getStrCatCount(Function caller, Address addr) {
		// Usually, the second (constant) argument to a *StrCatN function is assigned to
		// the EDX register right before the call instruction. This method attempts to
		// read the value by parsing the disassembly first and falls back to a decompiler
		// based approach if any assumption fails.
		try {
			Instruction insn = this.getInstructionBefore(addr);
			if (insn == null || insn.getNumOperands() != 2)
				return this.getConstantCallArgument(caller, addr, 2);
			Object[] EDX = insn.getOpObjects(0);
			Object[] IMM = insn.getOpObjects(1);
			if (insn.getOperandRefType(0) != RefType.WRITE)
				return this.getConstantCallArgument(caller, addr, 2);
			if (EDX.length != 1 || !(EDX[0] instanceof Register))
				return this.getConstantCallArgument(caller, addr, 2);
			if (((Register) EDX[0]).getName().compareTo("EDX") != 0)
				return this.getConstantCallArgument(caller, addr, 2);
			if (IMM.length != 1 || !(IMM[0] instanceof Scalar))
				return this.getConstantCallArgument(caller, addr, 2);
			return ((Scalar) IMM[0]).getUnsignedValue();
		} catch (IllegalStateException e) {
			return -1;
		}
	}

	private void overrideStrCatN(String name, DataType LPTSTR) {
		// This method fixes a *StrCatN function for string pointers of the given data type LPTSTR.
		DataType PPTSTR = PointerDataType.getPointer(LPTSTR, currentProgram.getDataTypeManager());
		Iterator<Function> functions = this.getGlobalFunctions(name).iterator();
		while (functions.hasNext()) {
			Function    StrCatN = functions.next();
			Reference[] refs    = this.getReferencesTo(StrCatN.getEntryPoint());
			StrCatN.setVarArgs(true);

			try {
				StrCatN.replaceParameters(
						FunctionUpdateType.DYNAMIC_STORAGE_ALL_PARAMS,
						true,
						DhrakeSource,
						new ParameterImpl("Result", PPTSTR, currentProgram),
						new ParameterImpl("Count", UINT, currentProgram)
				);
			} catch (Exception e) {
				long offset = StrCatN.getEntryPoint().getOffset();
				this.logMsg("%08X Unable to correctly retype %s.", offset, name);
			}

			monitor.setMaximum(refs.length);
			monitor.setProgress(0);
			monitor.setMessage(String.format("Obtaining references to %s.", name));
			for (int j=0; j < refs.length; j++) {
				Reference ref = refs[j];
				if (ref.getReferenceType() == RefType.UNCONDITIONAL_CALL) {
					Address addr = ref.getFromAddress();
					Function caller = this.getFunctionBefore(addr);
					long count = this.getStrCatCount(caller, addr);
					long offset = addr.getOffset();
					if (count < 0) {
						this.logMsg("%08X %s call with N unknown, skipping", offset, name);
					}
					FunctionDefinitionDataType signature = new FunctionDefinitionDataType(name);
					List<ParameterDefinitionImpl> args = new ArrayList<>();
					args.add(new ParameterDefinitionImpl("Destination", PPTSTR, "Receives the concatenated string"));
					args.add(new ParameterDefinitionImpl("StringCount", UINT, "The number of strings to be concatenated"));

					// Unfortunately, I know of no way to make HighFunctionDBUtil.writeOverride override
					// a function call in such a manner that custom storage can be used. Now, *StrCatN expects
					// the first two arguments in EAX and EDX, and all the remaining arguments on the stack.
					// However, the __register calling convention also dictates that the third parameter is
					// passed in the ECX register. The best solution I could come up with is to add a dummy
					// variable which represents this third argument, which does not actually exist:
					args.add(new ParameterDefinitionImpl(
							String.format("__dummy_%02d", offset & 0xFF), UINT, "Dummy Variable"));

					for (long k=0; k < count; k++)
						args.add(new ParameterDefinitionImpl(String.format("String%d", count - k), LPTSTR, ""));

					signature.setArguments(args.toArray(new ParameterDefinitionImpl[args.size()]));
					signature.setReturnType(UINT);
					signature.setVarArgs(false);
					int transaction = currentProgram.startTransaction(
							String.format("Fixing call to %s at %08X", name, offset));
					boolean success = false;
					try {
						HighFunctionDBUtil.writeOverride(caller, addr, signature);
						this.logMsg("%08X %s call with N=%d was fixed.", offset, name, count);
						success = true;
					} catch (Exception e) {
						this.logMsg("%08X %s call with N=%d could not be fixed.", offset, name, count);
					} finally {
						currentProgram.endTransaction(transaction, success);
					}
				}
				monitor.setProgress(j);
			}
		}
	}

	private boolean importSymbolsFromIDC() {
		File idc;
		long progress = 0;
		int linecount = 0;
		int countSymbols = 0;
		int countStrings = 0;
		int countVMTs = 0;

		monitor.setMessage("Loading symbols from IDC");

		try {
			idc = this.askFile("IDC File Path", "Load an IDC file");
		} catch (CancelledException e) {
			return false;
		}

		Pattern makeName = Pattern.compile("^\\s*MakeNameEx\\((?:0x)?([A-Fa-f0-9]+),\\s*\"([^\"]*)\",\\s*([xA-Fa-f0-9]+)\\);\\s*$");

		// String Type: group 1
		Pattern stringType = Pattern.compile("^\\s*SetLongPrm\\(INF_STRTYPE,\\s*ASCSTR_(PASCAL|TERMCHR|UNICODE)\\);\\s*$");

		// Both combined: group 1 = position, group 2 = end or null
		Pattern makeString = Pattern.compile("^\\s*MakeStr\\((?:0x)?([A-Fa-f0-9]+),\\s*(?:0x)?([-1|A-Fa-f0-9]+)\\s*\\);\\s*$");

		try (BufferedInputStream inputStream = new BufferedInputStream(new FileInputStream(idc));  Scanner sc = new Scanner(inputStream, StandardCharsets.UTF_8)) {
			// Count lines
			while (sc.hasNextLine()) {
				sc.nextLine();
				linecount++;
			}
			monitor.setMaximum(linecount);
		} catch (IOException e) {
			this.logMsg("file not found: %s", idc.toPath());
			return false;
		}

		try (BufferedInputStream inputStream  = new BufferedInputStream(new FileInputStream(idc));  Scanner sc = new Scanner(inputStream, StandardCharsets.UTF_8)) {
            monitor.setMessage("Processing IDC file");
            this.logMsg("Processing IDC file %s", idc.toPath());

			String foundStringType = "";

			while (sc.hasNextLine()) {
                if (monitor.isCancelled()) break;

				String line = sc.nextLine();

				monitor.setProgress(progress++);

				if (!line.contains("MakeNameEx") && !line.contains("SetLongPrm")) continue;

				Matcher funcMatch = makeName.matcher(line);
				Matcher stringTypeMatch = stringType.matcher(line);

				if (!funcMatch.matches() && !stringTypeMatch.matches()) continue;

				// Match: Function
				if (funcMatch.matches()) {
					long offset = Long.parseUnsignedLong(funcMatch.group(1), 16);
					Address entryPoint = this.toAddr(offset);
					String symName = funcMatch.group(2);
					monitor.setMessage(symName);

					if (symName.strip().length() > 0) {
						try {
							this.logMsg("Renaming symbol at %s to %s", entryPoint, symName);
							this.renameSymbol(entryPoint, symName);
							countSymbols++;
						} catch (InvalidInputException e) {
							this.logMsg("Renaming failed for: %s", symName);
						}
					}
					continue;
				}

				// Match: String
				if (stringTypeMatch.matches()) {
					foundStringType = stringTypeMatch.group(1);
					line = sc.nextLine();
					Matcher stringMatch = makeString.matcher(line);

					if (stringMatch.matches()) {
						long start  = Long.parseUnsignedLong(stringMatch.group(1), 16);
						long end    = Long.parseLong(stringMatch.group(2), 16);
						long length = end > start ? end - start : -1;

						Address startAddr = this.toAddr(start);
						Address endAddr   = this.toAddr(end);

						// Debug:
						// monitor.setMessage(String.format("Found %s string at %s", foundStringType, startAddr.toString()));
						// logMsg(String.format("Line %s found %s string at %s", progress, foundStringType, startAddr));

						// Process Unicode strings for now
						if (foundStringType.equals("UNICODE")) {
							createPascalString(foundStringType, startAddr, endAddr, length);
							countStrings++;
						}

						// Notes to self:
						// PASCAL = ShortString => 'PascalString255' (ikString)
						// TERMCHR = String (L) = Pointer String, AnsiString (L,R) => 'PascalString'
						//   If TERMCHR has a length, can be: PChar, PAnsiChar (ikCString)
						//   If TERMCHR has a length of -1, it's an AnsiString (ikLString)
						// UNICODE = WideString (L), Unicode (L,R,W,C) => 'PascalUnicode'
					}
				}
			}
		} catch (IOException e) {
			this.logMsg("file not found: %s", idc.toPath());
			return false;
		}

		this.logMsg("Total symbols: %d", countSymbols);
		this.logMsg("Total strings: %d", countStrings);
		this.logMsg("Total VMTs   : %d", countVMTs);

		return true;
	}

	private void createPascalString(String type, Address start, Address end, long length) {
		try {
			if (this.getReferencesFrom(start).length > 0) {
				this.logMsg("Found references from %s", start);
				if (this.getReferencesTo(start).length > 0) {
					this.logMsg("Found references to %s", start);
				}
				return;
			}

			// move this up
			if (this.getDataAt(start) != null) {
				if (this.getDataAt(start).isDefined()) {
					this.logMsg("Data is defined at %s", start);
				}

				if (this.getDataAt(start).isPointer()) {
					this.logMsg("Data defined at %s is a pointer", start);
					return;
				}
			}

			if (this.getDataAfter(start).hasStringValue()) {
				this.logMsg("Data after %s => %s has a string value", start, start.next());
				if (length > 0) {
					this.clearListing(new AddressSet(start, end));
				} else {
					this.clearListing(start);
				}
			}

			// todo: allow user to adjust the minimum length
			if (length > 5) {
           		if (this.getDataAt(start) == null) {
					this.logMsg("Found %s string at %s", type, start);

					switch (type) {
						case "PASCAL" -> this.createData(start, new PascalString255DataType());
						case "TERMCHR" -> this.createData(start, new PascalStringDataType());
						case "UNICODE" -> this.createData(start, new UnicodeDataType());
						// case "UNICODE" -> this.createData(start, new PascalUnicodeDataType());
					}
				}
			}
		} catch (CodeUnitInsertionException e) {
			this.logMsg("Cannot create string, conflicting data at address %s", start);
		} catch (Exception e) {
			this.logMsg("Cannot create string at %s, exception: %s", start, e);
		}
	}

	private void repairStringCompareFunctions() {
		try {
			monitor.setMessage("Repairing known function signatures");

			VariableStorage zfReturn = new VariableStorage(
					currentProgram, currentProgram.getRegister("ZF"));
			Map<String, DataType[]> comparators = Map.of(
					"@PStrCmp", new DataType[] { LPBYTE, LPBYTE },
					"@LStrCmp", new DataType[] { LPCSTR, LPCSTR },
					"@WStrCmp", new DataType[] { LPWSTR, LPWSTR },
					"@UStrCmp", new DataType[] { LPWSTR, LPWSTR },
					"@AStrCmp", new DataType[] { LPCSTR, LPCSTR, UINT }
			);
			Register argLocations[] = new Register[] {
					currentProgram.getRegister("EAX"),
					currentProgram.getRegister("EDX"),
					currentProgram.getRegister("ECX")
			};
			String[] argNames = new String[] {"a", "b", "size"};

			for (Map.Entry<String, DataType[]> cmp : comparators.entrySet()) {
				Iterator<Function> functions = this.getGlobalFunctions(cmp.getKey()).iterator();
				while (functions.hasNext()) {
					Function function = functions.next();
					function.setCustomVariableStorage(true);
					function.setReturn(BOOL, zfReturn, DhrakeSource);
					DataType[] argTypes = cmp.getValue();
					List <ParameterImpl> args     = new ArrayList<>();
					for (int k = 0; k < argTypes.length; k++)
						args.add(new ParameterImpl(argNames[k], argTypes[k], argLocations[k], currentProgram));
					ParameterImpl[] argumentArray = args.toArray(new ParameterImpl[args.size()]);
					try {
						function.replaceParameters(
								FunctionUpdateType.CUSTOM_STORAGE, true, DhrakeSource, argumentArray
						);
					} catch (DuplicateNameException e) {
						this.logMsg("%08X Unable to correctly retype %s.",
									function.getEntryPoint().getOffset(), cmp.getKey()
						);
					}
				}
			}
		} catch (InvalidInputException e1) {
			this.logMsg("Unexpected error obtaining registers");
		}
	}

	public void repairLibraryFunctionSignatures() {

		this.overrideStrCatN("@LStrCatN", LPCSTR);
		this.overrideStrCatN("@WStrCatN", LPWSTR);
		this.overrideStrCatN("@UStrCatN", LPWSTR);

		this.repairStringCompareFunctions();

		Map<String, DataType[]> comparators = Map.of(
				"@LStrCat3", new DataType[] { LPPCSTR, LPCSTR, LPCSTR },
				"@UStrCat3", new DataType[] { LPPWSTR, LPWSTR, LPWSTR },
				"@WStrCat3", new DataType[] { LPPWSTR, LPWSTR, LPWSTR }
		);

		for (Map.Entry<String, DataType[]> sig : comparators.entrySet()) {
			Iterator<Function> functions = this.getGlobalFunctions(sig.getKey()).iterator();
			while (functions.hasNext()) {
                Function   function = functions.next();
                DataType[] argTypes = sig.getValue();
				List <ParameterImpl> args     = new ArrayList<>();
				try {
					for (int k = 0; k < argTypes.length; k++)
						args.add(new ParameterImpl(String.format("a%d", k), argTypes[k], currentProgram));
					ParameterImpl[] argumentArray = args.toArray(new ParameterImpl[args.size()]);
					function.replaceParameters(
							FunctionUpdateType.DYNAMIC_STORAGE_ALL_PARAMS, true, DhrakeSource, argumentArray
					);
				} catch (Exception e) {
					this.logMsg("%08X Unable to correctly retype %s.",
								function.getEntryPoint().getOffset(), sig.getKey()
					);
				}
			}
		}
	}

	private void repairWrongFunctionEntries() {
		// This function attempts to detect and fix situations where Ghidra has incorrectly placed
		// the entry point of a Delphi function after the actual entry point.

		Function previousFunction = this.getFunctionAfter(this.getAddressFactory().getAddress("0"));
		Function currentFunction;
		FunctionManager functionManager = currentProgram.getFunctionManager();

		int transaction = currentProgram.startTransaction("fixing erroneous function entries");
		boolean success = true;
		try {
			while ((currentFunction = this.getFunctionAfter(previousFunction)) != null) {
				if (!previousFunction.isThunk()) {
					Address start = previousFunction.getEntryPoint();
					Address end = previousFunction.getBody().getMaxAddress();
					long size = end.getOffset() - start.getOffset();
					int refCount = this.getReferencesTo(currentFunction.getEntryPoint()).length;
					if (size <= 24 && refCount == 0) {
						String name = previousFunction.getName();
						Address next = currentFunction.getBody().getMaxAddress();
						functionManager.deleteAddressRange(start, next, monitor);
						this.createFunction(start, name);
						currentFunction = this.getFunctionAfter(end);
					}
				}
				previousFunction = currentFunction;
			}
		} catch (Exception e) {
			success = false;
		} finally {
			currentProgram.endTransaction(transaction, success);
		}
	}

	public void run()  {
		monitor.setCancelEnabled(true);
		monitor.setShowProgressValue(true);

		if (!this.importSymbolsFromIDC())
			return;

		this.repairWrongFunctionEntries();
		this.repairLibraryFunctionSignatures();
	}

}
