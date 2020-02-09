//Uses metadata from an IDR generated IDC script to rename symbols
//and fix certain calls in Delphi programs
//@category Delphi
//@author Jesko Huettenhain

import java.io.File;
import java.io.IOException;
import java.nio.charset.Charset;
import java.nio.file.Files;
import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import ghidra.app.decompiler.DecompInterface;
import ghidra.app.decompiler.DecompileResults;
import ghidra.app.script.GhidraScript;
import ghidra.util.exception.CancelledException;
import ghidra.util.exception.DuplicateNameException;
import ghidra.util.exception.InvalidInputException;
import ghidra.program.model.symbol.*;
import ghidra.program.model.listing.*;
import ghidra.program.model.listing.Function.FunctionUpdateType;
import ghidra.program.model.pcode.HighFunction;
import ghidra.program.model.pcode.HighFunctionDBUtil;
import ghidra.program.model.pcode.PcodeOp;
import ghidra.program.model.pcode.PcodeOpAST;
import ghidra.program.model.pcode.Varnode;
import ghidra.program.model.scalar.Scalar;
import ghidra.program.model.address.*;
import ghidra.program.model.data.BooleanDataType;
import ghidra.program.model.data.ByteDataType;
import ghidra.program.model.data.CharDataType;
import ghidra.program.model.data.DataType;
import ghidra.program.model.data.FunctionDefinitionDataType;
import ghidra.program.model.data.ParameterDefinitionImpl;
import ghidra.program.model.data.PointerDataType;
import ghidra.program.model.data.UnsignedIntegerDataType;
import ghidra.program.model.data.WideCharDataType;
import ghidra.program.model.lang.Register;

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
	
	private void logMsg(String message, Object... args){
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
			Object EDX[] = insn.getOpObjects(0);
			Object IMM[] = insn.getOpObjects(1);
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
			Function StrCatN = functions.next();
			Reference refs[] = this.getReferencesTo(StrCatN.getEntryPoint());
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
		String[] lines;

		monitor.setMessage("loading symbols from IDC");

		try {
			idc = this.askFile("IDC File Path", "Load an IDC file");
		} catch (CancelledException e) {
			return false;
		}
		try {
			List<String> stringList = Files.readAllLines(idc.toPath(), Charset.defaultCharset());
			lines = stringList.toArray(new String[]{});
		} catch (IOException e) {
			this.logMsg("file not found: %s", idc.getAbsolutePath());
			return false;
		}

		Pattern pattern = Pattern.compile(
				"^\\s*MakeNameEx\\((?:0x)?([A-Fa-f0-9]+),\\s*\"([^\"]*)\",\\s*([xA-Fa-f0-9]+)\\);\\s*$");
		monitor.setMaximum(lines.length);
		for (int k=0; k < lines.length; k++) {
			monitor.setProgress(k);
			if (!lines[k].contains("MakeNameEx"))
				continue;
			Matcher match = pattern.matcher(lines[k]);
			if (!match.matches())
				continue;
			Integer offset = Integer.parseUnsignedInt(match.group(1), 16);
			Address entryPoint = this.toAddr(offset);
			String functionName = match.group(2);
			monitor.setMessage(functionName);
			if (functionName.strip().length() > 0) {
				try {
					this.renameSymbol(entryPoint, functionName);
				} catch (InvalidInputException e) {
					this.logMsg("renaming failed for: %s", functionName);
				}
			}
		}

		return true;
	}
	
	private void repairStringCompareFunctions() {
		try {
			monitor.setMessage("reparing known function signatures");

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
			String argNames[] = new String[] {"a", "b", "size"};

			for (Map.Entry<String, DataType[]> cmp : comparators.entrySet()) {	   
				Iterator<Function> functions = this.getGlobalFunctions(cmp.getKey()).iterator();
				while (functions.hasNext()) {
					Function function = functions.next();
					function.setCustomVariableStorage(true);
					function.setReturn(BOOL, zfReturn, DhrakeSource);
					DataType argTypes[] = cmp.getValue();
					List <ParameterImpl> args = new ArrayList<>();
					for (int k = 0; k < argTypes.length; k++)
						args.add(new ParameterImpl(argNames[k], argTypes[k], argLocations[k], currentProgram));
					ParameterImpl argumentArray[] = args.toArray(new ParameterImpl[args.size()]);
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
				Function function = functions.next();
				DataType argTypes[] = sig.getValue();
				List <ParameterImpl> args = new ArrayList<>();
				try {
					for (int k = 0; k < argTypes.length; k++)
						args.add(new ParameterImpl(String.format("a%d", k), argTypes[k], currentProgram));
					ParameterImpl argumentArray[] = args.toArray(new ParameterImpl[args.size()]);
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
