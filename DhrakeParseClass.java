//Creates structs based on Delphi type information.
//@category Delphi
//@author Jesko Huettenhain
//@keybinding F8

import ghidra.app.script.GhidraScript;
import ghidra.app.util.NamespaceUtils;
import ghidra.program.model.address.Address;
import ghidra.program.model.data.StructureDataType;
import ghidra.program.model.data.FunctionDefinitionDataType;
import ghidra.program.model.data.DataTypeConflictHandler;
import ghidra.program.model.data.DataType;
import ghidra.program.model.listing.Function;
import ghidra.program.model.listing.GhidraClass;
import ghidra.program.model.mem.MemoryAccessException;
import ghidra.program.model.symbol.SourceType;

public class DhrakeParseClass extends GhidraScript {

	protected DataType putType(DataType dt, DataTypeConflictHandler h) {
		return this.getCurrentProgram().getDataTypeManager().addDataType(dt, h);
	}

	protected DataType putType(DataType dt) {
		return this.putType(dt, DataTypeConflictHandler.REPLACE_HANDLER);
	}

	protected DataType addFnType(Function fn) {
		FunctionDefinitionDataType ft = new FunctionDefinitionDataType(fn, false);
		return this.putType(ft, DataTypeConflictHandler.KEEP_HANDLER);
	}
	
	protected void log(String message) {
		this.println(String.format("[Dhrake] %s", message));
	}

	@Override
	protected void run() throws Exception {
		String className = null;
		Address nameAddress = this.toAddr(this.getInt(currentAddress.add(32)));
		try {	
			className = new String(this.getBytes(nameAddress.add(1), this.getByte(nameAddress)));
		} catch (MemoryAccessException e) {
			this.popup(
				"Unfortunately, we got a memory access error trying to even read the class name. "	+
				"Either you executed this at the wrong address or the class metadata layout is "	+
				"unknown. If you can figure out how to identify this Delphi compiler and how it "	+
				"stores class metadata, that'd be Bill-Lumbergh-Level great."
			);
			return;
		}
		assert className.startsWith("T");
		this.log(className);
		this.log(String.format("creating class %s", className));
		GhidraClass classNamespace = NamespaceUtils.convertNamespaceToClass(
			currentProgram.getSymbolTable().createNameSpace(
				currentProgram.getGlobalNamespace(), className, SourceType.USER_DEFINED));
		StructureDataType base = new StructureDataType(className, 0);
		StructureDataType vtbl = new StructureDataType(className + "VT", 0);
		long vt = this.getInt(currentAddress);
		for (long tooDamnHigh = vt + 4 * 100; vt < tooDamnHigh; vt += 4) {
			try {
				long offset = this.getInt(this.toAddr(vt));
				String name = null;
				Address entryPoint = this.toAddr(offset);
				Function function = this.getFunctionAt(entryPoint);
				if (function == null) {
					name = this.getSymbolAt(entryPoint).toString();
					if (name == null) {
						name = String.format("FUN_%08X", offset);
					}
					this.log(String.format("defining function at 0x%08X, name %s", offset, name));
					function = this.createFunction(entryPoint, name);
				}
				if (function == null)
					break;
				function.setParentNamespace(classNamespace);
				name = function.getName();
				this.log(String.format("adding function %s::%s", className, name));
				vtbl.add(this.addFnType(function), 4, name, "");
			} catch (Exception e) {
				break;
			}
		}
		base.add(this.getCurrentProgram().getDataTypeManager().getPointer(this.putType(vtbl)),
			"vt", "Virtual Function Table");
		this.putType(base);

	}
}
