/-
  EvmAsm.Codegen.Driver

  `IO` glue: write the emitted `.s` to disk and (optionally) shell out to
  `riscv64-unknown-elf-as` and `riscv64-unknown-elf-ld` to produce an ELF.

  Toolchain availability is gated by the `--asm-only` CLI flag — useful for
  CI hosts that don't have the cross binutils installed.
-/

namespace EvmAsm.Codegen.Driver

def asProgram : String := "riscv64-unknown-elf-as"
def ldProgram : String := "riscv64-unknown-elf-ld"

/-- Run a subprocess; throw an IO error containing stderr on non-zero exit. -/
def runOrFail (prog : String) (args : Array String) : IO Unit := do
  let res ← IO.Process.output { cmd := prog, args }
  if res.exitCode ≠ 0 then
    let argStr := " ".intercalate args.toList
    throw <| IO.userError
      s!"{prog} {argStr} failed (exit {res.exitCode}):\n{res.stderr}"

/-- Ensure the parent directory of `p` exists (no-op if it already does). -/
def ensureParentDir (p : System.FilePath) : IO Unit :=
  match p.parent with
  | some parent => IO.FS.createDirAll parent
  | none        => pure ()

/-- Write `text` to `asmPath`, creating parent directories as needed. -/
def writeAsmFile (asmPath : System.FilePath) (text : String) : IO Unit := do
  ensureParentDir asmPath
  IO.FS.writeFile asmPath text

/-- Assemble + link an emitted `.s` to a `.elf`, with `.o` as the intermediate.
    Returns the produced `(objPath, elfPath)`. Uses absolute `-Ttext=0x80000000`
    to match Zisk's default entry point. -/
def assembleAndLink (asmPath : System.FilePath) :
    IO (System.FilePath × System.FilePath) := do
  let objPath := asmPath.withExtension "o"
  let elfPath := asmPath.withExtension "elf"
  runOrFail asProgram
    #["-march=rv64imac", "-mno-relax", "-o", objPath.toString, asmPath.toString]
  runOrFail ldProgram
    #["-Ttext=0x80000000", "-nostdlib", "--no-relax",
      "-o", elfPath.toString, objPath.toString]
  return (objPath, elfPath)

end EvmAsm.Codegen.Driver
