import EvmAsm.Codegen

def main (args : List String) : IO UInt32 :=
  EvmAsm.Codegen.Cli.main args
