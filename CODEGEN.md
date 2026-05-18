# Codegen

This is a roadmap for generating executable assembly code from evm-asm.

## Requirements and Notes

- We can either test with an emulator from zisk or with [qemu](https://www.qemu.org).
    - Lean toward zisk, "ripping off the bandaid"
    - I believe the documentation for the emulator from zisk [can be found here](https://0xpolygonhermez.github.io/zisk/getting_started/quickstart.html)
- Ideally its an ELF, but its possible to do it in two steps (likely the easiest way to bootstrap):
    1. have evm-asm output raw assembly,
    1. then make a wrapper assembly file that just wraps the bytecode.

I think just having a .bin containing simple rv64 assembly and a .S file that wraps the emitted code like:
```
.section .text
.global _start

_start:
    .incbin "code.bin"
```

See for example:
- Here is an [ELF regression folder](https://github.com/0xPolygonHermez/zisk/tree/9537bcebe414f3a2a2cbf809b3d1cd09ac1e1b68/elf-regressions) in their repo, so that can also be used as a reference (with instructions)
- for example: https://github.com/0xPolygonHermez/zisk/blob/pre-develop-0.17.1/elf-regressions/simple_add/test.s
    - In the case above, the initial values of a0, a1, and a2 are constants — but zisk allows you to have an input file which is used to load in values from the prover/host


## Roadmap

TODO