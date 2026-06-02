# EEST Precompile Frontier

The stateless guest has reusable accelerator payload and ECALL bridge surfaces
for the cryptographic precompiles, but `EvmAsm/Stateless/VM/Precompiles.lean`
still routes EVM precompile dispatch to the unimplemented frontier. The matrix
below keeps the EEST fixture classes explicit so precompile tests are not
silently postponed as new generated fixtures appear.

Generate the current matrix with:

```bash
scripts/eest-precompile-frontier-report.py --markdown
```

After a stateless harness run, the report also consumes the latest
`gen-out/eest-run/manifest.tsv` or `gen-out/eest-run/run-*/manifest.tsv` and
matching `*.result.tsv` files, then adds selected-case guest outcomes by family.
`fixture files` counts cached generated JSON files; `selected` and the match
columns describe only the latest harness selection.

| Family | Address | Backend / missing piece | Bead |
|--------|---------|-------------------------|------|
| Precompile account warming / absence | `0x01..0x14`, `0x100` | VM call gas/account-access path before dispatch | `evm-asm-fhsxz.2.4.2.62.1` |
| ECRECOVER | `0x01` | `zkvm_secp256k1_ecrecover` bridge exists; stateless dispatch missing | `evm-asm-fhsxz.2.4.2.62.2` |
| SHA256 | `0x02` | `zkvm_sha256` bridge exists; stateless dispatch missing | `evm-asm-fhsxz.2.4.2.62.2` |
| RIPEMD160 | `0x03` | `zkvm_ripemd160` bridge exists at the desired ABI level, but the local ziskemu installation has no named RIPEMD160 backend; backend/probe required before dispatch | `evm-asm-fhsxz.2.4.2.62.2` |
| IDENTITY | `0x04` | in-guest memory copy; no accelerator | `evm-asm-fhsxz.2.4.2.62.2` |
| MODEXP | `0x05` | `zkvm_modexp` bridge exists; gas/return-data framing missing | `evm-asm-fhsxz.2.4.2.62.3` |
| BN254 add/mul/pairing | `0x06..0x08` | `zkvm_bn254_*` bridges exist; call framing missing | `evm-asm-fhsxz.2.4.2.62.3` |
| BLAKE2F | `0x09` | `zkvm_blake2f` bridge exists; call framing missing | `evm-asm-fhsxz.2.4.2.62.3` |
| KZG point evaluation | `0x0a` | `zkvm_kzg_point_eval` bridge exists; call framing missing | `evm-asm-fhsxz.2.4.2.62.3` |
| BLS12-381 | `0x0b..0x11` | `zkvm_bls12_*` bridges exist; call framing missing | `evm-asm-fhsxz.2.4.2.62.3` |
| P256VERIFY | `0x100` | `zkvm_secp256r1_verify` bridge exists; call framing missing | `evm-asm-fhsxz.2.4.2.62.3` |
| CALL/STATICCALL/revert/create interactions with precompiles | mixed | VM call/create/revert semantics plus dispatch | `evm-asm-fhsxz.2.4.2.62.1` |

The accelerator bridge source of truth is
[`docs/zkvm-accelerators-interface.md`](zkvm-accelerators-interface.md). The
report's path filters intentionally cover benchmark, fork-specific, and ported
static EEST fixture trees so the matrix stays complete when future fixtures are
added under the existing precompile test naming conventions.
