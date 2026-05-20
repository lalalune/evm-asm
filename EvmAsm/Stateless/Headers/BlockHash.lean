/-
  EvmAsm.Stateless.Headers.BlockHash

  Compute the canonical block hash of an Ethereum block header:

      block_hash(header) = keccak256(rlp_encoded_header_bytes)

  ## Contract

  Calling convention -- same as `zkvm_keccak256` (the parameterised
  wrapper introduced in PR-K3):

      a0  : pointer to RLP-encoded header bytes
      a1  : length in bytes
      a2  : pointer to 32-byte output buffer (the block hash)
      ra  : return address
      returns a0 = 0  (ZKVM_EOK on success)

  The implementation is a one-liner that forwards to
  `zkvm_keccak256` -- it exists as a separate symbol for proof
  structure (the eventual CPS triple will say "block_hash of the
  bytes from `a0..a0+a1` is at `a2..a2+32`" without exposing the
  sponge internals).

  ## PR-K8 status

  Scaffold only. The eventual definition will be a `Program` (or
  raw asm wrapper) that emits:

      jal ra, zkvm_keccak256

  and inherits the contract above. PR-K9 (or whichever PR wires
  this in) provides the body.
-/

namespace EvmAsm.Stateless.Headers.BlockHash

-- TODO(stateless-headers): wrap `zkvm_keccak256` in a Lean Program
-- (or asm shim) named `block_hash`. Same calling convention; same
-- 32-byte output buffer; same intrinsic underneath.

end EvmAsm.Stateless.Headers.BlockHash
