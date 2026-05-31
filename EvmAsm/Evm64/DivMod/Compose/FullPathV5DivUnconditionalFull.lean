/-
  EvmAsm.Evm64.DivMod.Compose.FullPathV5DivUnconditionalFull

  The capstone: the fully unconditional EVM-stack-level DIV spec, over the
  production v5 code surface `divCode_v5` (the bug-free `divK_div128_v5`
  implementation, WITH the entry-nop block).

  `evm_div_stack_spec_unconditional_v5_div` (#7669) proved the unconditional DIV
  dispatch triple over the no-NOP v5 surface `divCode_noNop_v5`.  Lifting it to
  the full v5 bundle `divCode_v5` (which only adds the entry-nop block) via the
  ready code-monotonicity bridge `cpsTripleWithin_divCode_noNop_v5_to_divCode_v5`
  yields `evm_div_stack_spec_unconditional`: the DIV dispatch triple holds for
  EVERY 256-bit divisor — no `b ≠ 0` runtime gate, no shape premise, no `hq_over`
  premise, no per-lane certificate.

  Surface note: the unconditional spec is provable ONLY at the v5 surface.  The
  legacy v4 surface (`divCode`, `divK_div128_v4`) has the two buggy ULTs that
  motivated the v5 migration in the first place, so it is *not* correct over the
  full 4-limb domain — which is precisely why the capstone targets `divCode_v5`.

  Bead `evm-asm-wbc4i.10.2` (the DIV goal of `evm-asm-wbc4i.10` / gh-61).
-/

import EvmAsm.Evm64.DivMod.Compose.FullPathV5DivUnconditional
import EvmAsm.Evm64.DivMod.Compose.V5Code2

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- **The unconditional EVM-stack-level DIV spec.**  Over the production v5 code
    surface `divCode_v5`, with the uniform dispatch shift `divDispatchShiftX2 b`
    in `x2`, the full DIV dispatch triple holds for every 256-bit divisor `b` —
    with no premise about `b` whatsoever (the `b = 0`, n=1, n=2, n=3 and n=4
    divisor shapes are all discharged internally). -/
theorem evm_div_stack_spec_unconditional
    (sp base : Word) (a b : EvmWord)
    (raVal v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratch_un0 scratchMem : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff) :
    cpsTripleWithin unifiedDivBound base (base + nopOff) (divCode_v5 base)
      (divModStackDispatchPreNoX1 sp a b
        (signExtend12 (4 : BitVec 12) - (4 : Word)) raVal
        (divDispatchShiftX2 b) v5 v6 v7 v10 v11
        q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratch_un0 **
       ((sp + signExtend12 3936) ↦ₘ scratchMem))
      (divStackDispatchPostV5 sp a b) :=
  cpsTripleWithin_divCode_noNop_v5_to_divCode_v5
    (evm_div_stack_spec_unconditional_v5_div sp base a b
      raVal v5 v6 v7 v10 v11
      q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
      nMem shiftMem jMem retMem dMem dloMem scratch_un0 scratchMem halign)

end EvmAsm.Evm64
