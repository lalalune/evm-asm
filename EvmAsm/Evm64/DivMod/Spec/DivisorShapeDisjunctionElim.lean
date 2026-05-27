/-
  EvmAsm.Evm64.DivMod.Spec.DivisorShapeDisjunctionElim

  Eliminator over the five-way Or disjunction `divisor_full_domain_shape`
  (PR #6973), using the named `NkShapeIs` predicates and `bzero`. Lets
  callers apply per-case continuations to the flat disjunction in one
  step, without an `rcases ... with ⟨...⟩ | ⟨...⟩ | ...` chain.
-/

import EvmAsm.Evm64.DivMod.Spec.DivisorFullDomainShape
import EvmAsm.Evm64.DivMod.Spec.DivisorShapeNamed

namespace EvmAsm.Evm64

open EvmAsm.Rv64 EvmWord

/-- Apply per-case continuations to the flat divisor shape disjunction. -/
theorem divisor_full_domain_shape_elim
    {P : EvmWord → Prop}
    (b : EvmWord)
    (hbzero : b = 0 → P b)
    (hn1 : N1ShapeIs b → P b)
    (hn2 : N2ShapeIs b → P b)
    (hn3 : N3ShapeIs b → P b)
    (hn4 : N4ShapeIs b → P b) :
    P b := by
  rcases divisor_full_domain_shape b with
      hbz | ⟨hbnz, hb3z, hb2z, hb1z, hb0nz⟩
    | ⟨hbnz, hb3z, hb2z, hb1nz⟩
    | ⟨hbnz, hb3z, hb2nz⟩
    | ⟨hbnz, hb3nz⟩
  · exact hbzero hbz
  · exact hn1 ⟨hbnz, hb3z, hb2z, hb1z, hb0nz⟩
  · exact hn2 ⟨hbnz, hb3z, hb2z, hb1nz⟩
  · exact hn3 ⟨hbnz, hb3z, hb2nz⟩
  · exact hn4 ⟨hbnz, hb3nz⟩

end EvmAsm.Evm64
