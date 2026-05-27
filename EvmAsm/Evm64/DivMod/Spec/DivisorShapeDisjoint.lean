/-
  EvmAsm.Evm64.DivMod.Spec.DivisorShapeDisjoint

  Pairwise disjointness lemmas for the four `NkShapeIs` predicates. Any two
  distinct shape predicates are mutually exclusive: the per-limb facts each
  carries contradict the others.
-/

import EvmAsm.Evm64.DivMod.Spec.DivisorShapeNamed

namespace EvmAsm.Evm64

open EvmAsm.Rv64

theorem N1ShapeIs.not_N2ShapeIs {b : EvmWord} (h1 : N1ShapeIs b) :
    ¬ N2ShapeIs b := by
  intro h2
  exact absurd h1.2.2.2.1 h2.2.2.2

theorem N1ShapeIs.not_N3ShapeIs {b : EvmWord} (h1 : N1ShapeIs b) :
    ¬ N3ShapeIs b := by
  intro h3
  exact absurd h1.2.2.1 h3.2.2

theorem N1ShapeIs.not_N4ShapeIs {b : EvmWord} (h1 : N1ShapeIs b) :
    ¬ N4ShapeIs b := by
  intro h4
  exact absurd h1.2.1 h4.2

theorem N2ShapeIs.not_N3ShapeIs {b : EvmWord} (h2 : N2ShapeIs b) :
    ¬ N3ShapeIs b := by
  intro h3
  exact absurd h2.2.2.1 h3.2.2

theorem N2ShapeIs.not_N4ShapeIs {b : EvmWord} (h2 : N2ShapeIs b) :
    ¬ N4ShapeIs b := by
  intro h4
  exact absurd h2.2.1 h4.2

theorem N3ShapeIs.not_N4ShapeIs {b : EvmWord} (h3 : N3ShapeIs b) :
    ¬ N4ShapeIs b := by
  intro h4
  exact absurd h3.2.1 h4.2

end EvmAsm.Evm64
