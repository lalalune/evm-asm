/-
  EvmAsm.Evm64.DivMod.Spec.N1PointedEvidence

  Short alias `N1PointedEvidence` for the verbose
  `N1CallableSelectedIfBorrowWordEvidence`, mirroring the naming used by
  `N2CanonicalPointedEvidence` / `N3CanonicalPointedEvidence` so the top-level
  assembly can reference all three lanes uniformly.

  The N1 lane uses if-borrow branch/path/word evidence rather than the
  canonical-bltu pattern used by N2/N3, so the underlying definition is
  not symmetric — but a short alias makes downstream references consistent.
-/

import EvmAsm.Evm64.DivMod.Spec.N1CallableSelectedIfBorrowShapeEvidence

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- Alias for the N1 callable pointed evidence bundle. Matches the
    `N{2,3}CanonicalPointedEvidence` naming so the top-level assembly can
    reference all three lanes uniformly. -/
abbrev N1PointedEvidence (a b : EvmWord) : Prop :=
  N1CallableSelectedIfBorrowWordEvidence a b

/-- Constructor mirroring `N{2,3}CanonicalPointedEvidence.of_parts`. -/
theorem N1PointedEvidence.of_parts {a b : EvmWord}
    (hbranches : N1CallableSelectedIfBorrowBranchFacts a b)
    (hpath : N1SelectedIfBorrowPathEvidence a b)
    (hword : fullDivN1CallMaxmaxmaxQuotientWordV4
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) =
        EvmWord.div a b) :
    N1PointedEvidence a b :=
  N1CallableSelectedIfBorrowWordEvidence.of_parts hbranches hpath hword

theorem N1PointedEvidence.branchFacts {a b : EvmWord}
    (h : N1PointedEvidence a b) :
    N1CallableSelectedIfBorrowBranchFacts a b :=
  N1CallableSelectedIfBorrowWordEvidence.branchFacts h

theorem N1PointedEvidence.selectedPath {a b : EvmWord}
    (h : N1PointedEvidence a b) :
    N1SelectedIfBorrowPathEvidence a b :=
  N1CallableSelectedIfBorrowWordEvidence.selectedPath h

theorem N1PointedEvidence.wordEq {a b : EvmWord}
    (h : N1PointedEvidence a b) :
    fullDivN1CallMaxmaxmaxQuotientWordV4
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) =
        EvmWord.div a b :=
  N1CallableSelectedIfBorrowWordEvidence.wordEq h

theorem N1PointedEvidence.hdivs {a b : EvmWord}
    (h : N1PointedEvidence a b) :
    FullDivN1CallMaxmaxmaxHdivs a b
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) :=
  N1CallableSelectedIfBorrowWordEvidence.hdivs h

end EvmAsm.Evm64
