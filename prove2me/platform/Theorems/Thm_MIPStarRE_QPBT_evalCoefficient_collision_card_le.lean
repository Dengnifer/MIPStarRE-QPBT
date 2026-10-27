import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_AxisParallelLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DiagonalLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_LinePolynomials
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_LowDegreePolynomial
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_OpFamily
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_ParametersBase
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_ParametersFiniteAnswers
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_QuantumState
import Definitions.Def_LIDT_MIPStarRE_LDT_CommutativityPoints_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_ExpansionHypercubeGraph_Defs_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_GlobalVariance_Defs_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Defs_Families
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Defs_Interpolation
import Definitions.Def_LIDT_MIPStarRE_LDT_Tactic_AvgCongr
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyCore
import Definitions.Def_QPBT_QPBT_Algebra_Coefficients
import Mathlib

namespace MIPStarRE.QPBT
end MIPStarRE.QPBT

/-!
# Coefficient polynomials and finite-field collision bounds

This module supplies the coefficient evaluation and polynomial representation
shared by the low-degree games and the combining argument. Distinct bounded
coefficient vectors agree at no more parameters than their degree bound.

## References

- Blueprint `def:ld-win-predicate` and `lem:coefficient-polynomial-agreement`.
- `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:331-344`.
- `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:950-955`.

Note: this module contributes declarations to the comparator statement closure
of the QPBT headline theorems, which must elaborate in the same environment as
the Mathlib-only `ChallengeQPBT.lean`.  Keep the full `import Mathlib`; do not
narrow it.  See `docs/comparator.md`, "Environment alignment".
-/



open scoped BigOperators

open MIPStarRE.QPBT

theorem MIPStarRE.QPBT.evalCoefficient_collision_card_le {K : Type*} [CommRing K] [IsDomain K]
    [Fintype K] [DecidableEq K] {bound : ℕ}
    (first second : Fin (bound + 1) → K) (hne : first ≠ second) :
    (Finset.univ.filter fun param => _root_.MIPStarRE.QPBT.evalCoefficient first param =
      _root_.MIPStarRE.QPBT.evalCoefficient second param).card ≤ bound := by sorry
