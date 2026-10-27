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
import Definitions.Def_QPBT_QPBT_Algebra_LowDegreeCode
import Mathlib

namespace MIPStarRE.QPBT
end MIPStarRE.QPBT
namespace MvPolynomial
end MvPolynomial

/-!
# The low-degree encoding

This module encodes the Boolean subcube by multilinear indicator polynomials
and packages the resulting low-degree code as honest polynomial representatives.

## References

The source-facing nodes are blueprint `def:polynomials-degree`,
`def:low-degree-encoding`, and `def:indicator-vector`; the paper origin is
`references/qpbt-paper/04_preliminaries.tex:832-897`.
The polynomial class `def:polyfunc` is reused from
`MIPStarRE.LDT.Preliminaries.polyFunc` (the LDT formalization).

Note: this module contributes declarations to the comparator statement closure
of the QPBT headline theorems, which must elaborate in the same environment as
the Mathlib-only `ChallengeQPBT.lean`.  Keep the full `import Mathlib`; do not
narrow it.  See `docs/comparator.md`, "Environment alignment".
-/



open scoped BigOperators
open MvPolynomial

open MIPStarRE.QPBT

/- The Boolean cube indexes the `2^m` qudits in the low-degree encoding. -/






/- Evaluation shorthand for the representative polynomial in
`def:low-degree-encoding`; it is Lean-only notation. -/

theorem MIPStarRE.QPBT.sum_indicatorVec_mul_indicatorVec {K : Type*} [CommRing K]
    [CharP K 2] {m : ℕ} (x z : Fin m → K) :
    ∑ y : _root_.MIPStarRE.QPBT.Cube m, _root_.MIPStarRE.QPBT.indicatorVec x y * _root_.MIPStarRE.QPBT.indicatorVec z y
      = ∏ i : Fin m, (1 + x i + z i) := by sorry
