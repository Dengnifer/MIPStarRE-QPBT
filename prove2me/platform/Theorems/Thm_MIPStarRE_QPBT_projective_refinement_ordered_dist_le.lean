import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_AxisParallelLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DiagonalLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_Distribution
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
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Basic
import Definitions.Def_LIDT_MIPStarRE_Quantum_Measurement
import Definitions.Def_QPBT_QPBT_Games_Consistency
import Definitions.Def_QPBT_QPBT_Games_Defs
import Definitions.Def_QPBT_QPBT_Games_Distance
import Definitions.Def_QPBT_QPBT_Games_DistanceTheorems_Support
import Mathlib
import Mathlib.Analysis.MeanInequalitiesPow

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT
namespace MIPStarRE.QPBT.CombinedPointsWitness
end MIPStarRE.QPBT.CombinedPointsWitness
namespace MIPStarRE.QPBT.DistanceCalculus
end MIPStarRE.QPBT.DistanceCalculus

/-!
# Ordered products selected by a global projective measurement

The point comparison of a projective measurement can be refined to its original
outcomes and composed with the two combined-point ordered-product estimates.
All bounds are on the actual expanded state and retain the complete outcome sum.

## References

`eq:qld-g-42` and `eq:qld-g-43`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1283-1300`.
These are auxiliary estimates for issue Dengnifer/MIPStarRE-QPBT-bak#513, not the global-pair
constructor.
-/



open scoped BigOperators Matrix MatrixOrder ComplexOrder

open MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum MIPStarRE.QPBT.DistanceCalculus

theorem MIPStarRE.QPBT.projective_refinement_ordered_dist_le {X Γ α ι : Type*}
    [Fintype X] [DecidableEq X] [Fintype Γ] [DecidableEq Γ]
    [Fintype α] [DecidableEq α] [Fintype ι] [DecidableEq ι]
    (μ : _root_.LIDT.MIPStarRE.LDT.Distribution X) (R : _root_.LIDT.MIPStarRE.Quantum.Measurement Γ ι) (hR : _root_.MIPStarRE.QPBT.Measurement.IsProjective R)
    (ev : X → Γ → α) (A B : X → _root_.LIDT.MIPStarRE.Quantum.Measurement α ι) (T : X → α → _root_.LIDT.MIPStarRE.Quantum.Op ι)
    (ψ : EuclideanSpace ℂ ι) (eta deltaSelf deltaOrder : ℝ)
    (hpoint : _root_.MIPStarRE.QPBT.consistencyDefect μ
      (fun x a => (R.postprocess (ev x)).effect a) (fun x a => (B x).effect a) ψ ≤ eta)
    (hself : _root_.MIPStarRE.QPBT.opFamilyDistSq μ (fun x a => (B x).effect a)
      (fun x a => (A x).effect a) ψ ≤ deltaSelf)
    (horder : _root_.MIPStarRE.QPBT.opFamilyDistSq μ (fun x a => (A x).effect a) T ψ ≤ deltaOrder) :
    _root_.MIPStarRE.QPBT.opFamilyDistSq μ (fun _ g => R.effect g)
      (fun x g => R.effect g * T x (ev x g)) ψ ≤
        4 * eta + 4 * deltaSelf + 4 * deltaOrder := by sorry
