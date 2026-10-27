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
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Basic
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_NormalizedTrace
import Definitions.Def_LIDT_MIPStarRE_Quantum_Measurement
import Definitions.Def_QPBT_QPBT_Games_Defs
import Definitions.Def_QPBT_QPBT_Games_DistanceTheorems_Support
import Definitions.Def_QPBT_QPBT_Test_MagicSquareTheorems_Rigidity_GroundSlice

namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT
namespace MIPStarRE.QPBT.DistanceCalculus
end MIPStarRE.QPBT.DistanceCalculus
namespace MIPStarRE.QPBT.MagicSquareRigidity
end MIPStarRE.QPBT.MagicSquareRigidity

/-!
# Range projections in Pauli soundness

Inserting an orthogonal projection into a measurement comparison costs at most
twice the squared distance to a vector fixed by that projection. Summing over
the measurement outcomes introduces no factor depending on their number.

## References

These are formalization-only auxiliary estimates for the final proof of
blueprint `thm:pauli`. The range projection is omitted at
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1864-1875`;
the corrected calculation is given in `docs/paper-gaps/qpbt_extraction-transfer.tex`.
They do not construct the extraction data or prove Pauli soundness.
-/



open scoped BigOperators Matrix MatrixOrder ComplexOrder

open MIPStarRE.QPBT

open LIDT.MIPStarRE.Quantum
open MIPStarRE.QPBT.DistanceCalculus MIPStarRE.QPBT.MagicSquareRigidity

theorem MIPStarRE.QPBT.sum_norm_mul_projection_sub_sq_le {α ι : Type*}
    [Fintype α] [Fintype ι] [DecidableEq ι]
    (N : _root_.LIDT.MIPStarRE.Quantum.Measurement α ι) (T : α → _root_.LIDT.MIPStarRE.Quantum.Op ι)
    (Q : _root_.LIDT.MIPStarRE.Quantum.Op ι) (hQ : _root_.LIDT.MIPStarRE.Quantum.IsProj Q) (theta delta : EuclideanSpace ℂ ι)
    (htheta : _root_.MIPStarRE.QPBT.applyOperatorToState Q theta = theta) :
    ∑ a : α, ‖_root_.MIPStarRE.QPBT.applyOperatorToState (N.effect a * Q - T a) delta‖ ^ 2 ≤
      2 * (∑ a : α, ‖_root_.MIPStarRE.QPBT.applyOperatorToState (N.effect a - T a) delta‖ ^ 2) +
        2 * ‖delta - theta‖ ^ 2 := by sorry
