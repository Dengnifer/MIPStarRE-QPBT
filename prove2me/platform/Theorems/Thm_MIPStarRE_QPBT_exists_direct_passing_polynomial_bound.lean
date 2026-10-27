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
import Definitions.Def_QPBT_QPBT_Combining_PassingError
import Definitions.Def_QPBT_QPBT_Games_ErrorFunctions
import Mathlib
import Mathlib.Analysis.MeanInequalitiesPow

namespace MIPStarRE.QPBT
end MIPStarRE.QPBT

/-!
# Absorbing both errors of the directly indexed game

The conversion from combined measurements to a low-degree strategy has passing
error `3 * (sqrt (deltaQ + deltaL) + m * d / q)`. This module bounds its cap by
one while retaining the point error and the dimension factor in the line error.
It then absorbs low-degree soundness at that capped error into `deltaQld`.
These scalar estimates do not construct either measurement witness.

## References

* `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1279-1288,1402`
* Blueprint `lem:qld-4-7`
-/



open MIPStarRE.QPBT

theorem MIPStarRE.QPBT.exists_direct_passing_polynomial_bound (pointError : ℝ → ℝ)
    (hpoint : _root_.MIPStarRE.QPBT.IsPolyErr pointError) (lineError : ℝ → ℝ → ℝ)
    (hline : _root_.MIPStarRE.QPBT.IsPolyErr₂ lineError) (C : ℝ) (hC : 0 ≤ C) :
    ∃ passingError : ℝ → ℝ → ℝ, _root_.MIPStarRE.QPBT.IsPolyErr₂ passingError ∧
      ∀ error ratio dimension : ℝ, 0 ≤ error → 0 ≤ ratio → 1 ≤ dimension →
        min 1 (_root_.MIPStarRE.QPBT.directPassingErrorEnvelope
          (pointError error + C * dimension * lineError error ratio) ratio) ≤
            dimension * passingError error ratio := by sorry
