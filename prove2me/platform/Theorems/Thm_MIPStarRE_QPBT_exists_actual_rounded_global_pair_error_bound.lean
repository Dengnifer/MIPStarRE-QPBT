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
import Definitions.Def_QPBT_QPBT_Test_LowDegreeGameMeasurements
import Definitions.Def_QPBT_QPBT_Test_PauliBasisTest
import Definitions.Def_QPBT_QPBT_Test_SoundnessDefs
import Mathlib
import Mathlib.Analysis.MeanInequalitiesPow

namespace MIPStarRE.QPBT
end MIPStarRE.QPBT

/-! # Absorption of the actual rounded polynomial-pair error

The point and line errors both enter low-degree soundness. The actual
projective rounding then incurs an eighth root. The unit cap is applied only
to the final consistency defect.

## References

Paper `lem:qld-4-7`,
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1267-1404`.
This module composes the direct passing estimate with square-root closure for
the global error function.
-/



open MIPStarRE.QPBT

theorem MIPStarRE.QPBT.exists_actual_rounded_global_pair_error_bound (pointError : ℝ → ℝ)
    (hpoint : _root_.MIPStarRE.QPBT.IsPolyErr pointError) (lineError : ℝ → ℝ → ℝ)
    (hline : _root_.MIPStarRE.QPBT.IsPolyErr₂ lineError) (C a b : ℝ) (hC : 0 ≤ C)
    (ha : 1 ≤ a) (hb : 0 < b) (hb1 : b ≤ 1) :
    ∃ A B : ℝ, 1 < A ∧ 0 < B ∧ B < 1 ∧
      ∀ (P : _root_.MIPStarRE.QPBT.AdmissibleParams) (epsilon : ℝ), 0 ≤ epsilon →
        let delta := _root_.MIPStarRE.QPBT.deltaLd a b
          (_root_.MIPStarRE.QPBT.directPassingErrorEnvelope
            (pointError epsilon + C * (P.m : ℝ) *
              lineError epsilon ((P.m * P.d : ℕ) / (P.q : ℝ)))
            ((P.m * P.d : ℕ) / (P.q : ℝ))) P.q (2 * P.m + 2) P.d 1
        let eta := delta + Real.sqrt (220 * delta ^ (1 / 4 : ℝ)) +
          2 * Real.sqrt (2 * delta)
        min 1 (8 * (4 * eta + 8 * pointError epsilon) +
          (((12 * P.m * P.d + 4 * P.d + 14 : ℕ) : ℝ) / P.q)) ≤
          _root_.MIPStarRE.QPBT.deltaQld A B epsilon P.m P.d P.q := by sorry
