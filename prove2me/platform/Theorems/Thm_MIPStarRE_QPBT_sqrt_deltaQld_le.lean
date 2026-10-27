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
import Definitions.Def_QPBT_QPBT_Test_PauliBasisTest
import Definitions.Def_QPBT_QPBT_Test_SoundnessDefs
import Mathlib

namespace MIPStarRE.QPBT
end MIPStarRE.QPBT

/-!
# Square roots of the Pauli soundness error

The state-extraction estimate bounds a squared norm. Taking its square root
preserves the Pauli soundness error family after halving the exponent.

## References

Blueprint `rem:pauli-robustness-form`; the source states the squared bound at
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1868-1876`,
whereas `thm:pauli` bounds the unsquared norm.
-/



open MIPStarRE.QPBT

theorem MIPStarRE.QPBT.sqrt_deltaQld_le {P : _root_.MIPStarRE.QPBT.AdmissibleParams} {a b epsilon : ℝ}
    (ha : 1 ≤ a) (hepsilon : 0 ≤ epsilon) :
    Real.sqrt (_root_.MIPStarRE.QPBT.deltaQld a b epsilon P.m P.d P.q) ≤
      _root_.MIPStarRE.QPBT.deltaQld a (b / 2) epsilon P.m P.d P.q := by sorry
