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
import Definitions.Def_QPBT_QPBT_Algebra_FieldBasis
import Definitions.Def_QPBT_QPBT_Test_PauliBasisTest
import Definitions.Def_QPBT_QPBT_Test_SoundnessDefs
import Mathlib

namespace MIPStarRE.QPBT
end MIPStarRE.QPBT

/-!
# Scalar absorption of the Naimark transfer constants

Transferring the Pauli operator distances from a Naimark dilation back to the
original spaces produces bounds of the shape `3 * δ + 6 * δ ^ 2`, where `δ` is
the Pauli soundness error `deltaQld`. This module records the purely scalar
fact that such a combination is again a Pauli soundness error, after enlarging
the universal prefactor. No strategy, measurement, or state content enters
here; the module only depends on `MIPStarRE.QPBT.Test.SoundnessDefs`.

## References

Blueprint `lem:delta-qld-scalar-absorption-support`. The source performs the
same constant bookkeeping inline when it records the error form of
`thm:pauli` at
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1862-1876`.
The companion constant adjustments are `deltaQld_mono`
(`MIPStarRE/QPBT/Test/SoundnessDefs.lean`) and `sqrt_deltaQld_le`
(`MIPStarRE/QPBT/Combining/RootErrorBounds.lean`).
-/



open MIPStarRE.QPBT

theorem MIPStarRE.QPBT.three_add_six_sq_deltaQld_le {P : _root_.MIPStarRE.QPBT.AdmissibleParams} {a b epsilon : ℝ}
    (ha : 1 ≤ a) (hb : 0 < b) (hepsilon : 0 ≤ epsilon) (hepsilon1 : epsilon ≤ 1) :
    3 * _root_.MIPStarRE.QPBT.deltaQld a b epsilon P.m P.d P.q +
        6 * _root_.MIPStarRE.QPBT.deltaQld a b epsilon P.m P.d P.q ^ 2 ≤
      _root_.MIPStarRE.QPBT.deltaQld (21 * a ^ 2) b epsilon P.m P.d P.q := by sorry
