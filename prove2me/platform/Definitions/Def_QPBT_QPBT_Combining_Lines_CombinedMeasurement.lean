-- Generated from QPBT/Combining/Lines/CombinedMeasurement.lean by skeleton subtraction.
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
import Definitions.Def_LIDT_MIPStarRE_Quantum_Measurement
import Definitions.Def_QPBT_QPBT_Algebra_FieldBasis
import Definitions.Def_QPBT_QPBT_Algebra_LowDegreeCode
import Definitions.Def_QPBT_QPBT_Algebra_Pauli
import Definitions.Def_QPBT_QPBT_Games_Sandwich_Defs
import Definitions.Def_QPBT_QPBT_Games_Sandwich_Pasting_Heterogeneous
import Definitions.Def_QPBT_QPBT_Observables_Defs
import Definitions.Def_QPBT_QPBT_Observables_ExpandedDefs
import Definitions.Def_QPBT_QPBT_Observables_LineDefs
import Definitions.Def_QPBT_QPBT_Observables_LineMeasurement_Expanded
import Definitions.Def_QPBT_QPBT_Test_LowDegreeGame
import Definitions.Def_QPBT_QPBT_Test_PauliBasisTest
import Mathlib
import Mathlib.Analysis.MeanInequalitiesPow

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT

/-!
# Combined X/Z line measurement

This module constructs the X-Z-X sandwich POVM used to combine one X-line
measurement with one Z-line measurement.  It also records the orientation of
the sandwich as a one-sided pasted measurement and the two axis-degree support
properties.

## References

The construction is the paired-line measurement in `lem:qld-xz-lines`, with
source `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:942-949`.
Its separate blueprint entries are `def:concrete-paired-line-measurement` and
`lem:concrete-paired-line-degree-support`; consistency remains the distinct
obligation `lem:combined-line-measurement-consistency`.
-/

@[expose] public section

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT LIDT.MIPStarRE.Quantum

noncomputable section

/-- The paired-line POVM in the proof of `lem:qld-xz-lines`, paper
`14_analysis_of_the_pauli_basis_test.tex:942-949`. The X effect is the outer
projector. This construction does not assert consistency with a point witness. -/
def ProjectiveSetting.combinedLineMeasurement {P : _root_.MIPStarRE.QPBT.AdmissibleParams} {ε : ℝ}
    (S : _root_.MIPStarRE.QPBT.ProjectiveSetting P ε) (side : _root_.MIPStarRE.QPBT.PlayerSide)
    (lineX lineZ : _root_.MIPStarRE.QPBT.LineDesc P.toLdParams) :
    _root_.LIDT.MIPStarRE.Quantum.Measurement (_root_.MIPStarRE.QPBT.DegPoly P.toLdParams (P.m * P.d) ×
      _root_.MIPStarRE.QPBT.DegPoly P.toLdParams (P.m * P.d)) (S.ExpandedLocalSpace side) :=
  _root_.LIDT.MIPStarRE.Quantum.Measurement.ofSumEqOne
    (fun fs => (S.lineMeasExp side .X lineX).effect fs.1 *
      (S.lineMeasExp side .Z lineZ).effect fs.2 *
      (S.lineMeasExp side .X lineX).effect fs.1)
    (fun fs => (_root_.MIPStarRE.QPBT.pastedMeasurement_isMeasurement
      (S.lineMeasExp side .Z lineZ) (S.lineMeasExp side .X lineX)
      (S.lineMeasExp_isProjective side .X lineX)).1 (fs.2, fs.1))
    (by
      classical
      have hsum := (_root_.MIPStarRE.QPBT.pastedMeasurement_isMeasurement
        (S.lineMeasExp side .Z lineZ) (S.lineMeasExp side .X lineX)
        (S.lineMeasExp_isProjective side .X lineX)).2
      simp only [_root_.MIPStarRE.QPBT.pastedMeasurement, Fintype.sum_prod_type] at hsum ⊢
      rw [Finset.sum_comm]
      exact hsum)

/-- The effects of the paired-line POVM are the source's X-Z-X sandwiches. -/
@[simp] theorem ProjectiveSetting.combinedLineMeasurement_effect
    {P : _root_.MIPStarRE.QPBT.AdmissibleParams} {ε : ℝ} (S : _root_.MIPStarRE.QPBT.ProjectiveSetting P ε) (side : _root_.MIPStarRE.QPBT.PlayerSide)
    (lineX lineZ : _root_.MIPStarRE.QPBT.LineDesc P.toLdParams)
    (fX fZ : _root_.MIPStarRE.QPBT.DegPoly P.toLdParams (P.m * P.d)) :
    (S.combinedLineMeasurement side lineX lineZ).effect (fX, fZ) =
      (S.lineMeasExp side .X lineX).effect fX *
        (S.lineMeasExp side .Z lineZ).effect fZ *
        (S.lineMeasExp side .X lineX).effect fX := rfl







end

end MIPStarRE.QPBT
