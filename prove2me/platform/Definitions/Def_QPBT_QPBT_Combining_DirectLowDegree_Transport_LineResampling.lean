-- Generated from QPBT/Combining/DirectLowDegree/Transport/LineResampling.lean by skeleton subtraction.
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
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Geometry
import Mathlib

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT

/-!
# Affine resampling of directly indexed lines

This module identifies the joint directly indexed line-point laws with the
equivalent sampling procedure that first draws their line marginal and then a
uniform affine parameter.  The argument retains zero diagonal directions: it
uses only translations of finite affine spaces and never cancels a direction.

## References

- `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:243-287`
- `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1020-1116`
-/

@[expose] public section

open scoped BigOperators

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT

noncomputable section

/-- Translate the point coordinate of a direct sample along a direction that
depends only on its stored index and direction coordinates. -/
 def directLdSpacePointTranslateEquiv (D : _root_.MIPStarRE.QPBT.DirectLdParams)
    (directionOf : Fin D.m → (Fin D.m → _root_.MIPStarRE.QPBT.DirectScalarQ D) →
      (Fin D.m → _root_.MIPStarRE.QPBT.DirectScalarQ D))
    (t : _root_.MIPStarRE.QPBT.DirectScalarQ D) : _root_.MIPStarRE.QPBT.DirectLdSpace D ≃ _root_.MIPStarRE.QPBT.DirectLdSpace D where
  toFun sample :=
    ⟨sample.point + t • directionOf sample.index sample.direction,
      sample.index, sample.direction⟩
  invFun sample :=
    ⟨sample.point + (-t) • directionOf sample.index sample.direction,
      sample.index, sample.direction⟩
  left_inv sample := by
    cases sample with
    | mk point index direction =>
        simp [add_assoc]
  right_inv sample := by
    cases sample with
    | mk point index direction =>
        simp [add_assoc]

@[simp]  theorem directLdSpacePointTranslateEquiv_apply
    (D : _root_.MIPStarRE.QPBT.DirectLdParams)
    (directionOf : Fin D.m → (Fin D.m → _root_.MIPStarRE.QPBT.DirectScalarQ D) →
      (Fin D.m → _root_.MIPStarRE.QPBT.DirectScalarQ D))
    (t : _root_.MIPStarRE.QPBT.DirectScalarQ D) (sample : _root_.MIPStarRE.QPBT.DirectLdSpace D) :
    directLdSpacePointTranslateEquiv D directionOf t sample =
      ⟨sample.point + t • directionOf sample.index sample.direction,
        sample.index, sample.direction⟩ := rfl

@[simp]  theorem directLdSpacePointTranslateEquiv_symm_apply
    (D : _root_.MIPStarRE.QPBT.DirectLdParams)
    (directionOf : Fin D.m → (Fin D.m → _root_.MIPStarRE.QPBT.DirectScalarQ D) →
      (Fin D.m → _root_.MIPStarRE.QPBT.DirectScalarQ D))
    (t : _root_.MIPStarRE.QPBT.DirectScalarQ D) (sample : _root_.MIPStarRE.QPBT.DirectLdSpace D) :
    (directLdSpacePointTranslateEquiv D directionOf t).symm sample =
      ⟨sample.point + (-t) • directionOf sample.index sample.direction,
        sample.index, sample.direction⟩ := rfl







end

end MIPStarRE.QPBT
