-- Generated from QPBT/Quantum/ControlledUnitary.lean by skeleton subtraction.
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
import Definitions.Def_QPBT_QPBT_Games_Defs
import Definitions.Def_QPBT_QPBT_Games_DistanceTheorems_Support

namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT

/-!
# Finite controlled unitaries

A complete projective measurement controls a family of operators on a second
finite-dimensional space. Orthogonality of the measurement effects makes
multiplication of the resulting operator sums componentwise. In particular,
unitary components give a unitary controlled operator.

These are formalization-only algebraic lemmas, not the extraction theorem:
they do not construct the global measurement or establish the Pauli relations.

## References

- `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1687-1700`,
  the unitarity calculation in the proof of `lem:qld-unitary`.
- Blueprint `def:v-swap-unitary` and `lem:v-swap-conjugation`.
-/

@[expose] public section

open scoped BigOperators Matrix

namespace LIDT
namespace MIPStarRE.Quantum

open MIPStarRE.QPBT

variable {Outcome Control Target : Type*}
variable [Fintype Outcome] [Fintype Control] [DecidableEq Control]
variable [Fintype Target]

/-- Multiplication of operator sums controlled by the same projective measurement
is componentwise. This isolates the orthogonality calculation in the proof of
`lem:qld-unitary`, before any unitarity of the controlled components is used. -/
theorem sum_heteroKron_mul_sum_heteroKron
    (measurement : _root_.LIDT.MIPStarRE.Quantum.Measurement Outcome Control)
    (hprojective : _root_.MIPStarRE.QPBT.Measurement.IsProjective measurement)
    (leftOperators rightOperators : Outcome → _root_.LIDT.MIPStarRE.Quantum.Op Target) :
    (∑ outcome, _root_.MIPStarRE.QPBT.heteroKron (measurement.effect outcome) (leftOperators outcome)) *
        (∑ outcome, _root_.MIPStarRE.QPBT.heteroKron (measurement.effect outcome) (rightOperators outcome)) =
      ∑ outcome, _root_.MIPStarRE.QPBT.heteroKron (measurement.effect outcome)
        (leftOperators outcome * rightOperators outcome) := by
  classical
  rw [Finset.sum_mul]
  simp_rw [Finset.mul_sum, _root_.MIPStarRE.QPBT.heteroKron_mul]
  apply Finset.sum_congr rfl
  intro outcome _
  rw [Finset.sum_eq_single outcome]
  · rw [(hprojective outcome).isIdempotentElem.eq]
  · intro other _ hother
    rw [_root_.MIPStarRE.QPBT.DistanceCalculus.projective_effect_mul_effect_eq_zero
      measurement hprojective hother.symm]
    exact Matrix.zero_kronecker _
  · simp

variable [DecidableEq Target]

/-- A controlled operator times its adjoint is the identity when each component
times its adjoint is the identity. This is the finite controlled-unitary
calculation at paper `14_analysis_of_the_pauli_basis_test.tex:1687-1700`,
with arbitrary unitary components in place of the products of Pauli observables. -/
theorem sum_heteroKron_mul_conjTranspose
    (measurement : _root_.LIDT.MIPStarRE.Quantum.Measurement Outcome Control)
    (hprojective : _root_.MIPStarRE.QPBT.Measurement.IsProjective measurement)
    (operators : Outcome → _root_.LIDT.MIPStarRE.Quantum.Op Target)
    (hunitary : ∀ outcome, operators outcome * (operators outcome)ᴴ = 1) :
    (∑ outcome, _root_.MIPStarRE.QPBT.heteroKron (measurement.effect outcome) (operators outcome)) *
        (∑ outcome, _root_.MIPStarRE.QPBT.heteroKron (measurement.effect outcome) (operators outcome))ᴴ = 1 := by
  have hself (outcome : Outcome) :
      (measurement.effect outcome)ᴴ = measurement.effect outcome :=
    (hprojective outcome).isSelfAdjoint.star_eq
  calc
    _ = (∑ outcome, _root_.MIPStarRE.QPBT.heteroKron (measurement.effect outcome) (operators outcome)) *
        (∑ outcome, _root_.MIPStarRE.QPBT.heteroKron (measurement.effect outcome) ((operators outcome)ᴴ)) := by
      simp only [Matrix.conjTranspose_sum, _root_.MIPStarRE.QPBT.heteroKron, Matrix.kronecker,
        Matrix.conjTranspose_kronecker, hself]
    _ = ∑ outcome, _root_.MIPStarRE.QPBT.heteroKron (measurement.effect outcome)
        (operators outcome * (operators outcome)ᴴ) :=
      _root_.LIDT.MIPStarRE.Quantum.sum_heteroKron_mul_sum_heteroKron measurement hprojective _ _
    _ = ∑ outcome, _root_.MIPStarRE.QPBT.heteroKron (measurement.effect outcome) (1 : _root_.LIDT.MIPStarRE.Quantum.Op Target) := by
      simp_rw [hunitary]
    _ = 1 := by
      rw [← _root_.MIPStarRE.QPBT.DistanceCalculus.heteroKron_finset_sum_left, measurement.sum_eq_one,
        _root_.MIPStarRE.QPBT.heteroKron_one_one]





end MIPStarRE.Quantum
end LIDT
