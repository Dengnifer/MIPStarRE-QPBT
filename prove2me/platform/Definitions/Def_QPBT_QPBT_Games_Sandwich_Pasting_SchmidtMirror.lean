-- Generated from QPBT/Games/Sandwich/Pasting/SchmidtMirror.lean by skeleton subtraction.
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
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_QXPLayerIdentities_PositiveGram_Completion
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_QXPLayerIdentities_PositiveGram_Rows
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Defs_Families
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Defs_Interpolation
import Definitions.Def_LIDT_MIPStarRE_LDT_Tactic_AvgCongr
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyCore
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Basic
import Definitions.Def_LIDT_MIPStarRE_Quantum_Measurement

namespace LIDT.MIPStarRE.LDT.MakingMeasurementsProjective
end LIDT.MIPStarRE.LDT.MakingMeasurementsProjective
namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT

/-! # State-dependent Schmidt mirrors

This module constructs the opposite-register mirror used in the one-sided
pasting argument. The auxiliary construction uses the spectral theorem and
orthonormal completion, including zero Schmidt coefficients.

## References

`references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:504-525`, `lem:pasting`;
`docs/paper-gaps/qpbt_pasting-product-error.tex`, issue Dengnifer/MIPStarRE-QPBT-bak#201. The
Schmidt-mirror
argument is a formalization auxiliary, not an additional paper hypothesis.
-/

@[expose] public section

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.Quantum
open LIDT.MIPStarRE.LDT.MakingMeasurementsProjective



/-- A square matrix admits Schmidt coordinates, including its zero singular
values. This specializes the existing positive-Gram orthonormal completion
to equal row and column index types; no invertibility is assumed. -/
theorem exists_schmidt_coordinates {ι : Type*} [Fintype ι] [DecidableEq ι]
    (coeff : _root_.LIDT.MIPStarRE.Quantum.Op ι) :
    ∃ (left right : Matrix.unitaryGroup ι ℂ) (values : ι → ℝ),
      (∀ index, 0 ≤ values index) ∧
      coeff = (left : _root_.LIDT.MIPStarRE.Quantum.Op ι) * Matrix.diagonal (fun index => (values index : ℂ)) *
        (right : _root_.LIDT.MIPStarRE.Quantum.Op ι)ᴴ := by
  classical
  let gram := coeffᴴ * coeff
  let hermitian := Matrix.isHermitian_conjTranspose_mul_self coeff
  obtain ⟨rows, hrows⟩ :=
    _root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.exists_unitaryGroup_with_positive_gram_spectrum_rows
      coeff gram hermitian rfl (Function.Embedding.subtype _)
  have htranspose : (rows : _root_.LIDT.MIPStarRE.Quantum.Op ι)ᵀ * ((rows : _root_.LIDT.MIPStarRE.Quantum.Op ι)ᵀ)ᴴ = 1 := by
    rw [show ((rows : _root_.LIDT.MIPStarRE.Quantum.Op ι)ᵀ)ᴴ = ((rows : _root_.LIDT.MIPStarRE.Quantum.Op ι)ᴴ)ᵀ from rfl,
      ← Matrix.transpose_mul,
      show (rows : _root_.LIDT.MIPStarRE.Quantum.Op ι)ᴴ * (rows : _root_.LIDT.MIPStarRE.Quantum.Op ι) = 1 from Unitary.coe_star_mul_self rows,
      Matrix.transpose_one]
  let left : Matrix.unitaryGroup ι ℂ :=
    ⟨(rows : _root_.LIDT.MIPStarRE.Quantum.Op ι)ᵀ, Matrix.mem_unitaryGroup_iff.mpr htranspose⟩
  let right := hermitian.eigenvectorUnitary
  let values := fun index => Real.sqrt (hermitian.eigenvalues index)
  have hcolumns : coeff * (right : _root_.LIDT.MIPStarRE.Quantum.Op ι) =
      (left : _root_.LIDT.MIPStarRE.Quantum.Op ι) * Matrix.diagonal (fun index => (values index : ℂ)) := by
    ext row col
    rw [Matrix.mul_diagonal]
    have himage : (coeff * (right : _root_.LIDT.MIPStarRE.Quantum.Op ι)) row col =
        (Matrix.toEuclideanLin coeff (hermitian.eigenvectorBasis col)) row := by
      simp [Matrix.mul_apply, right, Matrix.IsHermitian.eigenvectorUnitary_apply,
        Matrix.toEuclideanLin, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct]
    rw [himage]
    by_cases hpositive : 0 < hermitian.eigenvalues col
    · have hrow := hrows ⟨col, hpositive⟩ row
      have hvalue : (values col : ℂ) ≠ 0 := by
        exact_mod_cast (Real.sqrt_pos.mpr hpositive).ne'
      change (rows : _root_.LIDT.MIPStarRE.Quantum.Op ι) col row =
        ((1 / values col : ℝ) : ℂ) *
          (Matrix.toEuclideanLin coeff (hermitian.eigenvectorBasis col)) row at hrow
      change _ = (rows : _root_.LIDT.MIPStarRE.Quantum.Op ι) col row * (values col : ℂ)
      rw [hrow]
      push_cast
      field_simp
    · have hzero :=
        _root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.matrix_image_eq_zero_of_nonpositive_gram_eigenvalue
          coeff gram hermitian (Matrix.posSemidef_conjTranspose_mul_self coeff) rfl col hpositive
      have hvalue : values col = 0 := Real.sqrt_eq_zero_of_nonpos (le_of_not_gt hpositive)
      rw [hzero, hvalue]
      simp
  refine ⟨left, right, values, fun index => Real.sqrt_nonneg _, ?_⟩
  calc
    coeff = coeff * (right : _root_.LIDT.MIPStarRE.Quantum.Op ι) * (right : _root_.LIDT.MIPStarRE.Quantum.Op ι)ᴴ := by
      rw [Matrix.mul_assoc,
        show (right : _root_.LIDT.MIPStarRE.Quantum.Op ι) * (right : _root_.LIDT.MIPStarRE.Quantum.Op ι)ᴴ = 1 from Unitary.coe_mul_star_self right,
        Matrix.mul_one]
    _ = _ := by rw [hcolumns]







variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The coefficient matrix of a bipartite vector in the fixed computational
bases. This is a representation adapter, not a change of state. -/
def schmidtCoefficientMatrix (ψ : EuclideanSpace ℂ (ι × ι)) : _root_.LIDT.MIPStarRE.Quantum.Op ι :=
  Matrix.of fun row col => ψ (row, col)

/-- Schmidt coordinates chosen from the proved square-matrix decomposition.
The choice is made once for the state and is independent of all measurements. -/
noncomputable def schmidtCoordinates (ψ : EuclideanSpace ℂ (ι × ι)) :
    Matrix.unitaryGroup ι ℂ × Matrix.unitaryGroup ι ℂ × (ι → ℝ) :=
  let existence := _root_.MIPStarRE.QPBT.exists_schmidt_coordinates (_root_.MIPStarRE.QPBT.schmidtCoefficientMatrix ψ)
  ⟨Classical.choose existence, Classical.choose (Classical.choose_spec existence),
    Classical.choose (Classical.choose_spec (Classical.choose_spec existence))⟩



/-- The unitary identifying the transposed Bob coordinates with the Alice
Schmidt coordinates. Zero Schmidt directions use the orthonormal completion. -/
noncomputable def schmidtMirrorUnitary (ψ : EuclideanSpace ℂ (ι × ι)) :
    Matrix.unitaryGroup ι ℂ :=
  (_root_.MIPStarRE.QPBT.schmidtCoordinates ψ).1 * star (_root_.MIPStarRE.QPBT.schmidtCoordinates ψ).2.1

/-- The state-dependent opposite-register mirror, a linear map on Bob
operators. It reverses multiplication because it includes a transpose. -/
noncomputable def schmidtMirror (ψ : EuclideanSpace ℂ (ι × ι)) : _root_.LIDT.MIPStarRE.Quantum.Op ι →ₗ[ℂ] _root_.LIDT.MIPStarRE.Quantum.Op ι where
  toFun bob := (_root_.MIPStarRE.QPBT.schmidtMirrorUnitary ψ : _root_.LIDT.MIPStarRE.Quantum.Op ι) * bobᵀ * (_root_.MIPStarRE.QPBT.schmidtMirrorUnitary ψ : _root_.LIDT.MIPStarRE.Quantum.Op ι)ᴴ
  map_add' first second := by simp [Matrix.transpose_add, Matrix.mul_add, Matrix.add_mul]
  map_smul' scalar bob := by
    simp [Matrix.transpose_smul]



/-- Mirrors preserve the identity and therefore completeness of a measurement. -/
theorem schmidtMirror_one (ψ : EuclideanSpace ℂ (ι × ι)) :
    _root_.MIPStarRE.QPBT.schmidtMirror ψ 1 = 1 := by
  change (_root_.MIPStarRE.QPBT.schmidtMirrorUnitary ψ : _root_.LIDT.MIPStarRE.Quantum.Op ι) * (1 : _root_.LIDT.MIPStarRE.Quantum.Op ι)ᵀ *
    (_root_.MIPStarRE.QPBT.schmidtMirrorUnitary ψ : _root_.LIDT.MIPStarRE.Quantum.Op ι)ᴴ = 1
  rw [Matrix.transpose_one, Matrix.mul_one]
  exact Unitary.coe_mul_star_self _





/-- The transpose and unitary conjugation preserve positivity of effects. -/
theorem schmidtMirror_posSemidef (ψ : EuclideanSpace ℂ (ι × ι)) (bob : _root_.LIDT.MIPStarRE.Quantum.Op ι)
    (hbob : bob.PosSemidef) : (_root_.MIPStarRE.QPBT.schmidtMirror ψ bob).PosSemidef := by
  have hpositive := hbob.transpose.conjTranspose_mul_mul_same (_root_.MIPStarRE.QPBT.schmidtMirrorUnitary ψ : _root_.LIDT.MIPStarRE.Quantum.Op ι)ᴴ
  simpa only [_root_.MIPStarRE.QPBT.schmidtMirror, LinearMap.coe_mk, AddHom.coe_mk,
    Matrix.conjTranspose_conjTranspose] using hpositive



/-- Applying the fixed Schmidt mirror to every effect produces an actual
measurement; no normalization or completion of its effects is required. -/
noncomputable def schmidtMirrorMeasurement {α : Type*} [Fintype α]
    (ψ : EuclideanSpace ℂ (ι × ι)) (measurement : _root_.LIDT.MIPStarRE.Quantum.Measurement α ι) : _root_.LIDT.MIPStarRE.Quantum.Measurement α ι :=
  _root_.LIDT.MIPStarRE.Quantum.Measurement.ofSumEqOne (fun answer => _root_.MIPStarRE.QPBT.schmidtMirror ψ (measurement.effect answer))
    (fun answer => Matrix.nonneg_iff_posSemidef.mpr
      (_root_.MIPStarRE.QPBT.schmidtMirror_posSemidef ψ _ (Matrix.nonneg_iff_posSemidef.mp (measurement.pos answer))))
    (by rw [← map_sum, measurement.sum_eq_one, _root_.MIPStarRE.QPBT.schmidtMirror_one])





end MIPStarRE.QPBT
