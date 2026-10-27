-- Generated from QPBT/Games/DistanceTheorems/TensorSupport.lean by skeleton subtraction.
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_AxisParallelLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DiagonalLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_LinePolynomials
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_LowDegreePolynomial
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_OpFamily
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_ParametersBase
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_ParametersFiniteAnswers
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_QuantumState
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_TensorPlacement
import Definitions.Def_LIDT_MIPStarRE_LDT_CommutativityPoints_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_ExpansionHypercubeGraph_Defs_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_GlobalVariance_Defs_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Defs_Families
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Defs_Interpolation
import Definitions.Def_LIDT_MIPStarRE_LDT_Tactic_AvgCongr
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyCore
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Basic
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Order
import Definitions.Def_LIDT_MIPStarRE_Quantum_Measurement
import Definitions.Def_QPBT_QPBT_Games_Defs

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.LDT.MakingMeasurementsProjective
end LIDT.MIPStarRE.LDT.MakingMeasurementsProjective
namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
namespace MIPStarRE.QPBT.DistanceCalculus
end MIPStarRE.QPBT.DistanceCalculus

/-!
# Tensor-placement and marginal identities

This module collects tensor-placement, marginal, and finite-fiber identities
used in data processing and the commutator estimate.

## References

- `references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:397-461`
- Blueprint `fact:triangle-for-simeq`, `fact:data-processing`, and
  `lem:commutation-analysis`
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT.DistanceCalculus

open LIDT.MIPStarRE.LDT LIDT.MIPStarRE.Quantum
open LIDT.MIPStarRE.LDT.MakingMeasurementsProjective

/-- Formalization-only definition used in the proof of Fact 4.26: place a
complete measurement on the left tensor factor. -/
noncomputable def leftPlacedMeasurement {α ιA ιB : Type*}
    [Fintype α] [Fintype ιA] [DecidableEq ιA]
    [Fintype ιB] [DecidableEq ιB]
    (M : _root_.LIDT.MIPStarRE.Quantum.Measurement α ιA) :
    _root_.LIDT.MIPStarRE.Quantum.Measurement α (ιA × ιB) :=
  _root_.LIDT.MIPStarRE.Quantum.Measurement.ofSumEqOne
    (fun a => _root_.MIPStarRE.QPBT.heteroKron (M.effect a) 1)
    (fun a => _root_.LIDT.MIPStarRE.Quantum.kronecker_nonneg (M.pos a)
      (Matrix.PosSemidef.one.nonneg : 0 ≤ (1 : _root_.LIDT.MIPStarRE.Quantum.Op ιB)))
    (by
      change ∑ a : α, _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ιB) (M.effect a) = 1
      rw [_root_.LIDT.MIPStarRE.LDT.leftTensor_finset_sum, M.sum_eq_one, _root_.LIDT.MIPStarRE.LDT.leftTensor_one])

/-- Formalization-only definition used in the proof of Fact 4.26: place a
complete measurement on the right tensor factor. -/
noncomputable def rightPlacedMeasurement {α ιA ιB : Type*}
    [Fintype α] [Fintype ιA] [DecidableEq ιA]
    [Fintype ιB] [DecidableEq ιB]
    (M : _root_.LIDT.MIPStarRE.Quantum.Measurement α ιB) :
    _root_.LIDT.MIPStarRE.Quantum.Measurement α (ιA × ιB) :=
  _root_.LIDT.MIPStarRE.Quantum.Measurement.ofSumEqOne
    (fun a => _root_.MIPStarRE.QPBT.heteroKron 1 (M.effect a))
    (fun a => _root_.LIDT.MIPStarRE.Quantum.kronecker_nonneg
      (Matrix.PosSemidef.one.nonneg : 0 ≤ (1 : _root_.LIDT.MIPStarRE.Quantum.Op ιA)) (M.pos a))
    (by
      change ∑ a : α, _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ιA) (M.effect a) = 1
      rw [_root_.LIDT.MIPStarRE.LDT.rightTensor_finset_sum, M.sum_eq_one, _root_.LIDT.MIPStarRE.LDT.rightTensor_one])



/-- The (possibly unnormalized) rank-one state associated to a Euclidean vector. -/
 noncomputable def vectorQuantumState {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (ψ : EuclideanSpace ℂ ι) : _root_.LIDT.MIPStarRE.LDT.QuantumState ι where
  density := _root_.LIDT.MIPStarRE.LDT.pureDensity ψ.ofLp
  density_psd := by
    refine Matrix.nonneg_iff_posSemidef.mpr ?_
    exact (Matrix.posSemidef_vecMulVec_self_star ψ.ofLp).smul
      (by positivity : 0 ≤ (Fintype.card ι : ℂ))

























/-- Formalization-only definition used in approximate commutation at paper
lines 410--461: exchange the final two coordinates of a nested product. -/
def swapLast (α β γ : Type*) : ((α × γ) × β) ≃ ((α × β) × γ) where
  toFun p := ((p.1.1, p.2), p.1.2)
  invFun p := ((p.1.1, p.2), p.1.2)
  left_inv := by rintro ⟨⟨a, c⟩, b⟩; rfl
  right_inv := by rintro ⟨⟨a, b⟩, c⟩; rfl

/-- Formalization-only auxiliary lemma for approximate commutation at paper
lines 410--461: the inverse of `swapLast` has the same coordinate formula. -/
@[simp] theorem swapLast_symm_apply {α β γ : Type*}
    (p : (α × β) × γ) :
    (_root_.MIPStarRE.QPBT.DistanceCalculus.swapLast α β γ).symm p = ((p.1.1, p.2), p.1.2) :=
  rfl

end MIPStarRE.QPBT.DistanceCalculus
