module

public import MIPStarRE.Quantum.Measurement
public import MIPStarRE.Quantum.FiniteMatrix.BlockDiagonal
public import MIPStarRE.LDT.Basic.DistributionAvg
public import MIPStarRE.LDT.Basic.TensorPlacement
public import MIPStarRE.LDT.Preliminaries.FiniteFields

/-!
# Public helpers for the upstream LIDT interface

These finite-sum and measurement lemmas support the QPBT without modifying its LIDT dependency.
The marginal-state construction and rank-zero argument adapt the private proofs in
`LionSR/MIPStarRE`, commit `5fc363bc8b77b1a6bbdaaeea634f1b0f3ff0ad79`, module
`MIPStarRE.LDT.MakingMeasurementsProjective.LocalityPreservingRepair`.
The remaining lemmas are QPBT extensions of the upstream measurement and distribution APIs.
Their proofs use the public definitions and Mathlib finite-dimensional linear algebra.
-/

@[expose] public section

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.Quantum.Measurement
variable {d : Type*} [Fintype d] [DecidableEq d]
variable {α β : Type*} [Fintype α] [Fintype β]

/-- A complete measurement is determined by its effects. -/
theorem ext {M N : Measurement α d} (h : ∀ a, M.effect a = N.effect a) :
    M = N := by
  cases M with
  | mk M hM =>
      cases N with
      | mk N hN =>
          cases M with
          | mk effectM posM leM =>
              cases N with
              | mk effectN posN leN =>
                  simp only at h
                  have heffect : effectM = effectN := funext h
                  subst effectN
                  rfl

/-- Relabeling along `f` and then along `g` is relabeling along `g ∘ f`: the
fiber of `g ∘ f` over `c` is the disjoint union of the fibers of `f` over the
fiber of `g` over `c`, and regrouping a finite sum of effects along it does not
change the sum. -/
theorem postprocess_comp {γ : Type*} [Fintype γ]
    [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    (M : Measurement α d) (f : α → β) (g : β → γ) :
    (M.postprocess f).postprocess g = M.postprocess (fun a => g (f a)) := by
  classical
  apply ext
  intro c
  calc
    ((M.postprocess f).postprocess g).effect c =
        ∑ b : β, if g b = c then
          ∑ a : α, if f a = b then M.effect a else 0
        else 0 := by
          change (∑ b ∈ Finset.univ.filter (fun b : β => g b = c),
            ∑ a ∈ Finset.univ.filter (fun a : α => f a = b), M.effect a) = _
          rw [Finset.sum_filter]
          apply Finset.sum_congr rfl
          intro b _
          by_cases hgb : g b = c
          · simp only [hgb, ite_true]
            rw [Finset.sum_filter]
          · simp [hgb]
    _ = ∑ b : β, ∑ a : α,
        if g b = c ∧ f a = b then M.effect a else 0 := by
          apply Finset.sum_congr rfl
          intro b _
          by_cases hgc : g b = c <;> simp [hgc]
    _ = ∑ a : α, ∑ b : β,
        if g b = c ∧ f a = b then M.effect a else 0 := by
          rw [Finset.sum_comm]
    _ = ∑ a : α,
        if g (f a) = c then M.effect a else 0 := by
          apply Finset.sum_congr rfl
          intro a _
          by_cases hgc : g (f a) = c
          · rw [Finset.sum_eq_single (f a)]
            · simp [hgc]
            · intro b _ hba
              by_cases hfa : f a = b
              · exact (hba hfa.symm).elim
              · simp [hfa]
            · simp
          · have hzero :
                (∑ b : β,
                  if g b = c ∧ f a = b then M.effect a else 0) = 0 := by
              apply Finset.sum_eq_zero
              intro b _
              by_cases hfa : f a = b
              · subst b
                simp [hgc]
              · simp [hfa]
            simp [hgc, hzero]
    _ = (M.postprocess (fun a => g (f a))).effect c := by
          change _ = ∑ a ∈ Finset.univ.filter
            (fun a : α => g (f a) = c), M.effect a
          rw [Finset.sum_filter]

end MIPStarRE.Quantum.Measurement

namespace MIPStarRE.LDT

/-- Averaging scalar multiples of a fixed operator averages their coefficients
over the distribution's support. -/
theorem averageOperatorOverDistribution_smul_const {α ι : Type*}
    [Fintype ι] [DecidableEq ι] (𝒟 : Distribution α) (c : α → ℂ)
    (A : MIPStarRE.Quantum.Op ι) :
    averageOperatorOverDistribution 𝒟 (fun a => c a • A) =
      (∑ a ∈ 𝒟.support, (𝒟.weight a : ℂ) * c a) • A := by
  simp only [averageOperatorOverDistribution, Finset.sum_smul]
  apply Finset.sum_congr rfl
  intro a ha
  rw [← Complex.real_smul, smul_assoc]

/-- A uniform average over a finite type is its normalized finite sum. -/
theorem avgOver_uniform_eq_inv_card_mul_sum {α : Type*}
    [Fintype α] [DecidableEq α] [Nonempty α] (f : α → ℝ) :
    avgOver (uniformDistribution α) f = (Fintype.card α : ℝ)⁻¹ * ∑ a, f a := by
  unfold avgOver uniformDistribution Distribution.uniformOnFinset
  simp only [Finset.mem_univ, ite_true, Finset.card_univ, one_div, Finset.mul_sum]

namespace Distribution.IsProbability

/-- A probability distribution has total weight one over any finite superset
of its explicit support. -/
theorem weight_sum_eq_one_of_subset {α : Type*}
    {𝒟 : Distribution α} (h𝒟 : 𝒟.IsProbability) {s : Finset α}
    (hsubset : 𝒟.support ⊆ s) :
    ∑ a ∈ s, 𝒟.weight a = 1 := by
  have hsum :
      ∑ a ∈ 𝒟.support, 𝒟.weight a = ∑ a ∈ s, 𝒟.weight a :=
    Finset.sum_subset hsubset (fun a _ ha => 𝒟.outsideSupport a ha)
  exact hsum ▸ h𝒟.weight_sum_eq_one

end Distribution.IsProbability
end MIPStarRE.LDT

namespace MIPStarRE.LDT.Preliminaries

variable {p : ℕ} [Fact p.Prime]
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod p) F]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Fourier orthogonality for the canonical character over an arbitrary finite
coordinate type. This is the finite-index reindexing of
`prop:fourier-fact-vector`. -/
theorem expect_ffChar_sum_mul (v : ι → F) :
    𝔼 u : (ι → F), ffChar (p := p) (F := F) (∑ i, u i * v i) =
      if v = 0 then (1 : ℂ) else 0 := by
  let eι : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  let reindex : (ι → F) ≃ (Fin (Fintype.card ι) → F) :=
    { toFun := fun u j => u (eι.symm j)
      invFun := fun u i => u (eι i)
      left_inv := fun u => by
        funext i
        simp
      right_inv := fun u => by
        funext j
        simp }
  let v' : Fin (Fintype.card ι) → F := reindex v
  calc
    𝔼 u : (ι → F), ffChar (p := p) (F := F) (∑ i, u i * v i) =
        𝔼 u : (Fin (Fintype.card ι) → F),
          ffVecChar (p := p) (F := F) v' u := by
      refine Finset.expect_equiv reindex (by simp) ?_
      intro u _
      rw [ffVecChar_apply]
      congr 2
      exact Fintype.sum_equiv eι
        (fun i => u i * v i)
        (fun j => reindex u j * v' j)
        (fun i => by simp [reindex, v'])
    _ = if v' = 0 then (1 : ℂ) else 0 := fourier_fact_vector v'
    _ = if v = 0 then (1 : ℂ) else 0 := by
      have reindex_zero : reindex (0 : ι → F) = 0 := by
        ext j
        rfl
      by_cases hv : v = 0
      · subst v
        rw [show v' = 0 by exact reindex_zero]
        simp
      · have hv' : v' ≠ 0 := by
          intro hv'
          apply hv
          apply reindex.injective
          rw [reindex_zero]
          exact hv'
        simp [hv, hv']

/-- Sum form of canonical-character orthogonality over an arbitrary finite
coordinate type. -/
theorem sum_ffChar_sum_mul (v : ι → F) :
    ∑ u : ι → F, ffChar (p := p) (F := F) (∑ i, u i * v i) =
      if v = 0 then (Fintype.card (ι → F) : ℂ) else 0 := by
  rw [← Fintype.card_smul_expect, expect_ffChar_sum_mul]
  by_cases hv : v = 0 <;> simp [hv]

end MIPStarRE.LDT.Preliminaries

namespace MIPStarRE.LDT.MakingMeasurementsProjective
open MIPStarRE.LDT
noncomputable section

/-- The diagonal block of a bipartite operator at a fixed right index. -/
def diagBlock {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (M : MIPStarRE.Quantum.Op (ιA × ιB)) (b : ιB) :
    MIPStarRE.Quantum.Op ιA :=
  M.submatrix (fun i => (i, b)) (fun j => (j, b))

/-- The normalized left marginal of a bipartite density, obtained by
averaging its diagonal right blocks. -/
def leftMarginalDensity {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB] [Nonempty ιB]
    (ρ : MIPStarRE.Quantum.Op (ιA × ιB)) : MIPStarRE.Quantum.Op ιA :=
  ((((Fintype.card ιB : Error) : Error)⁻¹ : Error) : ℂ) •
    ∑ b : ιB, diagBlock ρ b

/-- Positivity passes from a bipartite density to its left marginal. -/
private lemma leftMarginalDensity_nonneg {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB] [Nonempty ιB]
    {ρ : MIPStarRE.Quantum.Op (ιA × ιB)} (hρ : 0 ≤ ρ) :
    0 ≤ leftMarginalDensity ρ := by
  have hρpsd : ρ.PosSemidef := Matrix.nonneg_iff_posSemidef.mp hρ
  have hsum : 0 ≤ ∑ b : ιB, diagBlock ρ b := by
    refine Finset.sum_nonneg fun b _ => ?_
    refine Matrix.nonneg_iff_posSemidef.mpr ?_
    simpa [diagBlock] using hρpsd.submatrix (fun i => (i, b))
  have hcoeff : 0 ≤ ((((Fintype.card ιB : Error) : Error)⁻¹ : Error) : ℂ) := by
    positivity
  simpa [leftMarginalDensity] using smul_nonneg hcoeff hsum

/-- The local state on the left factor defined by the left marginal density
of a bipartite state. This formalization-only definition supports the
locality-preserving projectivization lemma and the explicit-constant form of
the orthonormalization lemma. -/
def leftMarginalState {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB] [Nonempty ιB]
    (ψ : QuantumState (ιA × ιB)) : QuantumState ιA where
  density := leftMarginalDensity ψ.density
  density_psd := by
    exact leftMarginalDensity_nonneg ψ.density_psd

/-- Left tensor placement is block diagonal with the same block at every
right index. -/
private lemma leftTensor_eq_blockDiagonal_const {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (X : MIPStarRE.Quantum.Op ιA) :
    leftTensor (ι₂ := ιB) X = Matrix.blockDiagonal (fun _ : ιB => X) := by
  ext x y
  rcases x with ⟨i, b⟩
  rcases y with ⟨j, c⟩
  by_cases h : b = c
  · subst c
    simp [leftTensor, Matrix.blockDiagonal_apply]
  · simp [leftTensor, Matrix.blockDiagonal_apply, h]

/-- The trace against a constant block-diagonal operator is the sum of the
traces of the diagonal blocks. -/
private lemma trace_blockDiagonal_const_mul_eq_sum_trace_diagBlock
    {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (X : MIPStarRE.Quantum.Op ιA)
    (M : MIPStarRE.Quantum.Op (ιA × ιB)) :
    Matrix.trace (Matrix.blockDiagonal (fun _ : ιB => X) * M) =
      ∑ b : ιB, Matrix.trace (X * diagBlock M b) := by
  classical
  let e : ((ιA × ιB) × ιA) ≃ (ιB × (ιA × ιA)) :=
    { toFun := fun x => (x.1.2, (x.1.1, x.2))
      invFun := fun x => ((x.2.1, x.1), x.2.2)
      left_inv := fun ⟨⟨_, _⟩, _⟩ => rfl
      right_inv := fun ⟨_, ⟨_, _⟩⟩ => rfl }
  simpa [diagBlock, Matrix.trace, Matrix.mul_apply, Matrix.blockDiagonal_apply,
    Fintype.sum_prod_type, Finset.sum_sigma', e] using
    (e.sum_comp (fun y : ιB × (ιA × ιA) =>
      X y.2.1 y.2.2 * M (y.2.2, y.1) (y.2.1, y.1)))

/-- Evaluating a local operator against the left marginal agrees with
evaluating its left tensor placement against the bipartite density. -/
private lemma normalizedTrace_leftMarginalDensity_mul_eq
    {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB] [Nonempty ιB]
    (ρ : MIPStarRE.Quantum.Op (ιA × ιB)) (X : MIPStarRE.Quantum.Op ιA) :
    MIPStarRE.Quantum.normalizedTrace (leftMarginalDensity ρ * X) =
      MIPStarRE.Quantum.normalizedTrace (ρ * leftTensor (ι₂ := ιB) X) := by
  have hcard : ((Fintype.card ιB : Error) : ℂ) ≠ 0 := by
    exact_mod_cast Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  unfold MIPStarRE.Quantum.normalizedTrace leftMarginalDensity
  rw [smul_mul_assoc, Matrix.trace_smul, Matrix.sum_mul, Matrix.trace_sum]
  have hswap :
      ∑ b : ιB, Matrix.trace (diagBlock ρ b * X) =
        ∑ b : ιB, Matrix.trace (X * diagBlock ρ b) := by
    refine Finset.sum_congr rfl ?_
    intro b _
    exact Matrix.trace_mul_comm _ _
  rw [hswap]
  rw [Matrix.trace_mul_comm]
  rw [leftTensor_eq_blockDiagonal_const]
  rw [trace_blockDiagonal_const_mul_eq_sum_trace_diagBlock]
  simp [Fintype.card_prod]
  ring

/-- The complex normalized trace of a local operator is preserved by passage to
the left marginal. This formalization-only identity supports the marginal
reduction in the locality-preserving projectivization lemma and the
explicit-constant form of the orthonormalization lemma. -/
lemma normalizedTrace_leftMarginalState_density_mul_eq
    {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB] [Nonempty ιB]
    (ψ : QuantumState (ιA × ιB)) (X : MIPStarRE.Quantum.Op ιA) :
    MIPStarRE.Quantum.normalizedTrace ((leftMarginalState ψ).density * X) =
      MIPStarRE.Quantum.normalizedTrace (ψ.density * leftTensor (ι₂ := ιB) X) := by
  simpa [leftMarginalState] using
    normalizedTrace_leftMarginalDensity_mul_eq (ρ := ψ.density) (X := X)

/-- The left marginal of a normalized bipartite state is normalized. This
formalization-only lemma supports the marginal reduction in the
locality-preserving projectivization lemma and the explicit-constant form of
the orthonormalization lemma. -/
lemma leftMarginalState_isNormalized {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB] [Nonempty ιB]
    {ψ : QuantumState (ιA × ιB)} (hψ : ψ.IsNormalized) :
    (leftMarginalState ψ).IsNormalized := by
  unfold QuantumState.IsNormalized
  have hnorm :
      MIPStarRE.Quantum.normalizedTrace (leftMarginalState ψ).density =
        MIPStarRE.Quantum.normalizedTrace ψ.density := by
    simpa [leftTensor_one] using
      normalizedTrace_leftMarginalState_density_mul_eq (ψ := ψ)
        (X := (1 : MIPStarRE.Quantum.Op ιA))
  exact hnorm.trans hψ

/-- Local evaluation in the left marginal equals bipartite evaluation of the
left tensor placement. This formalization-only identity supports the marginal
reduction in the locality-preserving projectivization lemma and the
explicit-constant form of the orthonormalization lemma. -/
lemma leftMarginal_ev_eq {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB] [Nonempty ιB]
    (ψ : QuantumState (ιA × ιB)) (X : MIPStarRE.Quantum.Op ιA) :
    ev ψ (leftTensor (ι₂ := ιB) X) = ev (leftMarginalState ψ) X := by
  simpa [ev] using congrArg Complex.re
    (normalizedTrace_leftMarginalState_density_mul_eq (ψ := ψ) (X := X)).symm

/-- A finite complex matrix of rank zero is the zero matrix. This
formalization-only linear-algebra lemma handles the zero-rank alternatives in
the locality-preserving projectivization lemma and the explicit-constant form
of the orthonormalization lemma. -/
lemma matrix_eq_zero_of_rank_eq_zero {m n : Type*}
    [Finite m] [Fintype n] (A : Matrix m n ℂ) (hA : A.rank = 0) :
    A = 0 := by
  let _ : Fintype m := Fintype.ofFinite m
  classical
  have hrange : A.mulVecLin.range = ⊥ := by
    rw [Matrix.rank] at hA
    exact Submodule.finrank_eq_zero.mp hA
  ext i j
  have hv : A.mulVecLin (Pi.single j 1) ∈ A.mulVecLin.range := ⟨Pi.single j 1, rfl⟩
  have hv0 : A.mulVecLin (Pi.single j 1) = 0 := by
    simpa [hrange] using hv
  have hentry := congrArg (fun w => w i) hv0
  simpa [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, Finset.sum_ite_eq,
    Pi.single_apply] using hentry

end
end MIPStarRE.LDT.MakingMeasurementsProjective
