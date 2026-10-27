-- Generated from QPBT/Combining/DirectLowDegree/Transport/Combining/Coefficients.lean by skeleton subtraction.
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
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Transport_Combining_Polynomial
import Mathlib

namespace LIDT.MIPStarRE.LDT.Preliminaries
end LIDT.MIPStarRE.LDT.Preliminaries
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT

/-!
# The coefficients of a polynomial in the combining variables

The recovery step of the combining reduction reads a polynomial `p` in the
`m + k` combined variables as a polynomial in the `k` combining variables whose
coefficients `c_μ` are polynomials in the `m` point variables, and characterises
the two properties it needs in terms of those coefficients: `p` is the combined
polynomial of a tuple exactly when `c_μ` vanishes for every exponent vector `μ`
outside the `k` standard basis vectors, and the restriction `p(u, ·)` is a
linear form exactly when `c_μ(u)` vanishes for every such `μ`.  The
individual degrees of the coefficients are bounded by those of `p`, so each
`c_μ` has total degree at most `m d` and the Schwartz--Zippel lemma applies to
it.

The rereading is the algebra homomorphism sending the point variables to
constants and keeping the combining variables; it is injective, its left
inverse being the substitution which renames the point variables back and sends
the combining variables to the combining coordinates.

## Main definitions

* `combinedPointExp`, `combinedCoefExp` — the two blocks of an exponent vector
  of the combined dimension.
* `combinedCoefAlgHom` — the rereading of a polynomial in the combined
  variables as a polynomial in the combining variables with polynomial
  coefficients.
* `combinedCoef` — the coefficient of the combining monomial `μ`.

## Main statements

* `combinedCoefAlgHom_monomial` — the rereading of a monomial.
* `combinedCoefAlgHom_injective` — the rereading is injective.
* `eval_combinedCoef` — the value at `u` of `c_μ` is the coefficient of `μ` in
  the restriction `p(u, ·)`.
* `combinePolyTuple_combinedCoef_iff` — `p` is combined exactly when `c_μ`
  vanishes off the standard basis vectors.
* `degreeOf_combinedCoef_le`, `totalDegree_combinedCoef_le` — the degree bounds.

## References

* `references/neexp-paper/05_quantum_preliminaries.tex:1440-1470`
* `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:413-458`
* `blueprint/src/chapter/ch13_qpbt_test.tex:575-600`
-/

@[expose] public section

open scoped BigOperators

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT.Preliminaries

noncomputable section

/-! ## The two blocks of an exponent vector -/

/-- The point block of an exponent vector of the combined dimension. -/
def combinedPointExp {m k : ℕ} (s : Fin (m + k) →₀ ℕ) : Fin m →₀ ℕ :=
  Finsupp.comapDomain (_root_.MIPStarRE.QPBT.combinedPointVar m k) s (_root_.MIPStarRE.QPBT.combinedPointVar_injective m k).injOn

/-- The combining block of an exponent vector of the combined dimension. -/
def combinedCoefExp {m k : ℕ} (s : Fin (m + k) →₀ ℕ) : Fin k →₀ ℕ :=
  Finsupp.comapDomain (_root_.MIPStarRE.QPBT.combinedCoefficientVar m k) s
    (_root_.MIPStarRE.QPBT.combinedCoefficientVar_injective m k).injOn

@[simp] theorem combinedPointExp_apply {m k : ℕ} (s : Fin (m + k) →₀ ℕ) (j : Fin m) :
    _root_.MIPStarRE.QPBT.combinedPointExp s j = s (_root_.MIPStarRE.QPBT.combinedPointVar m k j) := rfl

@[simp] theorem combinedCoefExp_apply {m k : ℕ} (s : Fin (m + k) →₀ ℕ) (r : Fin k) :
    _root_.MIPStarRE.QPBT.combinedCoefExp s r = s (_root_.MIPStarRE.QPBT.combinedCoefficientVar m k r) := rfl



/-! ## Rereading a polynomial in the combining variables -/

/-- The substitution reading the point variables as constants of the polynomial
ring in the point variables and keeping the combining variables. -/
def combinedCoefSubstitution (K : Type*) [CommSemiring K] (m k : ℕ) :
    Fin (m + k) → MvPolynomial (Fin k) (MvPolynomial (Fin m) K) :=
  fun i => Sum.elim
    (fun j : Fin m => MvPolynomial.C (MvPolynomial.X j))
    (fun r : Fin k => MvPolynomial.X r) (finSumFinEquiv.symm i)

@[simp] theorem combinedCoefSubstitution_point (K : Type*) [CommSemiring K] (m k : ℕ)
    (j : Fin m) :
    _root_.MIPStarRE.QPBT.combinedCoefSubstitution K m k (_root_.MIPStarRE.QPBT.combinedPointVar m k j) =
      MvPolynomial.C (MvPolynomial.X j) := by
  simp [_root_.MIPStarRE.QPBT.combinedCoefSubstitution, _root_.MIPStarRE.QPBT.combinedPointVar]

@[simp] theorem combinedCoefSubstitution_coefficient (K : Type*) [CommSemiring K] (m k : ℕ)
    (r : Fin k) :
    _root_.MIPStarRE.QPBT.combinedCoefSubstitution K m k (_root_.MIPStarRE.QPBT.combinedCoefficientVar m k r) =
      (MvPolynomial.X r : MvPolynomial (Fin k) (MvPolynomial (Fin m) K)) := by
  simp [_root_.MIPStarRE.QPBT.combinedCoefSubstitution, _root_.MIPStarRE.QPBT.combinedCoefficientVar]

/-- The rereading of a polynomial in the `m + k` combined variables as a
polynomial in the `k` combining variables with coefficients in the polynomial
ring in the `m` point variables. -/
def combinedCoefAlgHom (K : Type*) [CommSemiring K] (m k : ℕ) :
    MvPolynomial (Fin (m + k)) K →ₐ[K]
      MvPolynomial (Fin k) (MvPolynomial (Fin m) K) :=
  MvPolynomial.aeval (_root_.MIPStarRE.QPBT.combinedCoefSubstitution K m k)

@[simp] theorem combinedCoefAlgHom_X (K : Type*) [CommSemiring K] (m k : ℕ)
    (i : Fin (m + k)) :
    _root_.MIPStarRE.QPBT.combinedCoefAlgHom K m k (MvPolynomial.X i) = _root_.MIPStarRE.QPBT.combinedCoefSubstitution K m k i :=
  MvPolynomial.aeval_X _ _





/-! ## Injectivity of the rereading -/

/-- The substitution inverting the rereading: rename the point variables back to
the point coordinates and send the combining variables to the combining
coordinates. -/
def combinedCoefInv (K : Type*) [CommSemiring K] (m k : ℕ) :
    MvPolynomial (Fin k) (MvPolynomial (Fin m) K) →+* MvPolynomial (Fin (m + k)) K :=
  MvPolynomial.eval₂Hom ((MvPolynomial.rename (_root_.MIPStarRE.QPBT.combinedPointVar m k)).toRingHom)
    (fun r : Fin k => MvPolynomial.X (_root_.MIPStarRE.QPBT.combinedCoefficientVar m k r))





/-! ## The coefficients -/

/-- The coefficient of the combining monomial `μ` in `p`: a polynomial in the
point variables. -/
def combinedCoef {K : Type*} [CommSemiring K] {m k : ℕ}
    (p : MvPolynomial (Fin (m + k)) K) (μ : Fin k →₀ ℕ) : MvPolynomial (Fin m) K :=
  (_root_.MIPStarRE.QPBT.combinedCoefAlgHom K m k p).coeff μ



/-! ## Combined polynomials in terms of the coefficients -/











/-! ## The degree bound on the coefficients -/











end

end MIPStarRE.QPBT
