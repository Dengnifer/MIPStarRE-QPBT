-- Generated from QPBT/Combining/DirectLowDegree/Transport/Combining/Answers.lean by skeleton subtraction.
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
import Definitions.Def_QPBT_QPBT_Algebra_Coefficients
import Mathlib

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.LDT.Preliminaries
end LIDT.MIPStarRE.LDT.Preliminaries
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT

/-!
# Answer polynomials of the combined strategy

The combined strategy of `def:ld-combined-strategy` answers every question of
the directly indexed low-degree game at the combined parameters by measuring a
single question of the original game and relabelling its outcome.  Four of its
five cases produce a line answer, that is a bounded coefficient vector, from a
line answer or from a point answer of the original game.  This module collects
the univariate polynomials underlying those relabellings, with their degree
bounds and their evaluation identities.

Line answers of both games are bounded coefficient vectors evaluated by
`evalCoefficient`.  The polynomials below are therefore built from
`linePolynomialOfCoefficients` and converted back to coefficient vectors by
`coefficientsOfPolynomial`; the degree bounds are what makes that round trip
faithful.

The parameter `s` in the two line cases is the affine shift relating the two
canonical parametrizations of the line.

## Main definitions

* `coefficientsOfPolynomial` — the bounded coefficient vector of a polynomial.
* `shiftedLinePolynomial` — the affine reparametrization of a line answer.
* `combinedAxisPolynomial` — case 2 of `def:ld-combined-strategy`.
* `combinedDiagonalPolynomial` — case 4 of `def:ld-combined-strategy`.
* `fiberLinePolynomial` — cases 3 and 5 of `def:ld-combined-strategy`, the two
  cases whose line lies in a fiber of the projection to the point coordinates.

## References

* `references/neexp-paper/05_quantum_preliminaries.tex:1409-1503`
* `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:413-458`
* `blueprint/src/chapter/ch13_qpbt_test.tex:420-472`
-/

@[expose] public section

open scoped BigOperators

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT
open LIDT.MIPStarRE.LDT.Preliminaries

noncomputable section

/-! ## Coefficient vectors and univariate polynomials -/

/-- The bounded coefficient vector of a univariate polynomial.  It is a left
inverse of `linePolynomialOfCoefficients` on polynomials of degree at most
`n`, which is the content of `evalCoefficient_coefficientsOfPolynomial`. -/
def coefficientsOfPolynomial {K : Type*} [Semiring K] (n : ℕ)
    (p : Polynomial K) : Fin (n + 1) → K :=
  fun i => p.coeff i.val



/-- The affine reparametrization `t ↦ evalCoefficient f (t + s)` of a bounded
coefficient vector, as a univariate polynomial. -/
def shiftedLinePolynomial {K : Type*} [CommSemiring K] {n : ℕ}
    (f : Fin (n + 1) → K) (s : K) : Polynomial K :=
  (_root_.MIPStarRE.QPBT.linePolynomialOfCoefficients f).comp (Polynomial.X + Polynomial.C s)





/-! ## The answer polynomials of the combined strategy -/

/-- The combined answer on an axis-parallel line of the combined space whose
stored index is a point coordinate: the combining part `α` of the canonical
base is constant along such a line, so the answer is the fixed combination
`∑ r, α r * f r` of the measured line answers, reparametrized by `s`.  This is
case 2 of `def:ld-combined-strategy`. -/
def combinedAxisPolynomial {K : Type*} [CommSemiring K] {k n : ℕ}
    (α : Fin k → K) (s : K) (f : Fin k → Fin (n + 1) → K) : Polynomial K :=
  ∑ r : Fin k, Polynomial.C (α r) * _root_.MIPStarRE.QPBT.shiftedLinePolynomial (f r) s





/-- The combined answer on a diagonal line of the combined space whose stored
index is a point coordinate: the combining part of the point at parameter `t`
is `α + t • w`, so the answer is `∑ r, (α r + t * w r) * f r (t + s)`.  This is
case 4 of `def:ld-combined-strategy`. -/
def combinedDiagonalPolynomial {K : Type*} [CommSemiring K] {k n : ℕ}
    (α w : Fin k → K) (s : K) (f : Fin k → Fin (n + 1) → K) : Polynomial K :=
  ∑ r : Fin k, (Polynomial.C (α r) + Polynomial.C (w r) * Polynomial.X) *
    _root_.MIPStarRE.QPBT.shiftedLinePolynomial (f r) s





/-- The combined answer on a line of the combined space contained in a fiber of
the projection to the point coordinates: the point part is constant along the
line, the combined value at parameter `t` is `∑ r, (α r + t * w r) * b r`, and
the measured outcome is the point answer `b`.  This is cases 3 and 5 of
`def:ld-combined-strategy`; case 3 is the axis-parallel case, where `w` is the
standard basis vector of the varying combining coordinate. -/
def fiberLinePolynomial {K : Type*} [CommSemiring K] {k : ℕ}
    (α w b : Fin k → K) : Polynomial K :=
  Polynomial.C (∑ r : Fin k, α r * b r) +
    Polynomial.C (∑ r : Fin k, w r * b r) * Polynomial.X





end

end MIPStarRE.QPBT
