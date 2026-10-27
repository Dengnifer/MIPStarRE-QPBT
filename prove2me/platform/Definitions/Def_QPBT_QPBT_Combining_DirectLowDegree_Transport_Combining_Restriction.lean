-- Generated from QPBT/Combining/DirectLowDegree/Transport/Combining/Restriction.lean by skeleton subtraction.
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
# Restricting a polynomial in the combined variables to a point

The recovery step of the combining reduction reads a polynomial `p` in the
`m + k` combined variables as a polynomial in the `k` combining variables whose
coefficients are polynomials in the `m` point variables, and asks whether the
restriction `p(u, ·)` obtained by substituting a point `u` for the point
variables is a linear form in the combining variables.  This module introduces
that restriction and records its elementary properties: it computes the
combined polynomial of a tuple to the linear form of the tuple of values of the
tuple at the point, and, when it is a linear form, its coefficients are forced
to be the values at the point of the components recovered by the substitution
of `lem:ld-combining-split`.  Consequently a restriction which is a linear form
agrees with the restriction of the combined polynomial of those components,
which is the first half of `lem:ld-combining-exact-linearity`.

## Main statements

* `eval_combinedRestrict` — evaluating `p(u, ·)` at `α` evaluates `p` at the
  combined point with parts `u` and `α`.
* `combinedRestrict_combinePolyTuple` — the restriction of a combined
  polynomial is the linear form of the tuple of values of its components.
* `combinedRestrict_eq_of_eq_combiningLinearForm` — a restriction which is a
  linear form agrees with the restriction of the combined polynomial of the
  components of `p`.

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

/-! ## The two coordinate blocks -/



@[simp] theorem combinedPoint_combinedPointVar {K : Type*} {m k : ℕ}
    (u : Fin m → K) (α : Fin k → K) (j : Fin m) :
    _root_.MIPStarRE.QPBT.combinedPoint u α (_root_.MIPStarRE.QPBT.combinedPointVar m k j) = u j := by
  simp [_root_.MIPStarRE.QPBT.combinedPoint, _root_.MIPStarRE.QPBT.combinedPointVar]

@[simp] theorem combinedPoint_combinedCoefficientVar {K : Type*} {m k : ℕ}
    (u : Fin m → K) (α : Fin k → K) (r : Fin k) :
    _root_.MIPStarRE.QPBT.combinedPoint u α (_root_.MIPStarRE.QPBT.combinedCoefficientVar m k r) = α r := by
  simp [_root_.MIPStarRE.QPBT.combinedPoint, _root_.MIPStarRE.QPBT.combinedCoefficientVar]

/-! ## The restriction to a point -/

/-- The substitution replacing the point coordinates by the coordinates of `u`
and keeping the combining coordinates as variables. -/
def combinedRestrictSubstitution {K : Type*} [CommSemiring K] {m : ℕ} (k : ℕ)
    (u : Fin m → K) : Fin (m + k) → MvPolynomial (Fin k) K :=
  fun i => Sum.elim (fun j : Fin m => MvPolynomial.C (u j))
    (fun r : Fin k => MvPolynomial.X r) (finSumFinEquiv.symm i)

@[simp] theorem combinedRestrictSubstitution_point {K : Type*} [CommSemiring K]
    {m k : ℕ} (u : Fin m → K) (j : Fin m) :
    _root_.MIPStarRE.QPBT.combinedRestrictSubstitution k u (_root_.MIPStarRE.QPBT.combinedPointVar m k j) =
      MvPolynomial.C (u j) := by
  simp [_root_.MIPStarRE.QPBT.combinedRestrictSubstitution, _root_.MIPStarRE.QPBT.combinedPointVar]

@[simp] theorem combinedRestrictSubstitution_coefficient {K : Type*} [CommSemiring K]
    {m k : ℕ} (u : Fin m → K) (r : Fin k) :
    _root_.MIPStarRE.QPBT.combinedRestrictSubstitution k u (_root_.MIPStarRE.QPBT.combinedCoefficientVar m k r) =
      (MvPolynomial.X r : MvPolynomial (Fin k) K) := by
  simp [_root_.MIPStarRE.QPBT.combinedRestrictSubstitution, _root_.MIPStarRE.QPBT.combinedCoefficientVar]

/-- The polynomial `p(u, ·)` in the combining variables obtained from `p` by
substituting the point `u` for the point variables. -/
def combinedRestrict {K : Type*} [CommSemiring K] {m k : ℕ}
    (p : MvPolynomial (Fin (m + k)) K) (u : Fin m → K) : MvPolynomial (Fin k) K :=
  MvPolynomial.aeval (_root_.MIPStarRE.QPBT.combinedRestrictSubstitution k u) p











end

end MIPStarRE.QPBT
