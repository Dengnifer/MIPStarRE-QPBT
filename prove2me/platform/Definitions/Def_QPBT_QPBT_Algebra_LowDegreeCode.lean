-- Generated from QPBT/Algebra/LowDegreeCode.lean by skeleton subtraction.
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
import Mathlib

namespace MIPStarRE.QPBT
end MIPStarRE.QPBT
namespace MvPolynomial
end MvPolynomial

/-!
# The low-degree encoding

This module encodes the Boolean subcube by multilinear indicator polynomials
and packages the resulting low-degree code as honest polynomial representatives.

## References

The source-facing nodes are blueprint `def:polynomials-degree`,
`def:low-degree-encoding`, and `def:indicator-vector`; the paper origin is
`references/qpbt-paper/04_preliminaries.tex:832-897`.
The polynomial class `def:polyfunc` is reused from
`MIPStarRE.LDT.Preliminaries.polyFunc` (the LDT formalization).

Note: this module contributes declarations to the comparator statement closure
of the QPBT headline theorems, which must elaborate in the same environment as
the Mathlib-only `ChallengeQPBT.lean`.  Keep the full `import Mathlib`; do not
narrow it.  See `docs/comparator.md`, "Environment alignment".
-/

@[expose] public section

open scoped BigOperators
open MvPolynomial

namespace MIPStarRE.QPBT

/- The Boolean cube indexes the `2^m` qudits in the low-degree encoding. -/
/-- The Boolean cube indexing the `2^m` qudits of the test.  This is the index
type in blueprint
`def:low-degree-encoding`, paper origin
`references/qpbt-paper/04_preliminaries.tex:832-897`.
-/
abbrev Cube (m : ℕ) := Fin m → Bool

/--
The representative polynomial which is `1` at `y` on the Boolean cube and
zero at the other cube points.  This is the indicator polynomial in blueprint
`def:low-degree-encoding`; paper
`references/qpbt-paper/04_preliminaries.tex:832-897`.
-/
noncomputable def indicatorPoly {K : Type*} [CommRing K] {m : ℕ} (y : _root_.MIPStarRE.QPBT.Cube m) :
    MvPolynomial (Fin m) K :=
  ∏ i : Fin m, if y i then X i else (1 - X i)

/--
The multilinear low-degree encoding of a coefficient string.  Polynomial
representatives are used, as fixed by issue Dengnifer/MIPStarRE-QPBT-bak#0004, rather than
quotienting by
functional equality.  Blueprint: `def:low-degree-encoding`; paper origin:
`references/qpbt-paper/04_preliminaries.tex:832-897`.
-/
noncomputable def lowDegreeEncoding {K : Type*} [CommRing K] {m : ℕ}
    (a : _root_.MIPStarRE.QPBT.Cube m → K) : MvPolynomial (Fin m) K :=
  ∑ y : _root_.MIPStarRE.QPBT.Cube m, a y • _root_.MIPStarRE.QPBT.indicatorPoly y

/- Evaluation shorthand for the representative polynomial in
`def:low-degree-encoding`; it is Lean-only notation. -/
/-- Evaluation shorthand for the low-degree encoding.  Blueprint
`def:low-degree-encoding`, paper origin
`references/qpbt-paper/04_preliminaries.tex:832-897`.
-/
noncomputable def lowDegreeEnc {K : Type*} [CommRing K] {m : ℕ}
    (a : _root_.MIPStarRE.QPBT.Cube m → K) (x : Fin m → K) : K :=
  eval x (_root_.MIPStarRE.QPBT.lowDegreeEncoding a)

/--
The indicator vector `ind_m(x)` of `def:indicator-vector`.
Blueprint: `def:indicator-vector`; paper origin:
`references/qpbt-paper/04_preliminaries.tex:832-897`.
-/
noncomputable def indicatorVec {K : Type*} [CommRing K] {m : ℕ}
    (x : Fin m → K) : _root_.MIPStarRE.QPBT.Cube m → K :=
  fun y => eval x (_root_.MIPStarRE.QPBT.indicatorPoly y)

/--
The defining dot-product identity for the encoding, corresponding to
Equation `eq:low-degree-encoding-definition` and `def:indicator-vector` in the
blueprint, with source node `def:indicator-vector`; paper origin
`references/qpbt-paper/04_preliminaries.tex:832-897`.
-/
theorem lowDegreeEnc_eq_dotProduct {K : Type*} [CommRing K] {m : ℕ}
    (a : _root_.MIPStarRE.QPBT.Cube m → K) (x : Fin m → K) :
    _root_.MIPStarRE.QPBT.lowDegreeEnc a x = dotProduct a (_root_.MIPStarRE.QPBT.indicatorVec x) := by
  simp [_root_.MIPStarRE.QPBT.lowDegreeEnc, _root_.MIPStarRE.QPBT.lowDegreeEncoding, _root_.MIPStarRE.QPBT.indicatorVec, dotProduct]

/--
The coordinatewise product form of an entry of the indicator vector: at a cube
point `y` the entry is the product of `x i` over the coordinates with `y i`
true and of `1 - x i` over the remaining ones.  Blueprint
`def:indicator-vector`;
paper origin: `references/qpbt-paper/04_preliminaries.tex:832-897`.
-/
theorem indicatorVec_apply_eq_prod {K : Type*} [CommRing K] {m : ℕ}
    (x : Fin m → K) (y : _root_.MIPStarRE.QPBT.Cube m) :
    _root_.MIPStarRE.QPBT.indicatorVec x y = ∏ i : Fin m, if y i then x i else 1 - x i := by
  simp [_root_.MIPStarRE.QPBT.indicatorVec, _root_.MIPStarRE.QPBT.indicatorPoly, apply_ite]



end MIPStarRE.QPBT
