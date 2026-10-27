-- Generated from QPBT/Algebra/Decoding.lean by skeleton subtraction.
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
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_Polynomials
import Definitions.Def_LIDT_MIPStarRE_LDT_Tactic_AvgCongr
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyCore
import Definitions.Def_QPBT_QPBT_Algebra_FieldBasis
import Definitions.Def_QPBT_QPBT_Algebra_LowDegreeCode
import Definitions.Def_QPBT_QPBT_Algebra_LowDegreeCodeTheorems
import Definitions.Def_QPBT_QPBT_Combining_Defs
import Definitions.Def_QPBT_QPBT_Test_PauliBasisTest
import Mathlib

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.LDT.Preliminaries
end LIDT.MIPStarRE.LDT.Preliminaries
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT

/-! # Polynomial decoding for Pauli extraction

This module provides the Chapter 16 decoder on the Chapter 15 bounded
polynomial representative type.  The generic retained-value decoder and its
specialization to polynomial representatives live in
`Algebra/LowDegreeCodeTheorems`; this module states the corresponding maps on
`Poly P` used in the extraction chapter.

## References

The decoder is blueprint `def:decoding-map`, with its extraction use in
blueprint `sec:separating` and paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1419-1450`.
The restricted decoder identity and its encoding hypothesis are documented in
`docs/paper-gaps/qpbt_decoding-identity.tex:87-123`.
-/

@[expose] public section

open scoped BigOperators

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT LIDT.MIPStarRE.LDT.Preliminaries

/-! ## Representative evaluation and decoding -/

/-- Evaluate the polynomial representative carried by `Poly P`.

This is polynomial evaluation on the source's `\ideg_{d,m}(\F_q)` carrier.  It
does not identify representatives that induce the same polynomial function. -/
noncomputable def evalPoly {P : _root_.MIPStarRE.QPBT.AdmissibleParams} (g : _root_.MIPStarRE.QPBT.Poly P)
    (x : Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P) : _root_.MIPStarRE.QPBT.PauliScalar P :=
  MvPolynomial.eval x g.1

/-- Decode a bounded polynomial while retaining only values in `H`.

This is the `H`-parameterized form of `def:decoding-map`; `decodeAt` remains
the decoding map for arbitrary functions.  The Boolean cube is embedded in
`PauliScalar P` by `cubeEmbed`. -/
noncomputable def decodeOn {P : _root_.MIPStarRE.QPBT.AdmissibleParams}
    (H : Finset (_root_.MIPStarRE.QPBT.PauliScalar P)) (g : _root_.MIPStarRE.QPBT.Poly P) : _root_.MIPStarRE.QPBT.PauliRegister P :=
  _root_.MIPStarRE.QPBT.decodeAt H (fun x => _root_.MIPStarRE.QPBT.evalPoly g x)

/-- Full-field specialization of `decodeOn` used in Chapter 16.

The retained-value set is `Finset.univ`, so every field value is kept.  This
choice is the correction recorded in
`docs/paper-gaps/qpbt_decoding-identity.tex:87-123`. -/
noncomputable abbrev decodeOnUniv {P : _root_.MIPStarRE.QPBT.AdmissibleParams} (g : _root_.MIPStarRE.QPBT.Poly P) :
    _root_.MIPStarRE.QPBT.PauliRegister P :=
  _root_.MIPStarRE.QPBT.decodeOn (Finset.univ : Finset (_root_.MIPStarRE.QPBT.PauliScalar P)) g

/-- The full-field decoder `\operatorname{Dec}_{\F_q}` on `Poly P`.

The map `decodeFqRep` has the same definition on arbitrary polynomial
representatives; `decodeFq` restricts its domain to the bounded-degree class
`Poly P`. -/
noncomputable abbrev decodeFq {P : _root_.MIPStarRE.QPBT.AdmissibleParams} (g : _root_.MIPStarRE.QPBT.Poly P) :
    _root_.MIPStarRE.QPBT.PauliRegister P :=
  _root_.MIPStarRE.QPBT.decodeOnUniv g

/-! ## The encoding image -/

/-- Membership of a multilinear encoding in the bounded representative class.

Each indicator factor has degree zero away from its own variable and degree at
most one in that variable, so the multilinear encoding has individual degree at
most one, and hence at most `P.d` using `P.hd`.  This is the degree
side-condition implicit in the source's `g_h` construction, not an extra
hypothesis of the decoding identity.  See blueprint
`def:low-degree-encoding`, and paper
`references/qpbt-paper/04_preliminaries.tex:832-897`. -/
theorem lowDegreeEncoding_mem_poly {P : _root_.MIPStarRE.QPBT.AdmissibleParams}
    (h : _root_.MIPStarRE.QPBT.PauliRegister P) :
    _root_.MIPStarRE.QPBT.lowDegreeEncoding h ∈
      _root_.LIDT.MIPStarRE.LDT.Preliminaries.polyFunc P.m (_root_.MIPStarRE.QPBT.PauliScalar P) P.d := by
  rw [MvPolynomial.mem_restrictDegree]
  intro s hs i
  apply (MvPolynomial.monomial_le_degreeOf i hs).trans
  rw [_root_.MIPStarRE.QPBT.lowDegreeEncoding]
  refine (MvPolynomial.degreeOf_sum_le i Finset.univ _).trans ?_
  refine Finset.sup_le fun y _ => ?_
  refine (show MvPolynomial.degreeOf i
      (h y • _root_.MIPStarRE.QPBT.indicatorPoly (K := _root_.MIPStarRE.QPBT.PauliScalar P) y) ≤
      MvPolynomial.degreeOf i (_root_.MIPStarRE.QPBT.indicatorPoly (K := _root_.MIPStarRE.QPBT.PauliScalar P) y) from ?_).trans ?_
  · simpa only [MvPolynomial.smul_eq_C_mul] using
      MvPolynomial.degreeOf_C_mul_le (_root_.MIPStarRE.QPBT.indicatorPoly (K := _root_.MIPStarRE.QPBT.PauliScalar P) y) i (h y)
  rw [_root_.MIPStarRE.QPBT.indicatorPoly]
  refine (MvPolynomial.degreeOf_prod_le i Finset.univ _).trans ?_
  calc
    ∑ j, MvPolynomial.degreeOf i
        (if y j then
          (MvPolynomial.X j : MvPolynomial (Fin P.m) (_root_.MIPStarRE.QPBT.PauliScalar P))
        else 1 - MvPolynomial.X j) ≤
        ∑ j, if i = j then 1 else 0 := by
      apply Finset.sum_le_sum
      intro j _
      split
      · exact le_of_eq (MvPolynomial.degreeOf_X i j)
      · exact (MvPolynomial.degreeOf_sub_le i 1 (MvPolynomial.X j)).trans_eq (by
          simp [MvPolynomial.degreeOf_X])
    _ = 1 := by simp
    _ ≤ P.d := P.hd

/-- The multilinear encoding as a bounded polynomial representative.

The individual-degree bound is supplied by `lowDegreeEncoding_mem_poly`. -/
noncomputable def encodingPoly {P : _root_.MIPStarRE.QPBT.AdmissibleParams} (h : _root_.MIPStarRE.QPBT.PauliRegister P) :
    _root_.MIPStarRE.QPBT.Poly P :=
  ⟨_root_.MIPStarRE.QPBT.lowDegreeEncoding h, _root_.MIPStarRE.QPBT.lowDegreeEncoding_mem_poly h⟩

/-- A `Poly P` outcome is an encoding when its decoder reconstructs the same
underlying polynomial representative.

This is the explicit support restriction required by the corrected Chapter 16
decoding argument.  It is the `Poly` view of `IsEncodingRep`; no unrestricted
decoder/evaluation identity is asserted.  See
`docs/paper-gaps/qpbt_decoding-identity.tex:87-123`. -/
def IsEncoding {P : _root_.MIPStarRE.QPBT.AdmissibleParams} (g : _root_.MIPStarRE.QPBT.Poly P) : Prop :=
  _root_.MIPStarRE.QPBT.lowDegreeEncoding (_root_.MIPStarRE.QPBT.decodeFq g) = g.1

/-! ## Decoder companions -/





/-- The full-field decoder is a left inverse to `encodingPoly`.

This is the identity `\operatorname{Dec}(g_h)=h` of
blueprint `lem:qld-decoder-linearity`, for
the full-field decoder specified at
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1419-1420`.
The degree proof is separated into `lowDegreeEncoding_mem_poly`; no additional
encoding or interpolation hypothesis is introduced.  See
`docs/paper-gaps/qpbt_decoding-identity.tex:87-123`. -/
theorem decodeFq_lowDegreeEncoding {P : _root_.MIPStarRE.QPBT.AdmissibleParams}
    (h : _root_.MIPStarRE.QPBT.PauliRegister P) :
    _root_.MIPStarRE.QPBT.decodeFq (_root_.MIPStarRE.QPBT.encodingPoly h) = h := by
  funext y
  simpa only [_root_.MIPStarRE.QPBT.decodeFq, _root_.MIPStarRE.QPBT.decodeOnUniv, _root_.MIPStarRE.QPBT.decodeOn, _root_.MIPStarRE.QPBT.decodeAt, _root_.MIPStarRE.QPBT.evalPoly,
    _root_.MIPStarRE.QPBT.encodingPoly, _root_.MIPStarRE.QPBT.lowDegreeEnc, Finset.mem_univ, if_true] using
      congrFun
        (_root_.MIPStarRE.QPBT.decodeAt_lowDegreeEnc
          (Finset.univ : Finset (_root_.MIPStarRE.QPBT.PauliScalar P)) h
            (fun z => Finset.mem_univ (h z))) y



end MIPStarRE.QPBT
