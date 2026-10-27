-- Generated from QPBT/Combining/ExtendedLineGame/ScalarPolynomial.lean by skeleton subtraction.
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
import Definitions.Def_QPBT_QPBT_Combining_Defs
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Game
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Geometry
import Definitions.Def_QPBT_QPBT_Combining_Points
import Definitions.Def_QPBT_QPBT_Combining_Witnesses
import Definitions.Def_QPBT_QPBT_Test_PauliBasisTest
import Mathlib
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Analysis.MeanInequalitiesPow

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT
namespace MIPStarRE.QPBT.ExtendedLineGame
end MIPStarRE.QPBT.ExtendedLineGame

/-!
# Scalar and base coefficients of the rounded polynomial outcomes

The singleton polynomial is transported through the canonical field equivalence
and Mathlib's equivalence between a polynomial in a sum of variables and an
iterated polynomial ring. Its individual-degree certificate controls both levels.
Splitting each base coefficient by either block gives the partial degrees used
in the fiber calculation. Independence of both wrong blocks identifies the
outcome with the existing bounded polynomial-pair combining map.

## References

`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1310-1326`,
the coefficient expansion preceding `eq:qld-g-prime-bound`.
The partial coefficient argument and separated image are at lines 1341--1368,
`eq:qld-g-2` and `eq:qld-g-non-separable`; blueprint `lem:qld-4-7`.
-/

@[expose] public section

open scoped BigOperators

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement

noncomputable section

namespace ExtendedLineGame







/-- The two base blocks, in the order `x,z` used by the extended game. -/
def baseCoordinateEquiv (m : ℕ) : Fin (2 * m) ≃ Fin m ⊕ Fin m :=
  (finCongr (by omega)).trans finSumFinEquiv.symm

/-- The scalar coordinates first, followed by the combined base coordinates. -/
def scalarBaseCoordinateEquiv (m : ℕ) : Fin (2 * m + 2) ≃ Fin 2 ⊕ Fin (2 * m) :=
  (_root_.MIPStarRE.QPBT.finCombineEquiv m).trans
    ((Equiv.sumCongr (_root_.MIPStarRE.QPBT.ExtendedLineGame.baseCoordinateEquiv m).symm (Equiv.refl _)).trans
      (Equiv.sumComm _ _))

/-- The actual singleton outcome as a polynomial in `alpha,beta` with
coefficients in the `2m` base variables, over the canonical Pauli field. -/
def scalarPolynomial (P : _root_.MIPStarRE.QPBT.AdmissibleParams) (g : _root_.MIPStarRE.QPBT.DirectPolyTuple P.extendedDirectLd) :
    MvPolynomial (Fin 2) (MvPolynomial (Fin (2 * P.m)) (_root_.MIPStarRE.QPBT.PauliScalar P)) :=
  MvPolynomial.sumRingEquiv _ _ _
    (MvPolynomial.rename (_root_.MIPStarRE.QPBT.ExtendedLineGame.scalarBaseCoordinateEquiv P.m)
      (MvPolynomial.map (_root_.MIPStarRE.QPBT.extendedDirectScalarEquiv P).toRingHom (g (0 : Fin 1)).1))





/-- Split a base coefficient into a polynomial in either varying block with
coefficients in the fixed block. The order parameter selects either `x` or `z`
as the varying block. This supports the two applications of `eq:qld-g-2` in
paper lines 1341--1358 and blueprint `lem:qld-4-7`. -/
def blockCoefficientPolynomial (P : _root_.MIPStarRE.QPBT.AdmissibleParams)
    (g : _root_.MIPStarRE.QPBT.DirectPolyTuple P.extendedDirectLd) (a : Fin 2 →₀ ℕ) (reverse : Bool) :
    MvPolynomial (Fin P.m) (MvPolynomial (Fin P.m) (_root_.MIPStarRE.QPBT.PauliScalar P)) :=
  MvPolynomial.sumRingEquiv _ _ _ (MvPolynomial.rename
    ((_root_.MIPStarRE.QPBT.ExtendedLineGame.baseCoordinateEquiv P.m).trans
      (if reverse then Equiv.sumComm _ _ else Equiv.refl _)) ((_root_.MIPStarRE.QPBT.ExtendedLineGame.scalarPolynomial P g).coeff a))











/-- Split the full joint uniform point into the base point and scalar point.
This is one equivalence of sample spaces, not four marginal identifications. -/
def scalarBaseQuestionEquiv (P : _root_.MIPStarRE.QPBT.AdmissibleParams) :
    ((Fin (2 * P.m) → _root_.MIPStarRE.QPBT.PauliScalar P) × (Fin 2 → _root_.MIPStarRE.QPBT.PauliScalar P)) ≃
      _root_.MIPStarRE.QPBT.ExtendedPointQuestion P :=
  (((_root_.MIPStarRE.QPBT.ExtendedLineGame.baseCoordinateEquiv P.m).piCongrLeft fun _ => _root_.MIPStarRE.QPBT.PauliScalar P).trans
    (Equiv.sumPiEquivProdPi fun _ : Fin P.m ⊕ Fin P.m => _root_.MIPStarRE.QPBT.PauliScalar P)).prodCongr
      (finTwoArrowEquiv (_root_.MIPStarRE.QPBT.PauliScalar P))







/-- Joint sample equivalence for the fiber calculation: the first input block
is fixed and the second varies. Reversal exchanges both the point blocks and
the scalar coefficients, so its ordered product is `ZX`. This supports the
two orders in `eq:qld-g-42/43` and blueprint `lem:qld-4-7`. -/
def fiberQuestionEquiv (P : _root_.MIPStarRE.QPBT.AdmissibleParams) (reverse : Bool) :
    (((Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P) × (Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P)) ×
      (Fin 2 → _root_.MIPStarRE.QPBT.PauliScalar P)) ≃ _root_.MIPStarRE.QPBT.ExtendedPointQuestion P :=
  (if reverse then Equiv.refl _ else Equiv.prodComm _ _).prodCongr
    ((finTwoArrowEquiv (_root_.MIPStarRE.QPBT.PauliScalar P)).trans
      (if reverse then Equiv.prodComm _ _ else Equiv.refl _))











end ExtendedLineGame

end

end MIPStarRE.QPBT
