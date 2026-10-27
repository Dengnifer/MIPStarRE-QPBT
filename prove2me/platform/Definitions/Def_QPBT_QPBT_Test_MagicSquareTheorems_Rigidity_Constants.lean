-- Generated from QPBT/Test/MagicSquareTheorems/Rigidity/Constants.lean by skeleton subtraction.
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

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
namespace MIPStarRE.QPBT.MagicSquareRigidity
end MIPStarRE.QPBT.MagicSquareRigidity

/-!
# Coarse estimates and the large-error regime of Magic Square rigidity

The rigidity theorem `thm:ms-rigidity` asserts a bound at the scale
`C * (sqrt ε + sqrt δ)` with a universal constant `C`.  Once `sqrt ε + sqrt δ`
exceeds one, that scale exceeds `C`, and the assertion is carried by the trivial
estimates available for *any* witness: two unit vectors are at distance at most
two, the state-dependent distance between two contractions on a unit vector is
at most two, and a two-outcome family therefore has squared distance at most
eight.

This file collects those estimates together with the elementary isometry used to
build a witness for an arbitrary strategy: the embedding of a local space as the
fiber of the extracted register over one fixed basis vector.  The estimates are
stated for the one-point distribution and the binary alphabet in which the
rigidity conclusions are phrased.

## References

blueprint `thm:ms-rigidity`,
paper `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:612-652`.
The distance conventions are blueprint
`def:povm-distance`, paper `06_nonlocal_games_and_mipstar.tex:258-285`.
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT.MagicSquareRigidity

open LIDT.MIPStarRE.LDT LIDT.MIPStarRE.Quantum

noncomputable section

/-! ## The fiber embedding of a local space in an extracted register -/

/-- Formalization-only linear embedding of a local space as the fiber of a
register over one fixed basis vector.  It is the coarse counterpart of the
swap isometries of `Rigidity/Swap.lean`, used to exhibit a witness of
`thm:ms-rigidity` for an arbitrary strategy in the regime where the asserted
bound is vacuous. -/
def registerFiberEmbeddingMap (κ ι : Type) [Fintype κ] [DecidableEq κ]
    [Fintype ι] [DecidableEq ι] (k : κ) :
    EuclideanSpace ℂ ι →ₗ[ℂ] EuclideanSpace ℂ (κ × ι) where
  toFun x := (EuclideanSpace.equiv (κ × ι) ℂ).symm
    (fun p => if p.1 = k then x p.2 else 0)
  map_add' x y := by
    ext p
    by_cases h : p.1 = k <;> simp [h]
  map_smul' c x := by
    ext p
    by_cases h : p.1 = k <;> simp [h]

/-- Formalization-only isometric embedding of a local space as the fiber of a
register over one fixed basis vector. -/
noncomputable def registerFiberEmbedding (κ ι : Type) [Fintype κ] [DecidableEq κ]
    [Fintype ι] [DecidableEq ι] (k : κ) :
    EuclideanSpace ℂ ι →ₗᵢ[ℂ] EuclideanSpace ℂ (κ × ι) :=
  LinearMap.isometryOfInner (_root_.MIPStarRE.QPBT.MagicSquareRigidity.registerFiberEmbeddingMap κ ι k) <| by
    intro x y
    simp [PiLp.inner_apply, Fintype.sum_prod_type, _root_.MIPStarRE.QPBT.MagicSquareRigidity.registerFiberEmbeddingMap]

/-- The coordinates of the fiber embedding. -/
@[simp]
theorem registerFiberEmbedding_apply {κ ι : Type} [Fintype κ] [DecidableEq κ]
    [Fintype ι] [DecidableEq ι] (k : κ) (x : EuclideanSpace ℂ ι) (p : κ × ι) :
    _root_.MIPStarRE.QPBT.MagicSquareRigidity.registerFiberEmbedding κ ι k x p = if p.1 = k then x p.2 else 0 := rfl

/-! ## Coarse contraction estimates -/







end

end MIPStarRE.QPBT.MagicSquareRigidity
