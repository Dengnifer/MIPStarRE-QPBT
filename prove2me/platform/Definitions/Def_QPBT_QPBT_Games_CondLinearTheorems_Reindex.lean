-- Generated from QPBT/Games/CondLinearTheorems/Reindex.lean by skeleton subtraction.
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

namespace MIPStarRE.QPBT
end MIPStarRE.QPBT

/-!
# Reindexing of conditionally linear functions

A conditionally linear function of one register space transports along an
injective map of index types.  The transported function restricts a coefficient
vector to the registers named by that map, applies the original function, and
extends the result by zero outside the image; it is conditionally linear at the
same level on the full register.  In the one-level case the predicate holds of
every linear map of the ambient coefficient space, which is the converse
direction of the remark following `def:cl-func`.

## References

The source definition is `def:cl-func` in
`blueprint/src/chapter/ch12_qpbt_games.tex`, with paper origin
`references/qpbt-paper/05_conditionally_linear_functions.tex:35-57`.
-/

@[expose] public section

namespace MIPStarRE.QPBT



/-- Transport a linear map of coefficient vectors along a reindexing `f` of
registers: restrict a vector to the registers named by `f`, apply the map, and
extend the result by zero outside the image of `f`.  This is the composition of
restriction along `f` with `Function.ExtendByZero.linearMap`, named here for the
reindexing of `def:cl-func`. -/
noncomputable def reindexLinearMap {K κ ι : Type*} [Field K] (f : κ → ι)
    (L : (κ → K) →ₗ[K] (κ → K)) : (ι → K) →ₗ[K] (ι → K) :=
  (Function.ExtendByZero.linearMap K f).comp (L.comp (LinearMap.funLeft K K f))

@[simp]
theorem reindexLinearMap_apply {K κ ι : Type*} [Field K] (f : κ → ι)
    (L : (κ → K) →ₗ[K] (κ → K)) (x : ι → K) :
    _root_.MIPStarRE.QPBT.reindexLinearMap f L x = Function.extend f (L fun k => x (f k)) 0 :=
  rfl











end MIPStarRE.QPBT
