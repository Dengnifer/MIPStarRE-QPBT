-- Generated from QPBT/Games/Distance.lean by skeleton subtraction.
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_AxisParallelLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DiagonalLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_Distribution
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
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Basic
import Definitions.Def_QPBT_QPBT_Games_Defs

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT

/-!
# Quantitative state and operator distances

The blueprint uses asymptotic `approx` notation.  The skeleton records the
corresponding squared norm functionals explicitly, leaving universal-constant
estimates to later proof stages.

## References

These are blueprint `def:state-distance` and `def:povm-distance`; the paper origin is
`references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:219-271`.
-/

@[expose] public section

open scoped BigOperators

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT
open LIDT.MIPStarRE.Quantum

/--
Squared Euclidean distance between pure states.  Blueprint `def:state-distance`, paper origin
`references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:219-271`.
-/
noncomputable def stateDistSq {ι : Type*} [Fintype ι]
    [DecidableEq ι]
    (ψ φ : EuclideanSpace ℂ ι) : ℝ :=
  ‖ψ - φ‖ ^ 2

/--
Average squared state-dependent distance between two operator families.  This
is blueprint `def:povm-distance`,
with paper origin `references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:219-271`.
-/
noncomputable def opFamilyDistSq {X α ι : Type*}
    [Fintype α] [Fintype ι] [DecidableEq ι]
    (μ : _root_.LIDT.MIPStarRE.LDT.Distribution X) (M N : X → α → _root_.LIDT.MIPStarRE.Quantum.Op ι)
    (ψ : EuclideanSpace ℂ ι) : ℝ :=
  _root_.LIDT.MIPStarRE.LDT.avgOver μ (fun x =>
    ∑ a : α, ‖_root_.MIPStarRE.QPBT.applyOperatorToState (M x a - N x a) ψ‖ ^ 2)

end MIPStarRE.QPBT
