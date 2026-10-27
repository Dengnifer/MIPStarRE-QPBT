-- Generated from QPBT/Games/Consistency.lean by skeleton subtraction.
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
import Definitions.Def_LIDT_MIPStarRE_Quantum_Measurement
import Definitions.Def_QPBT_QPBT_Games_Defs
import Definitions.Def_QPBT_QPBT_Games_Distance
import Definitions.Def_QPBT_QPBT_State

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT

/-! # State-dependent consistency and strategy closeness

The definitions are the finite-dimensional forms of blueprint
`def:consistency` and `def:strategy-distance`,
from `references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:219-288`.
-/

@[expose] public section

open scoped BigOperators

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT LIDT.MIPStarRE.Quantum

/-- The off-diagonal defect in blueprint
`def:consistency`, paper `06_nonlocal_games_and_mipstar.tex:232-248`. -/
noncomputable def consistencyDefect {X α ι : Type*}
    [Fintype X] [DecidableEq X] [Fintype α] [DecidableEq α]
    [Fintype ι] [DecidableEq ι]
    (μ : _root_.LIDT.MIPStarRE.LDT.Distribution X) (A B : X → α → _root_.LIDT.MIPStarRE.Quantum.Op ι)
    (ψ : EuclideanSpace ℂ ι) : ℝ :=
  _root_.LIDT.MIPStarRE.LDT.avgOver μ (fun x =>
    ∑ a : α, ∑ b : α,
      if a = b then 0 else
        (inner ℂ ψ ((EuclideanSpace.equiv ι ℂ).symm
          ((A x a * B x b).mulVec ψ))).re)











/-- Unit-alphabet specialization of blueprint
`def:povm-distance`, paper `06_nonlocal_games_and_mipstar.tex:258-271`. -/
noncomputable def opDistSq {X ι : Type*}
    [Fintype X] [DecidableEq X] [Fintype ι] [DecidableEq ι]
    (μ : _root_.LIDT.MIPStarRE.LDT.Distribution X) (M N : X → _root_.LIDT.MIPStarRE.Quantum.Op ι) (ψ : EuclideanSpace ℂ ι) : ℝ :=
  _root_.MIPStarRE.QPBT.opFamilyDistSq μ (fun x (_ : Unit) => M x) (fun x (_ : Unit) => N x) ψ



/-- The strategy-distance relation `def:strategy-distance`. The two strategies'
local Hilbert spaces are identified, and both measurement distances are
evaluated on the first strategy's state. Blueprint
`def:strategy-distance`, paper `06_nonlocal_games_and_mipstar.tex:273-285`. -/
structure AreCloseStrategies (G : _root_.MIPStarRE.QPBT.Game) (S S' : _root_.MIPStarRE.QPBT.Strategy G) (δ : ℝ) : Prop where
  /-- Identification of Alice's local Hilbert spaces. -/
  hA : S.ιA = S'.ιA
  /-- Identification of Bob's local Hilbert spaces. -/
  hB : S.ιB = S'.ιB
  state : _root_.MIPStarRE.QPBT.stateDistSq S.ψ (_root_.MIPStarRE.QPBT.reindexState
      (Equiv.prodCongr (Equiv.cast hA).symm (Equiv.cast hB).symm) S'.ψ) ≤ δ
  alice : _root_.MIPStarRE.QPBT.opFamilyDistSq (G.μ.map Prod.fst)
      (fun x a => _root_.MIPStarRE.QPBT.heteroKron ((S.A x).effect a) 1)
      (fun x a => _root_.MIPStarRE.QPBT.heteroKron (_root_.MIPStarRE.QPBT.reindexOp (Equiv.cast hA) ((S'.A x).effect a)) 1)
      S.ψ ≤ δ
  bob : _root_.MIPStarRE.QPBT.opFamilyDistSq (G.μ.map Prod.snd)
      (fun y b => _root_.MIPStarRE.QPBT.heteroKron 1 ((S.B y).effect b))
      (fun y b => _root_.MIPStarRE.QPBT.heteroKron 1 (_root_.MIPStarRE.QPBT.reindexOp (Equiv.cast hB) ((S'.B y).effect b)))
      S.ψ ≤ δ

end MIPStarRE.QPBT
