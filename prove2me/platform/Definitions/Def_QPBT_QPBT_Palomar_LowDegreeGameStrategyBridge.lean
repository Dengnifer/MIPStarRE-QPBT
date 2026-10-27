-- Generated from QPBT/Palomar/LowDegreeGameStrategyBridge.lean by skeleton subtraction.
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
import Definitions.Def_QPBT_QPBT_Algebra_FieldBasis
import Definitions.Def_QPBT_QPBT_Games_Defs
import Definitions.Def_QPBT_QPBT_Palomar_Bridge
import Definitions.Def_QPBT_QPBT_Palomar_Definitions
import Definitions.Def_QPBT_QPBT_Palomar_LowDegreeGameBridge
import Definitions.Def_QPBT_QPBT_Test_LowDegreeGame
import Mathlib

namespace MIPStarRE.QPBT.Palomar
end MIPStarRE.QPBT.Palomar
namespace MIPStarRE.QPBT.Palomar.Game
end MIPStarRE.QPBT.Palomar.Game
namespace MIPStarRE.QPBT.Palomar.POVM
end MIPStarRE.QPBT.Palomar.POVM
namespace MIPStarRE.QPBT.Palomar.Strategy
end MIPStarRE.QPBT.Palomar.Strategy

/-!
# Strategy bridge for the compact low individual degree game

This module transports compact strategies across the exact question and answer
equivalences of `LowDegreeGameBridge`.  The transported game is the existing
low-degree game, and every compact strategy has exactly the same Born value
after conversion through the Palomar foundation bridge.

## References

`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:31-440`.
-/

@[expose] public section

open scoped BigOperators

namespace MIPStarRE.QPBT.Palomar

noncomputable section

namespace POVM

/-- Relabel the outcomes of a compact POVM along an equivalence. -/
def relabel {A B I : Type*} [Fintype A] [Fintype B] [Fintype I]
    [DecidableEq I] (e : A ≃ B) (M : _root_.MIPStarRE.QPBT.Palomar.POVM A I) : _root_.MIPStarRE.QPBT.Palomar.POVM B I where
  effect := fun b => M.effect (e.symm b)
  pos := fun b => M.pos (e.symm b)
  sum_eq_one := by
    calc
      ∑ b : B, M.effect (e.symm b) = ∑ a : A, M.effect a :=
        Equiv.sum_comp e.symm M.effect
      _ = 1 := M.sum_eq_one

/-- Outcome relabeling preserves every POVM effect. -/
@[simp] theorem relabel_effect {A B I : Type*} [Fintype A] [Fintype B]
    [Fintype I] [DecidableEq I] (e : A ≃ B) (M : _root_.MIPStarRE.QPBT.Palomar.POVM A I) (b : B) :
    (_root_.MIPStarRE.QPBT.Palomar.POVM.relabel e M).effect b = M.effect (e.symm b) :=
  rfl



end POVM

namespace Game

/-- Two compact games on fixed carriers are equal when their data fields agree. -/
theorem ext {X Y A B : Type}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    [DecidableEq X] [DecidableEq Y] [DecidableEq A] [DecidableEq B]
    {G H : _root_.MIPStarRE.QPBT.Palomar.Game X Y A B} (hμ : G.μ = H.μ) (hdecide : G.decide = H.decide) :
    G = H := by
  cases G
  cases H
  simp_all

/-- Relabel all question and answer carriers of a compact game. -/
def relabel {X Y A B X' Y' A' B' : Type}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    [Fintype X'] [Fintype Y'] [Fintype A'] [Fintype B']
    [DecidableEq X] [DecidableEq Y] [DecidableEq A] [DecidableEq B]
    [DecidableEq X'] [DecidableEq Y'] [DecidableEq A'] [DecidableEq B']
    (G : _root_.MIPStarRE.QPBT.Palomar.Game X Y A B) (eX : X ≃ X') (eY : Y ≃ Y')
    (eA : A ≃ A') (eB : B ≃ B') : _root_.MIPStarRE.QPBT.Palomar.Game X' Y' A' B' where
  μ := G.μ.map (Equiv.prodCongr eX eY)
  decide := fun x y a b =>
    G.decide (eX.symm x) (eY.symm y) (eA.symm a) (eB.symm b)

end Game

namespace Strategy

/-- Relabel the questions and outcomes of a compact strategy. -/
def relabel {X Y A B X' Y' A' B' : Type}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    [Fintype X'] [Fintype Y'] [Fintype A'] [Fintype B']
    (S : _root_.MIPStarRE.QPBT.Palomar.Strategy X Y A B) (eX : X ≃ X') (eY : Y ≃ Y')
    (eA : A ≃ A') (eB : B ≃ B') : _root_.MIPStarRE.QPBT.Palomar.Strategy X' Y' A' B' where
  ιA := S.ιA
  ιB := S.ιB
  ψ := S.ψ
  ψ_norm := S.ψ_norm
  alice := fun x => _root_.MIPStarRE.QPBT.Palomar.POVM.relabel eA (S.alice (eX.symm x))
  bob := fun y => _root_.MIPStarRE.QPBT.Palomar.POVM.relabel eB (S.bob (eY.symm y))

/-- Relabeling preserves each Born weight after pulling back all four labels. -/
@[simp] theorem outcomeWeight_relabel {X Y A B X' Y' A' B' : Type}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    [Fintype X'] [Fintype Y'] [Fintype A'] [Fintype B']
    (S : _root_.MIPStarRE.QPBT.Palomar.Strategy X Y A B) (eX : X ≃ X') (eY : Y ≃ Y')
    (eA : A ≃ A') (eB : B ≃ B') (x : X') (y : Y') (a : A') (b : B') :
    (_root_.MIPStarRE.QPBT.Palomar.Strategy.relabel S eX eY eA eB).outcomeWeight x y a b =
      S.outcomeWeight (eX.symm x) (eY.symm y) (eA.symm a) (eB.symm b) :=
  rfl







end Strategy



/-- Convert a compact low-degree strategy into a strategy for the registered game. -/
def lowDegreeStrategyToLibrary (P : _root_.MIPStarRE.QPBT.LdParams)
    (S : _root_.MIPStarRE.QPBT.Palomar.Strategy
      (_root_.MIPStarRE.QPBT.Palomar.LowDegreeQuestion (_root_.MIPStarRE.QPBT.Palomar.LowDegreeParams.ofLdParams P) (_root_.MIPStarRE.QPBT.ScalarQ P))
      (_root_.MIPStarRE.QPBT.Palomar.LowDegreeQuestion (_root_.MIPStarRE.QPBT.Palomar.LowDegreeParams.ofLdParams P) (_root_.MIPStarRE.QPBT.ScalarQ P))
      (_root_.MIPStarRE.QPBT.Palomar.LowDegreeAnswer (_root_.MIPStarRE.QPBT.Palomar.LowDegreeParams.ofLdParams P) (_root_.MIPStarRE.QPBT.ScalarQ P))
      (_root_.MIPStarRE.QPBT.Palomar.LowDegreeAnswer (_root_.MIPStarRE.QPBT.Palomar.LowDegreeParams.ofLdParams P) (_root_.MIPStarRE.QPBT.ScalarQ P))) :
    _root_.MIPStarRE.QPBT.Strategy (_root_.MIPStarRE.QPBT.ldGame P) :=
  _root_.MIPStarRE.QPBT.Palomar.Strategy.toStrategy (G := _root_.MIPStarRE.QPBT.ldGame P)
    (_root_.MIPStarRE.QPBT.Palomar.Strategy.relabel S
      (_root_.MIPStarRE.QPBT.Palomar.lowDegreeQuestionEquiv P) (_root_.MIPStarRE.QPBT.Palomar.lowDegreeQuestionEquiv P)
      (_root_.MIPStarRE.QPBT.Palomar.lowDegreeAnswerEquiv P) (_root_.MIPStarRE.QPBT.Palomar.lowDegreeAnswerEquiv P))





end

end MIPStarRE.QPBT.Palomar
