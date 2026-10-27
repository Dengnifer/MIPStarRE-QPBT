-- Generated from QPBT/Test/MagicSquareTheorems/Basic.lean by skeleton subtraction.
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
import Definitions.Def_QPBT_QPBT_Games_CondLinear
import Definitions.Def_QPBT_QPBT_Games_Defs
import Definitions.Def_QPBT_QPBT_Games_StrategyClasses
import Definitions.Def_QPBT_QPBT_Test_MagicSquare

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT

/-!
# Basic Magic Square symmetry facts

This file proves symmetry of the Magic Square question distribution and
decision predicate, packages the game as a `SymmetricGame`, and defines the
observable associated with a binary measurement.

## References

The game is blueprint
`def:ms-game`, from
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:512-610`.
-/

@[expose] public section

open scoped BigOperators Matrix

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum

noncomputable section

/-- Symmetry of the Magic Square question distribution from blueprint
`def:ms-game`, paper
`08_classical_and_quantum_low_degree_tests.tex:512-610`. -/
theorem msQuestionDistribution_symm (x y : _root_.MIPStarRE.QPBT.MsType) :
    _root_.MIPStarRE.QPBT.msGame.μ.weight (x, y) = _root_.MIPStarRE.QPBT.msGame.μ.weight (y, x) := by
  classical
  simp [_root_.MIPStarRE.QPBT.msGame, _root_.MIPStarRE.QPBT.graphDistribution, Sym2.eq_swap]

/-- Symmetry of the Magic Square decision predicate from blueprint
`def:ms-game`, paper
`08_classical_and_quantum_low_degree_tests.tex:512-610`. -/
theorem msWinPredicate_symm (x y : _root_.MIPStarRE.QPBT.MsType) (a b : _root_.MIPStarRE.QPBT.MsAnswer) :
    _root_.MIPStarRE.QPBT.msWinPredicate x y a b = _root_.MIPStarRE.QPBT.msWinPredicate y x b a := by
  cases x <;> cases y <;> cases a <;> cases b <;>
    simp [_root_.MIPStarRE.QPBT.msWinPredicate, and_comm, eq_comm]

/-- The symmetric-game presentation of the Magic Square game. -/
noncomputable def msGameSymm : _root_.MIPStarRE.QPBT.SymmetricGame where
  Question := _root_.MIPStarRE.QPBT.MsType
  Answer := _root_.MIPStarRE.QPBT.MsAnswer
  μ := _root_.MIPStarRE.QPBT.msGame.μ
  μ_prob := _root_.MIPStarRE.QPBT.msGame.μ_prob
  μ_symm := _root_.MIPStarRE.QPBT.msQuestionDistribution_symm
  decide := _root_.MIPStarRE.QPBT.msWinPredicate
  decide_symm := _root_.MIPStarRE.QPBT.msWinPredicate_symm



/-- The observable associated with a binary measurement; formalization-only notation
used in blueprint `thm:ms-from-ac`, paper
`08_classical_and_quantum_low_degree_tests.tex:658-722`. -/
def obsOf {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : _root_.LIDT.MIPStarRE.Quantum.Measurement (ZMod 2) ι) : _root_.LIDT.MIPStarRE.Quantum.Op ι :=
  M.effect 0 - M.effect 1

end

end MIPStarRE.QPBT
