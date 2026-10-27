-- Generated from QPBT/Combining/ExtendedLineGame/ParameterCompletion.lean by skeleton subtraction.
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
import Definitions.Def_QPBT_QPBT_Algebra_Coefficients
import Definitions.Def_QPBT_QPBT_Algebra_FieldBasis
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Game
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Geometry
import Definitions.Def_QPBT_QPBT_Games_Defs
import Mathlib
import Mathlib.Analysis.MeanInequalitiesPow

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT
namespace MIPStarRE.QPBT.ExtendedLineGame
end MIPStarRE.QPBT.ExtendedLineGame

/-!
# Parameter evaluation versus completed line evaluation

Completed evaluation of a coefficient vector may return `none`, notably on a
zero-direction line when the represented polynomial is not constant.  A
successful completed readout at the point represented by a parameter agrees
with ordinary coefficient evaluation at that parameter.  Consequently,
parameter-value disagreement is contained in the union of completed-readout
disagreement and the two failure events.

The final theorem lifts this inclusion to the Born weights of two arbitrary
strategy POVMs.  It uses neither projectivity nor a collision estimate.

## References

- `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:230-390`
- `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1267-1402`
-/

@[expose] public section

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT

noncomputable section

namespace ExtendedLineGame





/-- Born mass of disagreement between the two parameter evaluations. -/
def parameterEvalDefect {G : _root_.MIPStarRE.QPBT.Game} {params : _root_.MIPStarRE.QPBT.DirectLdParams} {degree : ℕ}
    (S : _root_.MIPStarRE.QPBT.Strategy G) (questionA : G.QuestionA) (questionB : G.QuestionB)
    (readA : G.AnswerA → _root_.MIPStarRE.QPBT.DirectDegPoly params degree)
    (readB : G.AnswerB → _root_.MIPStarRE.QPBT.DirectDegPoly params degree)
    (parameter : _root_.MIPStarRE.QPBT.DirectScalarQ params) : ℝ :=
  _root_.MIPStarRE.QPBT.outcomeEventWeight S questionA questionB fun answerA answerB =>
    _root_.MIPStarRE.QPBT.evalCoefficient (readA answerA) parameter ≠
      _root_.MIPStarRE.QPBT.evalCoefficient (readB answerB) parameter

/-- Born mass of disagreement between the two completed evaluation readouts. -/
def completedEvalDefect {G : _root_.MIPStarRE.QPBT.Game} {params : _root_.MIPStarRE.QPBT.DirectLdParams} {degree : ℕ}
    (S : _root_.MIPStarRE.QPBT.Strategy G) (questionA : G.QuestionA) (questionB : G.QuestionB)
    (readA : G.AnswerA → _root_.MIPStarRE.QPBT.DirectDegPoly params degree)
    (readB : G.AnswerB → _root_.MIPStarRE.QPBT.DirectDegPoly params degree)
    (line : _root_.MIPStarRE.QPBT.DirectLineDesc params) (parameter : _root_.MIPStarRE.QPBT.DirectScalarQ params) : ℝ :=
  _root_.MIPStarRE.QPBT.outcomeEventWeight S questionA questionB fun answerA answerB =>
    _root_.MIPStarRE.QPBT.directEvalOpt line (line.base + parameter • line.direction) (readA answerA) ≠
      _root_.MIPStarRE.QPBT.directEvalOpt line (line.base + parameter • line.direction) (readB answerB)

/-- Alice's marginal Born mass of a failed completed evaluation. -/
def completedEvalNoneMassA {G : _root_.MIPStarRE.QPBT.Game} {params : _root_.MIPStarRE.QPBT.DirectLdParams} {degree : ℕ}
    (S : _root_.MIPStarRE.QPBT.Strategy G) (questionA : G.QuestionA)
    (readA : G.AnswerA → _root_.MIPStarRE.QPBT.DirectDegPoly params degree)
    (line : _root_.MIPStarRE.QPBT.DirectLineDesc params) (parameter : _root_.MIPStarRE.QPBT.DirectScalarQ params) : ℝ :=
  _root_.MIPStarRE.QPBT.aliceEventWeight S questionA fun answerA =>
    _root_.MIPStarRE.QPBT.directEvalOpt line (line.base + parameter • line.direction) (readA answerA) = none

/-- Bob's marginal Born mass of a failed completed evaluation. -/
def completedEvalNoneMassB {G : _root_.MIPStarRE.QPBT.Game} {params : _root_.MIPStarRE.QPBT.DirectLdParams} {degree : ℕ}
    (S : _root_.MIPStarRE.QPBT.Strategy G) (questionB : G.QuestionB)
    (readB : G.AnswerB → _root_.MIPStarRE.QPBT.DirectDegPoly params degree)
    (line : _root_.MIPStarRE.QPBT.DirectLineDesc params) (parameter : _root_.MIPStarRE.QPBT.DirectScalarQ params) : ℝ :=
  _root_.MIPStarRE.QPBT.bobEventWeight S questionB fun answerB =>
    _root_.MIPStarRE.QPBT.directEvalOpt line (line.base + parameter • line.direction) (readB answerB) = none



end ExtendedLineGame

end

end MIPStarRE.QPBT
