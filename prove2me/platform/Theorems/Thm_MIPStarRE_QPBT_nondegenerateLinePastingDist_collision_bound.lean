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
import Definitions.Def_QPBT_QPBT_Combining_Lines_NondegeneratePastingDistribution
import Definitions.Def_QPBT_QPBT_Games_DistributionAux
import Definitions.Def_QPBT_QPBT_Games_Sandwich_Defs
import Definitions.Def_QPBT_QPBT_Observables_LineDefs
import Definitions.Def_QPBT_QPBT_Observables_WinImplications_Setup
import Definitions.Def_QPBT_QPBT_Test_LowDegreeGame
import Definitions.Def_QPBT_QPBT_Test_PauliBasisTest
import Mathlib
import Mathlib.Analysis.MeanInequalitiesPow

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT

/-!
# Conditional collision bound for nondegenerate line pasting

This module verifies the conditional collision hypothesis used when applying
the pasting lemma to the proof-only nondegenerate line-pasting distribution.

## References

The collision estimate supports `lem:qld-xz-lines` at
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:950-963` and
instantiates the hypothesis of `lem:pasting` at
`references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:504-525`.
-/



open MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT

theorem MIPStarRE.QPBT.nondegenerateLinePastingDist_collision_bound
    (P : _root_.MIPStarRE.QPBT.AdmissibleParams) (bound : ℕ) :
    _root_.MIPStarRE.QPBT.HasConditionalCollisionBound (_root_.MIPStarRE.QPBT.nondegenerateLinePastingDist P.toLdParams)
      (fun (poly : _root_.MIPStarRE.QPBT.DegPoly P.toLdParams bound) sample => _root_.MIPStarRE.QPBT.evalOpt sample.1 sample.2 poly)
      ((bound : ℝ) / Fintype.card (_root_.MIPStarRE.QPBT.ScalarQ P.toLdParams)) := by sorry
