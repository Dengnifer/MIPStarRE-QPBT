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
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyBiProj_Measurements
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyCore
import Definitions.Def_QPBT_QPBT_Algebra_FieldBasis
import Definitions.Def_QPBT_QPBT_Algebra_Lines
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Game
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_GameValue
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Geometry
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Transport_BranchComparison
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Transport_Correspondence
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Transport_DiagonalRecursion
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Transport_Questions
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Transport_Strategy
import Definitions.Def_QPBT_QPBT_Games_Defs
import Definitions.Def_QPBT_QPBT_Games_StrategyClasses
import Definitions.Def_QPBT_QPBT_Test_LowDegreeGame
import Mathlib

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT

/-!
# Diagonal branches of the coordinate strategies of the direct low-degree game

The LDT `j`-restricted diagonal sampler decodes to a direct direction with
vanishing prefix below the reversed index `i = Fin.rev j`, and the transported
question of `Transport.Questions` carries the leading index of that direction.
On the generic event that the direction is nonzero at `i`, the leading index
is `i` and the question is the canonical direct question of the direct sample
`(p, i, v)`, where the LDT defect is bounded by the direct rejection.
Otherwise the restricted direction is also the restriction at the next index,
so the LDT quantity recurses to that index with the factor `q⁻¹`, the
probability that the sampled coordinate vanishes; at the last index the zero
direction has the last coordinate as its leading index by convention and no
recursion occurs.  Summing the recursion shows that each LDT diagonal branch
is at most `q / (q - 1) ≤ 2` times the corresponding branch rejection of the
direct game.  The factor is genuine: a strategy that answers the canonical
question of a direction badly and the non-canonical questions of the same
geometric line well has LDT diagonal failure exceeding the direct branch
rejection.

## References

- `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:214-458`
- `references/ldt-paper/test_definition.tex:49-65,130-151`
- Blueprint `def:ld-question-distribution`, `lem:ld-aline-level`,
  `lem:ld-dline-level`, `lem:ld-question-typed-cl`, `lem:alnf`, and `lem:dlnf`
- `docs/paper-gaps/qpbt_ld-dimension-divisibility.tex`
-/



open scoped BigOperators MatrixOrder Matrix ComplexOrder

open MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT
open LIDT.MIPStarRE.Quantum



/-! ## Direction coordinates and the one-coordinate recursion

The LDT `j`-restricted diagonal sampler decodes to a direct direction with
vanishing prefix below the reversed index `i = Fin.rev j`, and the transported
question carries the leading index of that direction.  On the generic event
that the direction is nonzero at `i`, the leading index is `i` and the
question is the canonical direct question of the direct sample `(p, i, v)`.
Otherwise the restricted direction is also the restriction at the next index,
so the LDT quantity recurses with the factor `q⁻¹`, the probability that
the sampled coordinate vanishes.  At the last index the zero direction has the
last coordinate as its leading index by convention, and no recursion occurs. -/



variable (D : _root_.MIPStarRE.QPBT.DirectLdParams)





















variable (D : _root_.MIPStarRE.QPBT.DirectLdParams)









/-! ## The diagonal-line branches -/



variable (D : _root_.MIPStarRE.QPBT.DirectLdParams) (S : _root_.MIPStarRE.QPBT.Strategy (_root_.MIPStarRE.QPBT.directLdGame D))
  (hS : S.IsProjective) (r : Fin D.k)

theorem MIPStarRE.QPBT.directCoordinate_diagonal_point_line_le :
    letI := D.toLDTFieldModel
    (_root_.MIPStarRE.QPBT.directCoordinateProjStrat D S hS r).diagonalPointLeftLineRightFailureProbability ≤
      2 * _root_.MIPStarRE.QPBT.directLdBranchRejectionProbability D S (.point, .dline) := by sorry
