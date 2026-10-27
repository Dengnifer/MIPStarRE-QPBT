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
import Definitions.Def_QPBT_QPBT_Algebra_Lines
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Game
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Geometry
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Transport_Combining_Parameters
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Transport_Combining_Polynomial
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Transport_Combining_QuestionLaw
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Transport_Combining_Strategy
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Transport_Questions
import Definitions.Def_QPBT_QPBT_Test_LowDegreeGame
import Mathlib

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.LDT.Preliminaries
end LIDT.MIPStarRE.LDT.Preliminaries
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT

/-!
# The questions measured by the combined strategy

`lem:ld-combined-question-law` identifies the pair of questions measured by the
combined strategy of `def:ld-combined-strategy` on a sample of the combined
game.  The coordinate index of the common sample is uniform on the `m + k`
coordinates of the combined dimension, and the identification splits according
to whether that index is a point coordinate or a combining coordinate.

On a point coordinate `j`, all three question types measure the canonical
question of the same type of the original game attached to the *projected*
sample `directCombinedSampleProjection`: the point part of the sampled point,
the index `j`, and the point part of the sampled direction.  This uses the
coordinate order of `def:ld-combining-map`: the point coordinates precede the
combining coordinates, so the coordinate direction of a point coordinate has
point part the corresponding coordinate direction, and the prefix projection at
a point coordinate restricts to the prefix projection at that coordinate of the
point part.

On a combining coordinate, every direction produced by the question
distribution has vanishing point part, so all three question types measure the
point question at the point part of the sampled point.

The projected sample is read from the *canonical* base of the combined line,
which need not project to the canonical base of the image line; the two agree
after rebasing along the image direction, which is
`lineRepMap_directCombinedPointPart_lineRepMap`.

## References

* `references/neexp-paper/05_quantum_preliminaries.tex:1409-1503`
* `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:413-458`
* `blueprint/src/chapter/ch13_qpbt_test.tex:473-508`
-/



open scoped BigOperators

open MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT
open LIDT.MIPStarRE.LDT.Preliminaries





/-! ## Coordinates of the combined dimension -/













/-! ## Canonical bases -/







/-! ## The measured questions -/
attribute [local instance] _root_.MIPStarRE.QPBT.directCombinedIndexNonempty

theorem MIPStarRE.QPBT.directCombined_measuredQuestion_of_pointVar (D : _root_.MIPStarRE.QPBT.DirectLdParams)
    (t : _root_.MIPStarRE.QPBT.LdType) (j : Fin D.m) (sample : _root_.MIPStarRE.QPBT.DirectLdSpace D.combined)
    (hindex : sample.index = _root_.MIPStarRE.QPBT.combinedPointVar D.m D.k j) :
    _root_.MIPStarRE.QPBT.directCombinedMeasuredQuestion D (t, _root_.MIPStarRE.QPBT.directLdMap D.combined t sample) =
      (t, _root_.MIPStarRE.QPBT.directLdMap D t (_root_.MIPStarRE.QPBT.directCombinedSampleProjection D j sample)) := by sorry
