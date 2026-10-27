-- Generated from QPBT/Combining/Lines/SubLineMixture.lean by skeleton subtraction.
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
import Definitions.Def_QPBT_QPBT_Combining_Lines_SubLineBranch
import Definitions.Def_QPBT_QPBT_Combining_Witnesses
import Definitions.Def_QPBT_QPBT_Games_DistributionAux
import Definitions.Def_QPBT_QPBT_Observables_LineDefs
import Definitions.Def_QPBT_QPBT_Test_PauliBasisTest
import Mathlib
import Mathlib.Analysis.MeanInequalitiesPow

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT

/-!
# The projected mixtures of the sub-line law

This module assembles the two projected point marginals of the sub-line law of
`lem:qld-sublines` into mixtures of the restricted product laws.  Drawing a
uniform point of the extended line of a mixture of line laws is the same
mixture of the corresponding uniform-point laws, so the two projected
marginals of the sub-line law are the mixtures, over the drawn kind and the
drawn extended coordinate, of the projected marginals of one branch at one
extended coordinate.  Each of those is the component law of the pair of
indices carried by that branch, so the mixing law is the law of the kind
together with the pair of indices assigned to a uniform extended coordinate.

## References

The assembly is the last step of the proof of `lem:qld-sublines` in
blueprint `lem:qld-sublines`, whose source is
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`.
The restricted laws are `def:ith-restricted-line`, blueprint lines
1209--1228, paper lines 1038--1048.
-/

@[expose] public section

open scoped BigOperators

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT

noncomputable section

/-! ## The uniform point of a mixture of line laws -/



/-! ## The projected marginals of one branch at one extended coordinate -/







/-! ## The mixing law of the two indices -/

/-- The law of the kind and the pair of source indices assigned to a uniform
extended coordinate of one branch.  Blueprint
`lem:qld-sublines`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`. -/
noncomputable def subLineComponentBranch (P : _root_.MIPStarRE.QPBT.AdmissibleParams)
    (kind : _root_.MIPStarRE.QPBT.LineKind) : _root_.LIDT.MIPStarRE.LDT.Distribution (_root_.MIPStarRE.QPBT.SubLineComponent P) :=
  (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin (2 * P.m + 2))).map fun k =>
    (kind, (_root_.MIPStarRE.QPBT.subLineXIndex P k, _root_.MIPStarRE.QPBT.subLineZIndex P k))

/-- The mixing law of the sub-line lemma: the equal mixture over the two kinds
of the law of the pair of source indices of a uniform extended coordinate.
Blueprint `lem:qld-sublines`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`. -/
noncomputable def subLineComponentDist (P : _root_.MIPStarRE.QPBT.AdmissibleParams) :
    _root_.LIDT.MIPStarRE.LDT.Distribution (_root_.MIPStarRE.QPBT.SubLineComponent P) :=
  _root_.MIPStarRE.QPBT.Distribution.bind (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin 2))
    ![_root_.MIPStarRE.QPBT.subLineComponentBranch P .axis, _root_.MIPStarRE.QPBT.subLineComponentBranch P .diagonal]



/-! ## The two projected marginals of one branch -/





/-! ## The two projected marginals of the sub-line law -/







end

end MIPStarRE.QPBT
