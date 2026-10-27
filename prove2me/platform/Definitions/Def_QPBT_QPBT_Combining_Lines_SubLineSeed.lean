-- Generated from QPBT/Combining/Lines/SubLineSeed.lean by skeleton subtraction.
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
import Definitions.Def_QPBT_QPBT_Algebra_FieldBasis
import Definitions.Def_QPBT_QPBT_Test_LowDegreeGame
import Mathlib
import Mathlib.Analysis.MeanInequalitiesPow

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT

/-!
# The two independent blocks of a fresh diagonal direction pair

This module splits the fresh diagonal direction pair of the sub-line sampling
procedure into its two independent blocks.  The coordinate-index event
constrains only the scalar seed of the pair, so conditioning on it leaves the
direction block uniform and independent of the conditioned seed.  The
direction block of a fresh pair is therefore available as an unconstrained
uniform vector, which is what allows the sampling procedure to read it off the
corresponding block of the direction of the sampled extended line.

## References

The block decomposition supports `lem:qld-sublines` in
blueprint `lem:qld-sublines`, whose source is
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`.
The coordinate-index event is that of `def:ith-restricted-line`, blueprint
lines 1209--1228, paper lines 1038--1048.
-/

@[expose] public section

open scoped BigOperators

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT

noncomputable section

/-! ## The coordinate-index event on a scalar seed -/

/-- The coordinate-index event of `def:ith-restricted-line` read on a scalar
seed alone.  Blueprint `def:ith-restricted-line`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1038-1048`. -/
def ldSeedIndexEvent (L : _root_.MIPStarRE.QPBT.LdParams) (i : Fin L.m) (s : _root_.MIPStarRE.QPBT.ScalarQ L) : Prop :=
  _root_.MIPStarRE.QPBT.chiIndex L s = i

/-- Decidability of the coordinate-index event on a scalar seed. -/
instance ldSeedIndexEvent_decidablePred (L : _root_.MIPStarRE.QPBT.LdParams) (i : Fin L.m) :
    DecidablePred (_root_.MIPStarRE.QPBT.ldSeedIndexEvent L i) := by
  intro s
  unfold _root_.MIPStarRE.QPBT.ldSeedIndexEvent
  infer_instance

/-- Every coordinate-index event of a scalar seed has positive mass under the
uniform law.  Blueprint `def:ith-restricted-line`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1038-1048`. -/
theorem ldSeedIndexEvent_positive (L : _root_.MIPStarRE.QPBT.LdParams) (i : Fin L.m) :
    0 < ∑ s ∈ (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.MIPStarRE.QPBT.ScalarQ L)).support.filter
        (_root_.MIPStarRE.QPBT.ldSeedIndexEvent L i),
      (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.MIPStarRE.QPBT.ScalarQ L)).weight s := by
  classical
  refine Finset.sum_pos'
    (fun a _ => (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.MIPStarRE.QPBT.ScalarQ L)).nonnegative a)
    ⟨_root_.MIPStarRE.QPBT.seedOfIndexResidue L i ⟨0, L.seedFiberCard_pos⟩,
      Finset.mem_filter.mpr ⟨by simp, ?_⟩, ?_⟩
  · change _root_.MIPStarRE.QPBT.chiIndex L (_root_.MIPStarRE.QPBT.seedOfIndexResidue L i ⟨0, L.seedFiberCard_pos⟩) = i
    exact _root_.MIPStarRE.QPBT.chiIndex_seedOfIndexResidue L i _
  · simp only [_root_.LIDT.MIPStarRE.LDT.uniformDistribution, _root_.LIDT.MIPStarRE.LDT.Distribution.uniformOnFinset_weight,
      Finset.mem_univ, if_true]
    positivity

/-! ## The blocks of a fresh diagonal direction pair -/





end

end MIPStarRE.QPBT
