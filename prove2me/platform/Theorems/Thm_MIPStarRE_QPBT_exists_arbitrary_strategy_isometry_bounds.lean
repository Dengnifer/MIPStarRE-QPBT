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
import Definitions.Def_QPBT_QPBT_Algebra_LowDegreeCode
import Definitions.Def_QPBT_QPBT_Algebra_Pauli
import Definitions.Def_QPBT_QPBT_Combining_Witnesses
import Definitions.Def_QPBT_QPBT_ExplicitConstants
import Definitions.Def_QPBT_QPBT_Extraction_Defs
import Definitions.Def_QPBT_QPBT_Extraction_Unitary
import Definitions.Def_QPBT_QPBT_Games_Defs
import Definitions.Def_QPBT_QPBT_Games_StrategyClasses
import Definitions.Def_QPBT_QPBT_Observables_Defs
import Definitions.Def_QPBT_QPBT_State
import Definitions.Def_QPBT_QPBT_Test_MagicSquareTheorems_Rigidity_Dilation
import Definitions.Def_QPBT_QPBT_Test_PauliBasisTest
import Definitions.Def_QPBT_QPBT_Test_SoundnessDefs
import Definitions.Def_QPBT_QPBT_Test_Soundness_NaimarkReduction
import Mathlib
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecificLimits.Basic

namespace MIPStarRE.QPBT
end MIPStarRE.QPBT

/-!
# Pauli isometry bounds for arbitrary strategies

The projective-setting isometry bounds are composed with the questionwise
Naimark dilation.  An arbitrary Pauli-test strategy winning with probability at
least `1 - ε` dilates to a projective setting at the same error, the projective
bounds apply there, and the resulting witness is pulled back to the original
spaces.  The state comparison transfers as an equality; both operator families
transfer with the dilation constants of `pauli_naimark_operator_distanceA_le`,
which the enlarged universal prefactor absorbs.  The error domain is still
restricted to `[0, 1]`.

## References

This is a formalization-only support result for blueprint `thm:pauli`, whose
source statement is at
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1426-1447`.
The source performs the projective reduction in one sentence at
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:160-190`, and the
isometry passage is at
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1862-1876`.
Blueprint `thm:pauli-arbitrary-strategy-isometry-support`; issue Dengnifer/MIPStarRE-QPBT-bak#614.
-/



open MIPStarRE.QPBT

theorem MIPStarRE.QPBT.exists_arbitrary_strategy_isometry_bounds :
    ∃ a b : ℝ, 1 ≤ a ∧ 0 < b ∧ b < 1 ∧
      ∀ (P : _root_.MIPStarRE.QPBT.AdmissibleParams) (ε : ℝ), 0 ≤ ε → ε ≤ 1 →
        ∀ S : _root_.MIPStarRE.QPBT.Strategy (_root_.MIPStarRE.QPBT.pauliBasisTest P), 1 - ε ≤ S.value →
          ∃ w : _root_.MIPStarRE.QPBT.PauliSoundnessWitness P S,
            ‖_root_.MIPStarRE.QPBT.isometryTensor w.φA w.φB S.ψ - _root_.MIPStarRE.QPBT.idealState P w.aux‖ ≤
                _root_.MIPStarRE.QPBT.deltaQld a b ε P.m P.d P.q ∧
            (∀ W : _root_.MIPStarRE.QPBT.PauliKind,
              _root_.MIPStarRE.QPBT.pauliOperatorDistanceA P S w W ≤ _root_.MIPStarRE.QPBT.deltaQld a b ε P.m P.d P.q) ∧
            (∀ W : _root_.MIPStarRE.QPBT.PauliKind,
              _root_.MIPStarRE.QPBT.pauliOperatorDistanceB P S w W ≤ _root_.MIPStarRE.QPBT.deltaQld a b ε P.m P.d P.q) := by sorry
