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
import Definitions.Def_QPBT_QPBT_Games_Consistency
import Definitions.Def_QPBT_QPBT_Games_Defs
import Definitions.Def_QPBT_QPBT_Games_StrategyClasses
import Definitions.Def_QPBT_QPBT_Palomar_Bridge
import Definitions.Def_QPBT_QPBT_Palomar_Definitions
import Definitions.Def_QPBT_QPBT_Palomar_LowDegreeConsistencyBridge
import Definitions.Def_QPBT_QPBT_Palomar_LowDegreeGameBridge
import Definitions.Def_QPBT_QPBT_Palomar_LowDegreeGameStrategyBridge
import Definitions.Def_QPBT_QPBT_Test_LowDegreeGame
import Definitions.Def_QPBT_QPBT_Test_LowDegreeGameMeasurements
import Mathlib
import Mathlib.Analysis.MeanInequalitiesPow

namespace MIPStarRE.QPBT.Palomar
end MIPStarRE.QPBT.Palomar

/-!
# Compact low-degree soundness

This module transports the registered low-degree soundness theorem to the
compact Palomar game surface, preserving its constants, parameter domain,
quantifier order, and three separate consistency conclusions.

## References

`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:413-440`,
paper `lem:ld-soundness`.
-/



open MIPStarRE.QPBT.Palomar

theorem MIPStarRE.QPBT.Palomar.exists_ld_soundness :
    ∃ a b : ℝ, 1 ≤ a ∧ 0 < b ∧ b ≤ 1 ∧
      ∀ (P : _root_.MIPStarRE.QPBT.Palomar.LowDegreeParams) (ε : ℝ), 0 < ε →
        ∀ S : _root_.MIPStarRE.QPBT.Palomar.LowDegreeStrategy P (_root_.MIPStarRE.QPBT.fixedFieldModel P.q
            P.is_admissible_size).K,
          S.IsProjective →
          1 - ε ≤ S.value (_root_.MIPStarRE.QPBT.Palomar.lowDegreeGame P
            (_root_.MIPStarRE.QPBT.binaryRepresentation
              (_root_.MIPStarRE.QPBT.fixedFieldModel P.q
                P.is_admissible_size))) →
          ∃ GA : _root_.MIPStarRE.QPBT.Palomar.LowDegreePolynomialPOVM P
              (_root_.MIPStarRE.QPBT.fixedFieldModel P.q
                P.is_admissible_size).K S.ιA,
            ∃ GB : _root_.MIPStarRE.QPBT.Palomar.LowDegreePolynomialPOVM P
                (_root_.MIPStarRE.QPBT.fixedFieldModel P.q
                  P.is_admissible_size).K S.ιB,
              _root_.MIPStarRE.QPBT.Palomar.ldPointPolynomialDefect P S GB ≤
                  _root_.MIPStarRE.QPBT.Palomar.deltaLd a b ε P.q P.m P.d P.k ∧
                _root_.MIPStarRE.QPBT.Palomar.ldPolynomialPointDefect P S GA ≤
                  _root_.MIPStarRE.QPBT.Palomar.deltaLd a b ε P.q P.m P.d P.k ∧
                _root_.MIPStarRE.QPBT.Palomar.ldPolynomialPolynomialDefect P S GA GB ≤
                  _root_.MIPStarRE.QPBT.Palomar.deltaLd a b ε P.q P.m P.d P.k := by sorry
