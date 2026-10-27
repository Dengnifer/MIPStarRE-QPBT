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
import Definitions.Def_QPBT_QPBT_Games_StrategyClasses
import Definitions.Def_QPBT_QPBT_Palomar_Bridge
import Definitions.Def_QPBT_QPBT_Palomar_Definitions
import Definitions.Def_QPBT_QPBT_Palomar_LowDegreeGameStrategyBridge
import Definitions.Def_QPBT_QPBT_Palomar_PauliExtractionBridge
import Definitions.Def_QPBT_QPBT_Palomar_PauliGameBridge
import Definitions.Def_QPBT_QPBT_Palomar_PauliGameStrategyBridge
import Definitions.Def_QPBT_QPBT_Test_Completeness
import Definitions.Def_QPBT_QPBT_Test_PauliBasisTest
import Mathlib
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecificLimits.Basic

namespace MIPStarRE.QPBT.Palomar
end MIPStarRE.QPBT.Palomar

/-!
# Compact Pauli basis test completeness

This module transports the registered value-one SPCC strategy to the compact
Palomar game.  Its public statement uses the concrete Pauli SPCC predicate and
the once-and-for-all field model, while symmetric-game and relabeling objects
occur only in the proof.

## References

`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1229-1421`,
paper `lem:pauli-completeness`.
-/



open MIPStarRE.QPBT.Palomar

theorem MIPStarRE.QPBT.Palomar.exists_spcc_value_one (P : _root_.MIPStarRE.QPBT.Palomar.PauliParams) :
    ∃ S : _root_.MIPStarRE.QPBT.Palomar.SymmetricPauliStrategy P
        (_root_.MIPStarRE.QPBT.fixedFieldModel P.q P.is_admissible_size).K,
      S.IsPauliSPCC P
          (_root_.MIPStarRE.QPBT.binaryRepresentation
            (_root_.MIPStarRE.QPBT.fixedFieldModel P.q P.is_admissible_size)) ∧
      S.toStrategy.value
          (_root_.MIPStarRE.QPBT.Palomar.pauliGame P
            (_root_.MIPStarRE.QPBT.binaryRepresentation
              (_root_.MIPStarRE.QPBT.fixedFieldModel P.q P.is_admissible_size))
            (_root_.MIPStarRE.QPBT.fixedBinTrace
              (_root_.MIPStarRE.QPBT.fixedFieldModel P.q P.is_admissible_size))) = 1 := by sorry
