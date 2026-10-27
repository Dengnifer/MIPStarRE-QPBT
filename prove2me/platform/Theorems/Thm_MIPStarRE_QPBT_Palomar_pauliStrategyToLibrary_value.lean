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
import Definitions.Def_QPBT_QPBT_Palomar_Bridge
import Definitions.Def_QPBT_QPBT_Palomar_Definitions
import Definitions.Def_QPBT_QPBT_Palomar_LowDegreeGameStrategyBridge
import Definitions.Def_QPBT_QPBT_Palomar_PauliGameBridge
import Definitions.Def_QPBT_QPBT_Palomar_PauliGameStrategyBridge
import Definitions.Def_QPBT_QPBT_Test_PauliBasisTest
import Mathlib

namespace MIPStarRE.QPBT.Palomar
end MIPStarRE.QPBT.Palomar
namespace MIPStarRE.QPBT.Palomar.Game
end MIPStarRE.QPBT.Palomar.Game
namespace MIPStarRE.QPBT.Palomar.PMF
end MIPStarRE.QPBT.Palomar.PMF
namespace MIPStarRE.QPBT.Palomar.POVM
end MIPStarRE.QPBT.Palomar.POVM
namespace MIPStarRE.QPBT.Palomar.SymmetricGame
end MIPStarRE.QPBT.Palomar.SymmetricGame
namespace MIPStarRE.QPBT.Palomar.SymmetricStrategy
end MIPStarRE.QPBT.Palomar.SymmetricStrategy

/-!
# Strategy bridge for the compact Pauli basis game

This module transports compact strategies across the exact question and answer
equivalences of `PauliGameBridge`.  It preserves the game, Born value,
projectivity, symmetry, consistency, positive-support commutation, and the SPCC
predicate exactly.

## References

`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1126-1491`.
-/



open MIPStarRE.QPBT.Palomar





open MIPStarRE.QPBT.Palomar.PMF







open MIPStarRE.QPBT.Palomar.POVM







open MIPStarRE.QPBT.Palomar.Game





open MIPStarRE.QPBT.Palomar.SymmetricGame





open MIPStarRE.QPBT.Palomar.SymmetricStrategy
attribute [local instance] _root_.MIPStarRE.QPBT.Palomar.compactPauliQuestionDecidableEq

theorem MIPStarRE.QPBT.Palomar.pauliStrategyToLibrary_value (P : _root_.MIPStarRE.QPBT.AdmissibleParams)
    (S : _root_.MIPStarRE.QPBT.Palomar.Strategy
      (_root_.MIPStarRE.QPBT.Palomar.PauliQuestion (_root_.MIPStarRE.QPBT.Palomar.PauliParams.ofAdmissibleParams P) (_root_.MIPStarRE.QPBT.PauliScalar P))
      (_root_.MIPStarRE.QPBT.Palomar.PauliQuestion (_root_.MIPStarRE.QPBT.Palomar.PauliParams.ofAdmissibleParams P) (_root_.MIPStarRE.QPBT.PauliScalar P))
      (_root_.MIPStarRE.QPBT.Palomar.PauliAnswer (_root_.MIPStarRE.QPBT.Palomar.PauliParams.ofAdmissibleParams P) (_root_.MIPStarRE.QPBT.PauliScalar P))
      (_root_.MIPStarRE.QPBT.Palomar.PauliAnswer (_root_.MIPStarRE.QPBT.Palomar.PauliParams.ofAdmissibleParams P) (_root_.MIPStarRE.QPBT.PauliScalar P))) :
    (_root_.MIPStarRE.QPBT.Palomar.pauliStrategyToLibrary P S).value =
      S.value (_root_.MIPStarRE.QPBT.Palomar.pauliGame (_root_.MIPStarRE.QPBT.Palomar.PauliParams.ofAdmissibleParams P)
        (_root_.MIPStarRE.QPBT.binaryRepresentation P.model)
        (_root_.MIPStarRE.QPBT.fixedBinTrace P.model)) := by sorry
