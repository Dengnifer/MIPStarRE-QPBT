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
import Definitions.Def_QPBT_QPBT_Algebra_PauliTheorems
import Definitions.Def_QPBT_QPBT_Algebra_SelfDualBasisTheorems
import Definitions.Def_QPBT_QPBT_Games_Defs
import Definitions.Def_QPBT_QPBT_State
import Definitions.Def_QPBT_QPBT_Test_PauliBasisTest
import Definitions.Def_QPBT_QPBT_Test_QubitForm
import Definitions.Def_QPBT_QPBT_Test_SoundnessDefs
import Mathlib
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecificLimits.Basic

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT
namespace MIPStarRE.QPBT.BinaryWitnessTransport
end MIPStarRE.QPBT.BinaryWitnessTransport

/-!
# Qubit form of Pauli basis test soundness

The fixed self-dual normal basis converts the qudit EPR register and generalized
Pauli projectors into qubit coordinates. The conversion uses only the basis
stored in the canonical `FixedFieldModel`.

`PauliSoundnessWitness.toQubit` transports supplied existential data, and the
three `qubit_*_to_qubit` identities preserve its comparison quantities exactly.
These are Lean-only transport results, not soundness existence theorems. This
module derives `pauli_soundness_qubit` from `pauli_soundness` using those identities.
`pauli_soundness` itself is now proved, so the corollary is complete: its
axiom closure is `propext`, `Classical.choice` and `Quot.sound`. The
composition that discharged it is recorded in issue Dengnifer/MIPStarRE-QPBT-bak#614, under the
umbrella issue Dengnifer/MIPStarRE-QPBT-bak#529.

## References

The conversion is blueprint
`lem:pauli-binary`, from
`references/qpbt-paper/04_preliminaries.tex:1163-1208`. The resulting
statement is blueprint `cor:pauli-binary`,
from `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1450-1491`.
-/



open scoped BigOperators Matrix

open MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT LIDT.MIPStarRE.Quantum









attribute [instance] _root_.MIPStarRE.QPBT.QubitSoundnessWitness.ιAFintype
  _root_.MIPStarRE.QPBT.QubitSoundnessWitness.ιBFintype _root_.MIPStarRE.QPBT.QubitSoundnessWitness.ιADecidableEq
  _root_.MIPStarRE.QPBT.QubitSoundnessWitness.ιBDecidableEq













open MIPStarRE.QPBT.BinaryWitnessTransport

theorem MIPStarRE.QPBT.qubit_operator_distance_a_to_qubit
    (P : _root_.MIPStarRE.QPBT.AdmissibleParams) (S : _root_.MIPStarRE.QPBT.Strategy (_root_.MIPStarRE.QPBT.pauliBasisTest P))
    (w : _root_.MIPStarRE.QPBT.PauliSoundnessWitness P S) (W : _root_.MIPStarRE.QPBT.PauliKind) :
    _root_.MIPStarRE.QPBT.qubitOperatorDistanceA P S w.toQubit W = _root_.MIPStarRE.QPBT.rawPauliOperatorDistanceA P S w W := by sorry
