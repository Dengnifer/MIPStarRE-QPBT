-- Generated from QPBT/Combining/DirectLowDegree/Transport/Consistency/Compression.lean by skeleton subtraction.
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
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Game
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Geometry
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Transport_Correspondence
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Transport_SeedFiber
import Definitions.Def_QPBT_QPBT_Test_LowDegreeGame
import Definitions.Def_QPBT_QPBT_Test_LowDegreeGameMeasurements
import Mathlib

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.LDT.Preliminaries
end LIDT.MIPStarRE.LDT.Preliminaries
namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT

/-!
# Correlated-ancilla consistency compression

This module contains the correlated-state identities and the two valid
seed-fiber consistency-defect compression results.

## References

- `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:393-458`
- `references/ldt-paper/test_definition.tex:180-202`
- `docs/paper-gaps/qpbt_ld-dimension-divisibility.tex`
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT
open LIDT.MIPStarRE.LDT.Preliminaries
open LIDT.MIPStarRE.Quantum

noncomputable section

/-! ## Seed-fiber identities -/

/-- Reconstructing a seed-indexed point question in any residue block gives
the original point question. -/
@[simp] theorem seededLdQuestion_directLdPointQuestionOf
    (L : _root_.MIPStarRE.QPBT.LdParams) (u : Fin L.m → _root_.MIPStarRE.QPBT.ScalarQ L)
    (residue : Fin (L.q / L.m)) :
    _root_.MIPStarRE.QPBT.seededLdQuestion L
        (_root_.MIPStarRE.QPBT.directLdPointQuestionOf L.toDirectLdParams u) residue =
      _root_.MIPStarRE.QPBT.ldPointQuestionOf L u :=
  rfl

/-- The direct point-answer readout agrees with the seed-indexed readout: the
answer equivalence preserves point answers. -/
@[simp] theorem ldPointValuesOrZero_ldDirectAnswerEquiv_symm
    (L : _root_.MIPStarRE.QPBT.LdParams) (a : _root_.MIPStarRE.QPBT.DirectLdAnswer L.toDirectLdParams) :
    _root_.MIPStarRE.QPBT.ldPointValuesOrZero L ((_root_.MIPStarRE.QPBT.ldDirectAnswerEquiv L).symm a) =
      _root_.MIPStarRE.QPBT.directLdPointValuesOrZero L.toDirectLdParams a := by
  cases a <;> rfl























end

end MIPStarRE.QPBT
