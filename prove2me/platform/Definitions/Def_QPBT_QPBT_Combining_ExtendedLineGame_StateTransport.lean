-- Generated from QPBT/Combining/ExtendedLineGame/StateTransport.lean by skeleton subtraction.
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
import Definitions.Def_QPBT_QPBT_Games_Defs
import Definitions.Def_QPBT_QPBT_Observables_Defs
import Definitions.Def_QPBT_QPBT_Observables_ExpandedDefs
import Definitions.Def_QPBT_QPBT_Observables_ExpandedPlacement
import Definitions.Def_QPBT_QPBT_Test_PauliBasisTest
import Mathlib
import Mathlib.Analysis.MeanInequalitiesPow

namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT
namespace MIPStarRE.QPBT.ExtendedLineGame
end MIPStarRE.QPBT.ExtendedLineGame
namespace MIPStarRE.QPBT.ProjectiveSetting
end MIPStarRE.QPBT.ProjectiveSetting

/-!
# Correlations on the two-player expanded state

The six-register state of `eq:def-psihat` factors as the two-player state
`ExtendedLineGame.pairState` and an unused normalized EPR pair, for each of
the opposite register placements `AA'`--`BA''` and `AB''`--`BB'`. Therefore
arbitrary Hermitian operators on the expanded local spaces have the same
correlation in the two descriptions. An individual operator need not factor
between its strategy register and its Pauli register.

These are formalization-only auxiliary identities for the strategy construction
in the proof of `lem:qld-4-7`. They do not establish its passing value or the
existence of its input measurements. Parent issue Dengnifer/MIPStarRE-QPBT-bak#119 remains open.

## References

- `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:367-372`,
  equation `eq:def-psihat`.
- The same source, `lem:qld-4-7`, proof at lines 1279-1288.
- Blueprint `def:expanded-state`, `def:symmetric-equivalents`, and `lem:qld-4-7`.
- Issue Dengnifer/MIPStarRE-QPBT-bak#302.
-/

@[expose] public section

-- The six-register products require the same instance-search size as ExpandedPlacement.
set_option synthInstance.maxSize 400

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.Quantum
open ProjectiveSetting

noncomputable section

namespace ExtendedLineGame

variable {P : _root_.MIPStarRE.QPBT.AdmissibleParams} {epsilon : Real}

/-- Regroup the six registers as `(AA', BA'')` and the unused pair `(B', B'')`.
This is the first opposite-placement partition of `eq:def-psihat`. -/
def aaBaRegrouping (setting : _root_.MIPStarRE.QPBT.ProjectiveSetting P epsilon) :
    _root_.MIPStarRE.QPBT.SixReg P setting.toStrategy.ιA setting.toStrategy.ιB ≃
      (setting.ExpandedLocalSpace .alice × setting.ExpandedLocalSpace .bob) ×
        (_root_.MIPStarRE.QPBT.PauliRegister P × _root_.MIPStarRE.QPBT.PauliRegister P) :=
  (_root_.MIPStarRE.QPBT.ProjectiveSetting.aaBaBipartition P setting.toStrategy.ιA setting.toStrategy.ιB).trans
    (Equiv.prodAssoc _ _ _).symm

/-- Regroup the six registers as `(AB'', BB')` and the unused pair `(A', A'')`.
This is the second opposite-placement partition of `eq:def-psihat`. -/
def abBbRegrouping (setting : _root_.MIPStarRE.QPBT.ProjectiveSetting P epsilon) :
    _root_.MIPStarRE.QPBT.SixReg P setting.toStrategy.ιA setting.toStrategy.ιB ≃
      (setting.ExpandedLocalSpace .alice × setting.ExpandedLocalSpace .bob) ×
        (_root_.MIPStarRE.QPBT.PauliRegister P × _root_.MIPStarRE.QPBT.PauliRegister P) :=
  (_root_.MIPStarRE.QPBT.ProjectiveSetting.abBbBipartition P setting.toStrategy.ιA setting.toStrategy.ιB).trans
    (Equiv.prodAssoc _ _ _).symm









end ExtendedLineGame

end

end MIPStarRE.QPBT
