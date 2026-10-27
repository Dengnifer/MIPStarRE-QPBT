-- Generated from QPBT/Combining/Lines/Construction.lean by skeleton subtraction.
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
import Definitions.Def_QPBT_QPBT_Observables_ExpandedDefs
import Definitions.Def_QPBT_QPBT_Test_PauliBasisTest
import Mathlib
import Mathlib.Analysis.MeanInequalitiesPow

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT
namespace MIPStarRE.QPBT.DistanceCalculus
end MIPStarRE.QPBT.DistanceCalculus

/-!
# Construction of consistent combined lines

The heterogeneous pasting theorem bounds the actual X-Z-X measurement.
Polynomial absorption produces a line error for each polynomial point family.

## References

Paper `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:882-963`,
blueprint `lem:qld-xz-lines`. The source and completed-answer distinctions remain
as documented in
`docs/paper-gaps/qpbt_combined-lines-error-term.tex`.
-/

@[expose] public section

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum MIPStarRE.QPBT.DistanceCalculus
open scoped BigOperators Matrix MatrixOrder ComplexOrder

noncomputable section

/-- The fourth directed bipartition, with `BB'` first, `AB''` second, and
the unused `A'A''` pair retained on the second side. This is a coordinate
equivalence, not an identification of the two strategy-player spaces. -/
def bbAbBipartition (params : _root_.MIPStarRE.QPBT.AdmissibleParams) (left right : Type*) :
    _root_.MIPStarRE.QPBT.SixReg params left right ≃
      (right × _root_.MIPStarRE.QPBT.PauliRegister params) ×
        ((left × _root_.MIPStarRE.QPBT.PauliRegister params) × (_root_.MIPStarRE.QPBT.PauliRegister params × _root_.MIPStarRE.QPBT.PauliRegister params)) where
  toFun indices := ((indices.2.1, indices.2.2.1),
    ((indices.1.1, indices.2.2.2), (indices.1.2.1, indices.1.2.2)))
  invFun indices := ((indices.2.1.1, (indices.2.2.1, indices.2.2.2)),
    (indices.1.1, (indices.1.2, indices.2.1.2)))
  left_inv indices := by cases indices; rfl
  right_inv indices := by cases indices; rfl

/-- Coordinates of the `BB' | AB''(A'A'')` bipartition. -/
@[simp] theorem bbAbBipartition_apply (params : _root_.MIPStarRE.QPBT.AdmissibleParams) (left right : Type*)
    (indices : _root_.MIPStarRE.QPBT.SixReg params left right) :
    _root_.MIPStarRE.QPBT.bbAbBipartition params left right indices =
      ((indices.2.1, indices.2.2.1),
        ((indices.1.1, indices.2.2.2), (indices.1.2.1, indices.1.2.2))) := rfl


























end

end MIPStarRE.QPBT
