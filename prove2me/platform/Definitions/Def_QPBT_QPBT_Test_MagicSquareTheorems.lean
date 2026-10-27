-- Generated from QPBT/Test/MagicSquareTheorems.lean by skeleton subtraction.
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
import Definitions.Def_QPBT_QPBT_Test_MagicSquare

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT
namespace MIPStarRE.QPBT.MagicSquareRigidity
end MIPStarRE.QPBT.MagicSquareRigidity

/-!
# Magic Square rigidity

This stable public facade re-exports the elementary symmetry facts, the
value-to-parity relation layer, and the perfect strategy construction while
retaining the rigidity theorem and its supporting definitions.

The rigidity theorem is stated in the corrected form adopted on issue
Dengnifer/MIPStarRE-QPBT-bak#172: the
source quantifies over all strategies, which is false for the role-symmetric
game (`docs/paper-gaps/qpbt_ms-rigidity-symmetric-strategies.tex`), and the
corrected statement assumes that the two players' `Variable_1` and `Variable_5`
measurements agree between the players up to `δ` in the squared
state-dependent distance of `def:povm-distance`
(`msVariableConsistencyDefect`, in `Rigidity/Consistency.lean`).  Symmetric
consistent strategies in the sense of `def:consistent-strategy`, which are
projective, and in particular the SPCC strategies of `def:spcc`, satisfy the
hypothesis with `δ = 0` (`exists_ms_rigidity_of_symmetric_consistent`).

## References

The source statement is blueprint
`thm:ms-rigidity`, from
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:612-652`.

The variable indices below are zero-based: indices 0 and 4 represent the
paper's first and fifth variables, respectively.
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT LIDT.MIPStarRE.Quantum MagicSquareRigidity

noncomputable section





/-- The isometries and auxiliary unit state in the conclusion of
`thm:ms-rigidity`. -/
structure MsRigidityWitness (S : _root_.MIPStarRE.QPBT.Strategy _root_.MIPStarRE.QPBT.msGame) where
  ιA'' : Type
  ιB'' : Type
  [ιA''Fintype : Fintype ιA'']
  [ιB''Fintype : Fintype ιB'']
  [ιA''DecidableEq : DecidableEq ιA'']
  [ιB''DecidableEq : DecidableEq ιB'']
  φA : EuclideanSpace ℂ S.ιA →ₗᵢ[ℂ]
    EuclideanSpace ℂ ((Fin 2 → ZMod 2) × ιA'')
  φB : EuclideanSpace ℂ S.ιB →ₗᵢ[ℂ]
    EuclideanSpace ℂ ((Fin 2 → ZMod 2) × ιB'')
  aux : EuclideanSpace ℂ (ιA'' × ιB'')
  aux_norm : ‖aux‖ = 1

attribute [instance] _root_.MIPStarRE.QPBT.MsRigidityWitness.ιA''Fintype
  _root_.MIPStarRE.QPBT.MsRigidityWitness.ιB''Fintype _root_.MIPStarRE.QPBT.MsRigidityWitness.ιA''DecidableEq
  _root_.MIPStarRE.QPBT.MsRigidityWitness.ιB''DecidableEq









/-! ## The coarse witness and the large-error regime -/





/-! ## The bit-measurement and anticommutator estimates on the dilation -/

















end

end MIPStarRE.QPBT
