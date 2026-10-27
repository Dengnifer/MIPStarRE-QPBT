-- Generated from QPBT/Test/Soundness/Ancilla.lean by skeleton subtraction.
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
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Basic
import Definitions.Def_QPBT_QPBT_State
import Definitions.Def_QPBT_QPBT_Test_MagicSquareTheorems_Rigidity_GroundSlice

namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT
namespace MIPStarRE.QPBT.MagicSquareRigidity
end MIPStarRE.QPBT.MagicSquareRigidity

/-!
# Ancilla isometries for Pauli soundness

Adjoining a unit vector and applying a unitary gives the local isometry in the
final soundness argument. The exact intertwining identity below supplies the
algebraic hypothesis of the range-projection estimates. These results are
recorded in blueprint `thm:pauli-ancilla-intertwining-support`.

## References

Formalization support for blueprint `thm:pauli`, specifically the isometry at
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1864-1875`.
The registers are ordered as `AA'A''`, with the first two factors grouped.
These constructions do not assume or construct a global polynomial measurement.
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.Quantum MagicSquareRigidity

noncomputable section

variable {ι κ ν : Type} [Fintype ι] [DecidableEq ι]
  [Fintype κ] [DecidableEq κ] [Fintype ν] [DecidableEq ν]

/-- Adjoin a unit ancilla on the last two registers, in the extraction order
`(AA')A''`. The norm condition is precisely the normalization of that ancilla. -/
def ancillaBlockIsometry (eta : EuclideanSpace ℂ (κ × ν)) (heta : ‖eta‖ = 1) :
    EuclideanSpace ℂ ι →ₗᵢ[ℂ] EuclideanSpace ℂ ((ι × κ) × ν) where
  toFun psi := _root_.MIPStarRE.QPBT.reindexState (Equiv.prodAssoc ι κ ν).symm (_root_.MIPStarRE.QPBT.vecTensor psi eta)
  map_add' psi chi := by
    ext p
    simp [_root_.MIPStarRE.QPBT.reindexState, _root_.MIPStarRE.QPBT.vecTensor, add_mul]
  map_smul' c psi := by
    ext p
    simp [_root_.MIPStarRE.QPBT.reindexState, _root_.MIPStarRE.QPBT.vecTensor, mul_assoc]
  norm_map' psi := by
    change ‖_root_.MIPStarRE.QPBT.reindexState (Equiv.prodAssoc ι κ ν).symm (_root_.MIPStarRE.QPBT.vecTensor psi eta)‖ = ‖psi‖
    rw [_root_.MIPStarRE.QPBT.reindexState_norm_eq, _root_.MIPStarRE.QPBT.vecTensor_norm_eq, heta, mul_one]





/-- Apply a matrix isometry after adjoining the unit ancilla. In the source
proof the matrix is the swap unitary and the ancilla is the local EPR state. -/
def unitaryAncillaIsometry (eta : EuclideanSpace ℂ (κ × ν)) (heta : ‖eta‖ = 1)
    (U : _root_.LIDT.MIPStarRE.Quantum.Op ((ι × κ) × ν)) (hU : Uᴴ * U = 1) :
    EuclideanSpace ℂ ι →ₗᵢ[ℂ] EuclideanSpace ℂ ((ι × κ) × ν) where
  toLinearMap := (Matrix.toEuclideanLin U).comp
    (_root_.MIPStarRE.QPBT.ancillaBlockIsometry eta heta).toLinearMap
  norm_map' psi := by
    change ‖Matrix.toEuclideanLin U (_root_.MIPStarRE.QPBT.ancillaBlockIsometry eta heta psi)‖ = ‖psi‖
    rw [_root_.MIPStarRE.QPBT.MagicSquareRigidity.norm_toEuclideanLin_of_conjTranspose_mul_eq_one hU, LinearIsometry.norm_map]





end

end MIPStarRE.QPBT
