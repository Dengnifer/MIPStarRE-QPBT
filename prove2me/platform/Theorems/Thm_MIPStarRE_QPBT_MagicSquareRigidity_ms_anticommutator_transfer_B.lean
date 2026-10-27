import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_AxisParallelLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DiagonalLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_Distribution
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
import Definitions.Def_LIDT_MIPStarRE_Quantum_Measurement
import Definitions.Def_QPBT_QPBT_Games_CondLinear
import Definitions.Def_QPBT_QPBT_Games_Consistency
import Definitions.Def_QPBT_QPBT_Games_Defs
import Definitions.Def_QPBT_QPBT_Games_Distance
import Definitions.Def_QPBT_QPBT_State
import Definitions.Def_QPBT_QPBT_Test_MagicSquare
import Definitions.Def_QPBT_QPBT_Test_MagicSquareTheorems_Basic
import Definitions.Def_QPBT_QPBT_Test_MagicSquareTheorems_Rigidity_AnticommutatorB
import Definitions.Def_QPBT_QPBT_Test_MagicSquareTheorems_Rigidity_Dilation
import Definitions.Def_QPBT_QPBT_Test_MagicSquareTheorems_Rigidity_GroundSlice
import Definitions.Def_QPBT_QPBT_Test_MagicSquareTheorems_Rigidity_Relations
import Definitions.Def_QPBT_QPBT_Test_MagicSquareTheorems_Rigidity_Transfer

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
namespace MIPStarRE.QPBT.DistanceCalculus
end MIPStarRE.QPBT.DistanceCalculus
namespace MIPStarRE.QPBT.MagicSquareRigidity
end MIPStarRE.QPBT.MagicSquareRigidity

/-!
# Transfer of Bob's anticommutator estimate along the projective dilation

The right-placed counterpart of the Alice-side anticommutator transfer in
`Rigidity/Transfer.lean`: Bob's dilated observables leak out of the ground
slice by at most the forward cell-consistency defects, and the product of the
compressed observables is compared with the product of the dilated ones on the
dilated state through Alice's partner observable.

## References

blueprint `thm:ms-rigidity`,
paper `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:612-652`.
-/



open scoped BigOperators Matrix MatrixOrder ComplexOrder

open MIPStarRE.QPBT.MagicSquareRigidity

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum MIPStarRE.QPBT.DistanceCalculus

theorem MIPStarRE.QPBT.MagicSquareRigidity.ms_anticommutator_transfer_B {κA κB : Type} [Fintype κA] [DecidableEq κA]
    [Fintype κB] [DecidableEq κB] (S : _root_.MIPStarRE.QPBT.Strategy _root_.MIPStarRE.QPBT.msGame)
    (φA : EuclideanSpace ℂ (S.ιA × Option _root_.MIPStarRE.QPBT.MsAnswer) →ₗᵢ[ℂ] EuclideanSpace ℂ κA)
    (φB : EuclideanSpace ℂ (S.ιB × Option _root_.MIPStarRE.QPBT.MsAnswer) →ₗᵢ[ℂ] EuclideanSpace ℂ κB)
    (ξ : EuclideanSpace ℂ (κA × κB)) (ε η : ℝ)
    (hwin : 1 - ε ≤ S.value)
    (hξ : ‖_root_.MIPStarRE.QPBT.isometryTensor φA φB (_root_.MIPStarRE.QPBT.MagicSquareRigidity.msDilatedStrategy S).ψ - ξ‖ ≤ η) :
    _root_.MIPStarRE.QPBT.opDistSq (_root_.LIDT.MIPStarRE.LDT.uniformDistribution Unit)
        (fun _ => _root_.MIPStarRE.QPBT.heteroKron 1 (_root_.MIPStarRE.QPBT.conjIsometry (φB.comp (_root_.MIPStarRE.QPBT.MagicSquareRigidity.naimarkEmbedding S.ιB _root_.MIPStarRE.QPBT.MsAnswer))
            (_root_.MIPStarRE.QPBT.obsOf ((S.B (.var 0)).postprocess _root_.MIPStarRE.QPBT.msBitOrZero))) *
          _root_.MIPStarRE.QPBT.heteroKron 1 (_root_.MIPStarRE.QPBT.conjIsometry (φB.comp (_root_.MIPStarRE.QPBT.MagicSquareRigidity.naimarkEmbedding S.ιB _root_.MIPStarRE.QPBT.MsAnswer))
            (_root_.MIPStarRE.QPBT.obsOf ((S.B (.var 4)).postprocess _root_.MIPStarRE.QPBT.msBitOrZero))))
        (fun _ => -(_root_.MIPStarRE.QPBT.heteroKron 1 (_root_.MIPStarRE.QPBT.conjIsometry (φB.comp (_root_.MIPStarRE.QPBT.MagicSquareRigidity.naimarkEmbedding S.ιB _root_.MIPStarRE.QPBT.MsAnswer))
            (_root_.MIPStarRE.QPBT.obsOf ((S.B (.var 4)).postprocess _root_.MIPStarRE.QPBT.msBitOrZero))) *
          _root_.MIPStarRE.QPBT.heteroKron 1 (_root_.MIPStarRE.QPBT.conjIsometry (φB.comp (_root_.MIPStarRE.QPBT.MagicSquareRigidity.naimarkEmbedding S.ιB _root_.MIPStarRE.QPBT.MsAnswer))
            (_root_.MIPStarRE.QPBT.obsOf ((S.B (.var 0)).postprocess _root_.MIPStarRE.QPBT.msBitOrZero))))) ξ ≤
      3 * _root_.MIPStarRE.QPBT.opDistSq (_root_.LIDT.MIPStarRE.LDT.uniformDistribution Unit)
        (fun _ => _root_.MIPStarRE.QPBT.heteroKron 1 (_root_.MIPStarRE.QPBT.conjIsometry φB
            (_root_.MIPStarRE.QPBT.obsOf (((_root_.MIPStarRE.QPBT.MagicSquareRigidity.msDilatedStrategy S).B (.var 0)).postprocess _root_.MIPStarRE.QPBT.msBitOrZero))) *
          _root_.MIPStarRE.QPBT.heteroKron 1 (_root_.MIPStarRE.QPBT.conjIsometry φB
            (_root_.MIPStarRE.QPBT.obsOf (((_root_.MIPStarRE.QPBT.MagicSquareRigidity.msDilatedStrategy S).B (.var 4)).postprocess _root_.MIPStarRE.QPBT.msBitOrZero))))
        (fun _ => -(_root_.MIPStarRE.QPBT.heteroKron 1 (_root_.MIPStarRE.QPBT.conjIsometry φB
            (_root_.MIPStarRE.QPBT.obsOf (((_root_.MIPStarRE.QPBT.MagicSquareRigidity.msDilatedStrategy S).B (.var 4)).postprocess _root_.MIPStarRE.QPBT.msBitOrZero))) *
          _root_.MIPStarRE.QPBT.heteroKron 1 (_root_.MIPStarRE.QPBT.conjIsometry φB
            (_root_.MIPStarRE.QPBT.obsOf (((_root_.MIPStarRE.QPBT.MagicSquareRigidity.msDilatedStrategy S).B (.var 0)).postprocess _root_.MIPStarRE.QPBT.msBitOrZero))))) ξ +
      15552 * ε + 48 * η ^ 2 := by sorry
