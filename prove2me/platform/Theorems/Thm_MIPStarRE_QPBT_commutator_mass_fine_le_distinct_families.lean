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
import Definitions.Def_QPBT_QPBT_Games_Defs
import Definitions.Def_QPBT_QPBT_Games_Distance
import Definitions.Def_QPBT_QPBT_Games_DistanceTheorems_Support
import Definitions.Def_QPBT_QPBT_Games_Sandwich_Support

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT
namespace MIPStarRE.QPBT.DistanceCalculus
end MIPStarRE.QPBT.DistanceCalculus

/-! # Ordered product masses and the assembly of the pasting estimate

This module records the mass estimates of step 3 of the proof of the adopted
statement of `lem:pasting`, the fine commutator mass of step 5, the assembly of
those estimates into the explicit bound on the defect of the pasted family, the
bound of one on the defect of an arbitrary pair of placed families, and the
scalar comparison of the assembled bound with the error function of the
theorem.  The proof of the adopted statement is recorded in
`docs/paper-gaps/qpbt_pasting-product-error.tex`.

## References

Blueprint `ch12_qpbt_games.tex:960-990`, paper origin
`references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:504-525`.
-/



open scoped BigOperators MatrixOrder Matrix ComplexOrder

open MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum
open MIPStarRE.QPBT.DistanceCalculus

theorem MIPStarRE.QPBT.commutator_mass_fine_le_distinct_families {X Y₁ Y₂ R₁ R₂ Γ₂ ι : Type*}
    [Fintype X] [DecidableEq X] [Fintype Y₁] [DecidableEq Y₁]
    [Fintype Y₂] [DecidableEq Y₂] [Fintype R₁] [DecidableEq R₁]
    [Fintype R₂] [DecidableEq R₂] [Fintype Γ₂] [DecidableEq Γ₂]
    [Fintype ι] [DecidableEq ι]
    (D : _root_.LIDT.MIPStarRE.LDT.Distribution ((X × Y₁) × Y₂)) (eval₂ : Γ₂ → Y₂ → R₂)
    (G₂ opposite : X → _root_.LIDT.MIPStarRE.Quantum.Measurement Γ₂ ι) (P : (X × Y₁) → _root_.LIDT.MIPStarRE.Quantum.Measurement R₁ ι)
    (ψ : EuclideanSpace ℂ (ι × ι)) (η K₀ m εc εf : ℝ)
    (hD : D.IsProbability) (hψ : ‖ψ‖ = 1) (hη : 0 ≤ η)
    (hG₂ : ∀ x, _root_.MIPStarRE.QPBT.Measurement.IsProjective (G₂ x))
    (hcoll : ∀ x y₁, 0 < (D.map Prod.fst).weight (x, y₁) →
      ∀ g g' : Γ₂, g ≠ g' →
        (∑ y₂ : Y₂, D.weight ((x, y₁), y₂) *
          if eval₂ g y₂ = eval₂ g' y₂ then 1 else 0) ≤
          η * (D.map Prod.fst).weight (x, y₁))
    (hK₀ : _root_.MIPStarRE.QPBT.opFamilyDistSq D (fun q (ab : R₁ × R₂) => _root_.MIPStarRE.QPBT.heteroKron 1
      ((P q.1).effect ab.1 * ((G₂ q.1.1).postprocess
          (fun g => eval₂ g q.2)).effect ab.2 -
        ((G₂ q.1.1).postprocess (fun g => eval₂ g q.2)).effect ab.2 *
          (P q.1).effect ab.1)) (fun _ _ => 0) ψ ≤ K₀)
    (hmass : 1 - m ≤ _root_.LIDT.MIPStarRE.LDT.avgOver D (fun q => ∑ ab : R₁ × R₂,
      ‖_root_.MIPStarRE.QPBT.applyOperatorToState (_root_.MIPStarRE.QPBT.heteroKron 1 ((P q.1).effect ab.1 *
        ((G₂ q.1.1).postprocess (fun g => eval₂ g q.2)).effect ab.2)) ψ‖ ^ 2))
    (hglc : _root_.MIPStarRE.QPBT.opFamilyDistSq D
      (fun q b => _root_.MIPStarRE.QPBT.heteroKron 1 (((G₂ q.1.1).postprocess
        (fun g => eval₂ g q.2)).effect b))
      (fun q b => _root_.MIPStarRE.QPBT.heteroKron (((opposite q.1.1).postprocess
        (fun g => eval₂ g q.2)).effect b) 1) ψ ≤ εc)
    (hglf : _root_.MIPStarRE.QPBT.opFamilyDistSq D (fun q g => _root_.MIPStarRE.QPBT.heteroKron 1 ((G₂ q.1.1).effect g))
      (fun q g => _root_.MIPStarRE.QPBT.heteroKron ((opposite q.1.1).effect g) 1) ψ ≤ εf) :
    _root_.LIDT.MIPStarRE.LDT.avgOver D (fun q => ∑ a : R₁, ∑ g : Γ₂, ‖_root_.MIPStarRE.QPBT.applyOperatorToState
        (_root_.MIPStarRE.QPBT.heteroKron 1 ((P q.1).effect a * (G₂ q.1.1).effect g -
          (G₂ q.1.1).effect g * (P q.1).effect a)) ψ‖ ^ 2) ≤
      K₀ + m + 2 * η + 2 * Real.sqrt εf + 2 * Real.sqrt εc := by sorry
