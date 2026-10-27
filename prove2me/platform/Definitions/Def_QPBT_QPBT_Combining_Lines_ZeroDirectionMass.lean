-- Generated from QPBT/Combining/Lines/ZeroDirectionMass.lean by skeleton subtraction.
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
import Definitions.Def_QPBT_QPBT_Algebra_FieldBasis
import Definitions.Def_QPBT_QPBT_Algebra_Lines
import Definitions.Def_QPBT_QPBT_Games_CondLinear
import Definitions.Def_QPBT_QPBT_Observables_LineDefs
import Definitions.Def_QPBT_QPBT_Test_LowDegreeGame
import Mathlib

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT

/-!
# Zero-direction mass for axis lines

This module records that the axis-line component of the line-point sampler has
no mass at zero direction.

## References

The sampler is `def:line-point-dist`, from
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:274-287`.
-/

@[expose] public section

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT

noncomputable section

/-- Axis-line sampling gives zero mass to zero directions, since a coordinate
direction is nonzero. This is a formalization-only consequence of
`def:line-point-dist`, paper `08_classical_and_quantum_low_degree_tests.tex:274-287`. -/
theorem aLinePointDist_zero_direction_mass (L : _root_.MIPStarRE.QPBT.LdParams) :
    _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.MIPStarRE.QPBT.aLinePointDist L) (fun sample =>
      if sample.1.direction = 0 then 1 else 0) = 0 := by
  classical
  unfold _root_.MIPStarRE.QPBT.aLinePointDist
  rw [_root_.LIDT.MIPStarRE.LDT.Distribution.avgOver_map]
  have hdir (raw : _root_.MIPStarRE.QPBT.LdSpace L) : (_root_.MIPStarRE.QPBT.aLineDescOf L raw).direction ≠ 0 := by
    intro hzero
    have hcoord := congrFun hzero (_root_.MIPStarRE.QPBT.chiIndex L raw.seed)
    simp [_root_.MIPStarRE.QPBT.aLineDescOf, _root_.MIPStarRE.QPBT.LineDesc.direction, _root_.MIPStarRE.QPBT.coordinateDirection] at hcoord
  simp [_root_.LIDT.MIPStarRE.LDT.avgOver, hdir]

end

end MIPStarRE.QPBT
