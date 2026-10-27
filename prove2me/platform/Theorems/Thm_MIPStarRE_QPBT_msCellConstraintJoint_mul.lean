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
import Definitions.Def_LIDT_MIPStarRE_Quantum_Measurement
import Definitions.Def_QPBT_QPBT_Algebra_Pauli
import Definitions.Def_QPBT_QPBT_Games_Defs
import Definitions.Def_QPBT_QPBT_Test_MagicSquare
import Definitions.Def_QPBT_QPBT_Test_MagicSquareTheorems_PerfectStrategy_Measurements
import Definitions.Def_QPBT_QPBT_Test_MagicSquareTheorems_PerfectStrategy_Observables

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT

/-!
# Measurements of the perfect Magic Square strategy

This module turns the operator table of `thm:ms-from-ac` into a measurement
family.  It forms the joint measurement of two commuting binary projective
measurements, records the post-processing identities for injective
relabellings, encodes a constraint answer as the parity triple determined by
two freely chosen bits, and assembles the nine cell measurements into the
Magic Square measurement family, closing with the multiplication rule relating
a constraint outcome to the outcomes of its incident variables.

## References

The source statement is blueprint
`thm:ms-from-ac`, from
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:654-722`.
-/



open scoped BigOperators Matrix MatrixOrder ComplexOrder

open MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum

theorem MIPStarRE.QPBT.msCellConstraintJoint_mul
    {V : Type*} [Fintype V] [DecidableEq V]
    (OA OB : _root_.LIDT.MIPStarRE.Quantum.Op V) (hOA : OAᴴ = OA) (hOB : OBᴴ = OB)
    (hOA_sq : OA * OA = 1) (hOB_sq : OB * OB = 1)
    (hac : OA * OB = -(OB * OA))
    (i : Fin 6) (k : Fin 3) (ab : ZMod 2 × ZMod 2) (b : ZMod 2) :
    let P := _root_.MIPStarRE.QPBT.msCellMeasurement OA OB hOA hOB hOA_sq hOB_sq hac
    (_root_.MIPStarRE.QPBT.msConstraintJoint P
        (_root_.MIPStarRE.QPBT.msCellMeasurement_projective OA OB hOA hOB hOA_sq hOB_sq hac)
        (fun i k l a b => _root_.MIPStarRE.QPBT.reflectionEffect_commute
          (_root_.MIPStarRE.QPBT.msConstraintObservable_commute OA OB hOA_sq hOB_sq hac i k l) a b)
        i).effect ab * (P (_root_.MIPStarRE.QPBT.msConstraintVars i k)).effect b =
      if _root_.MIPStarRE.QPBT.parityTriple i ab k = b then
        (_root_.MIPStarRE.QPBT.msConstraintJoint P
          (_root_.MIPStarRE.QPBT.msCellMeasurement_projective OA OB hOA hOB hOA_sq hOB_sq hac)
          (fun i k l a b => _root_.MIPStarRE.QPBT.reflectionEffect_commute
            (_root_.MIPStarRE.QPBT.msConstraintObservable_commute OA OB hOA_sq hOB_sq hac i k l) a b)
          i).effect ab else 0 := by sorry
