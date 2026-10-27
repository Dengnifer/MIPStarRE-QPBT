-- Generated from QPBT/Combining/DirectLowDegree/Transport/SeedFiberValue.lean by skeleton subtraction.
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
import Definitions.Def_QPBT_QPBT_Games_Defs
import Definitions.Def_QPBT_QPBT_Test_LowDegreeGame
import Mathlib

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT

/-!
# Value of the seed-fiber dilation

The correlated seed-fiber dilation `ldStrategyToDirect` reads a strategy for
the seed-indexed low-degree game as a strategy for the directly indexed game.
This module shows that the dilation preserves the value exactly.

The direct game asks the canonical questions of a common direct sample.  In
each residue block the dilated strategy asks the original strategy the seeded
canonical questions of that sample; since canonicalizing a canonical sample
changes nothing, these are the seed-indexed questions of the common sample
carrying that residue.  The Born weight of the dilation is the uniform average
of the original Born weights over the residue, the predicates agree after
parsing, and the seed-indexed sample is a direct sample together with a
uniform residue, so the two averages coincide branch by branch, including the
point/point, line/line, and wrong-form clauses and the zero-direction
convention.

## References

- `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:214-458`
- Blueprint `def:ld-question-distribution`, `lem:ld-aline-level`,
  `lem:ld-dline-level`, `lem:ld-question-typed-cl`, `lem:alnf`, and `lem:dlnf`
- `docs/paper-gaps/qpbt_ld-dimension-divisibility.tex`
-/

@[expose] public section

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT
open LIDT.MIPStarRE.Quantum

noncomputable section



/-- Accepted Born mass at a fixed pair of seed-indexed questions. -/
 def ldAcceptedMass (L : _root_.MIPStarRE.QPBT.LdParams) (S : _root_.MIPStarRE.QPBT.Strategy (_root_.MIPStarRE.QPBT.ldGame L))
    (x y : _root_.MIPStarRE.QPBT.LdQuestion L) : ℝ :=
  ∑ a : _root_.MIPStarRE.QPBT.LdAnswer L, ∑ b : _root_.MIPStarRE.QPBT.LdAnswer L,
    if _root_.MIPStarRE.QPBT.ldWinPredicate L x y a b then _root_.MIPStarRE.QPBT.outcomeWeight S x y a b else 0

/-- Accepted Born mass at a fixed pair of direct questions. -/
 def directAcceptedMass (D : _root_.MIPStarRE.QPBT.DirectLdParams) (S : _root_.MIPStarRE.QPBT.Strategy (_root_.MIPStarRE.QPBT.directLdGame D))
    (x y : _root_.MIPStarRE.QPBT.DirectLdQuestion D) : ℝ :=
  ∑ a : _root_.MIPStarRE.QPBT.DirectLdAnswer D, ∑ b : _root_.MIPStarRE.QPBT.DirectLdAnswer D,
    if _root_.MIPStarRE.QPBT.directLdWinPredicate D x y a b then _root_.MIPStarRE.QPBT.outcomeWeight S x y a b else 0





end

end MIPStarRE.QPBT
