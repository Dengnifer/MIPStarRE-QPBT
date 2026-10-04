# Source statements and formal conventions

The primary source is [MIP*=RE, arXiv:2001.04383v3](https://arxiv.org/abs/2001.04383v3).
The comparator-configured statements correspond to Theorem 7.8, Lemma 7.13,
Theorem 7.14, and Corollary 7.15. The Lean statements retain explicit error functions and the
admissibility conditions on the parameters. They concern finite-dimensional
strategies; this library does not formalize the whole MIP*=RE theorem.

## Degenerate lines

Figure 3 writes the line/point acceptance condition using an affine parameter
`t` satisfying `x = u₀ + t v`. This parameter is unique when `v ≠ 0`, but is
not specified when `v = 0`. The formal predicate requires the equality of
answers for every parameter satisfying that equation. Thus, on a zero-direction
line, the answer polynomial must be the constant function with the point's
value. This is a completion of the degenerate case, not a claim that Figure 3
explicitly states this convention. See
[`dlinePointCondition`](QPBT/Test/LowDegreeGame.lean) and the
[compact verifier](QPBT/Palomar/Definitions.lean).

## Low-degree soundness

The printed proof of MIP*=RE Theorem 7.8 claims a game correspondence and
applies Theorem 4.7 of Ji, Natarajan, Vidick, Wright, and Yuen,
[*Quantum soundness of testing tensor codes*, arXiv:2111.08131v3](https://arxiv.org/abs/2111.08131v3),
with `K = m³ d`. That theorem assumes `K ≥ 12 m t`; for the degree-`d`
Reed-Solomon code, `t = d + 1`. Thus the printed choice of `K` does not meet
the hypothesis for small `m`. MIP*=RE does not print the inequality
`K ≥ 12 m (d + 1)`. This formalization neither uses nor establishes the claimed
correspondence or that bound for the printed choice of `K`. Instead, it proves
soundness for a directly indexed low individual degree game, obtains simultaneous
measurements by adapting the combining argument in
[NEEXP in MIP*, arXiv:1904.05870v3, Theorem 4.43](https://arxiv.org/abs/1904.05870v3),
and transports the result through a correlated seed dilation. The two
point-consistency relations survive compression exactly; the global relation
follows from point agreement and Schwartz–Zippel. See
[the direct reduction](QPBT/Combining/DirectLowDegree/Soundness.lean) and
[the seed-indexed theorem](QPBT/Test/LowDegreeGameTheorems.lean).
The combining argument is proved locally; the NEEXP theorem is not an axiom.

The underlying LIDT theorem is imported from the pinned
[LionSR/MIPStarRE dependency](https://github.com/LionSR/MIPStarRE/tree/5fc363bc8b77b1a6bbdaaeea634f1b0f3ff0ad79).
Its public `MIPStarRE.LDT.Test.mainFormal` uses the corrected conditions
`K ≥ 400 M d` and `K > 0`, where `M` is the dimension of the single-polynomial
game passed to that theorem. The auxiliary choice `K = 2560000 M³ d` satisfies
both, as proved in
[the parameter estimates](QPBT/Combining/DirectLowDegree/Transport/Error.lean).
The standalone `k = 1` base case uses `M = m`; the
[general combining construction](QPBT/Combining/DirectLowDegree/Transport/Combining/SimultaneousGeneral.lean)
uses `M = m + k`, as defined by
[the combined parameters](QPBT/Combining/DirectLowDegree/Transport/Combining/Parameters.lean).
These conditions are discharged internally, not added to the QPBT headline
statements. The QPBT-local [linear-triangle bounds](QPBT/LDT/Test/MainTheorem/LinearTriangle/MainFormal.lean)
retain the sharper quantitative estimates needed by the QPBT error analysis.

## Finite fields and compact statements

MIP*=RE Section 3.3.2 fixes a self-dual normal basis and identifies field
elements with their natural binary coordinates. `FixedFieldModel` records this
basis, self-duality, normality, and the binary encoding explicitly, and
`fixedFieldModel` selects it once for each admissible field size. See
[the field model](QPBT/Algebra/FieldBasis.lean).

The compact definitions in [Challenge.lean](Challenge.lean) are Mathlib-only.
The four theorem names, parameter order, witnesses, error bounds, and fixed-field
selector contract are transported from the library by proved equivalences in
[the Palomar modules](QPBT/Palomar). The production build imports the
[axiom audit](QPBT/Test/AxiomAudit.lean); its permitted axioms are `propext`,
`Quot.sound`, and `Classical.choice`.

The [archived list of intermediate deviations](https://github.com/Dengnifer/MIPStarRE-QPBT-bak/blob/8df6267fa02edf52be1a4f946d188ca8f8feb5d3/docs/DEVIATIONS.md)
records further corrections to intermediate results; these do not change the
comparator-configured headline statements.
