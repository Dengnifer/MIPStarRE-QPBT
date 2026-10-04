# Source statements and formal conventions

The primary source is [MIP*=RE, arXiv:2001.04383v3](https://arxiv.org/abs/2001.04383v3).
The registered statements are Theorem 7.8, Lemma 7.13, Theorem 7.14, and
Corollary 7.15. The Lean statements retain explicit error functions and the
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

The proof of MIP*=RE Theorem 7.8 invokes a tensor-code game correspondence and
uses `K = m³ d` while asserting `K ≥ 12 m (d + 1)`. The latter inequality does
not hold uniformly for its stated positive parameters. This formalization
neither uses nor proves those two assertions. Instead, it proves soundness for
a directly indexed low individual degree game, obtains simultaneous
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
`K ≥ 400 m d` and `K > 0`. Our auxiliary choice `K = 2560000 m³ d` satisfies
both, as proved in
[the parameter estimates](QPBT/Combining/DirectLowDegree/Transport/Error.lean).
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
