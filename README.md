# pvsnp — Computational Directional Asymmetry (Lean 4 formalization)

Lean 4 formalization of "Computational Directional Asymmetry: Dissolving the Classical Question Behind P vs NP" by Franny Philos Sophia (revision 1).

- Japanese version of this README: [`README.ja.md`](README.ja.md)
- Paper: <https://doi.org/10.5281/zenodo.22939703>
- Specifications (in Japanese): [`docs/lean4-spec-v3.md`](docs/lean4-spec-v3.md), [`docs/lean4-spec-v4.md`](docs/lean4-spec-v4.md)
- Verification reports (in Japanese): [`VERIFICATION-v3.md`](VERIFICATION-v3.md) and [`VERIFICATION-v4.md`](VERIFICATION-v4.md); the v2 record is kept in [`VERIFICATION.md`](VERIFICATION.md)

> **Note.** This formalization does not prove P ≠ NP. Theorem 2 is proved as an implication whose hypotheses are Conjectures A and B together with the existence of an NP-complete relation. Conjectures A and B are unproven, and the project declares no custom axioms.

## Corrections relative to v2 (important)

Version 2, which corresponds to the previous README and to the first preprint of the paper, had three problems.

1. **An inconsistent axiom system.** v2 declared Conjectures A and B as axioms, with Conjecture B quantified over all NP relations rather than over NP-complete ones. That axiom system is inconsistent: `False` is derivable from a trivial relation (empty language, constant-output solver), as verified in Lean. The v2 theorem `conditional_p_ne_np` therefore held vacuously. The previous README's statement that `#print axioms conditional_p_ne_np` depends only on `conjecture_A` and `conjecture_B` carries no verificational content and is withdrawn.
2. **Running time as an abstract field.** A solver's running time was a number unrelated to its execution, so a solver could be transported from one witnessing relation to another at no cost. The search construction of Theorem 1 was therefore not verified.
3. **Degenerate per-instance optima.** `optimalAsymmetry` was a per-instance infimum, which a solver with a hard-coded answer drives to O(log n) on every instance.

v3 resolves all three. That Conjecture B must be restricted to NP-complete relations is proved formally as the regression lemma `v2_style_inconsistent : ConjA → ConjB_allRel → False`.

## Computational model

Algorithms are represented as syntax: programs in a small language over binary strings, with pairing, head and tail operations, conditionals, and loops. Running time is derived from a big-step cost semantics `Eval`; it is never stored as a field. Every primitive costs at least the lengths of its input and output, so data cannot grow faster than running time.

The search procedure actually runs:

```lean
run 200 (prefixSearch D0 V0) [true, false] = some ([true], 168)   -- checked by rfl
```

**Unformalized assumption:** the programming language is polynomially equivalent to Turing machines. This is the standard invariance assumption of complexity theory (paper, §8.4).

## Building

```bash
lake exe cache get   # fetch prebuilt Mathlib (first time only; required)
lake build
```

Environment: Lean 4 **v4.33.1** / Mathlib **v4.33.1**.

Besides the formalization itself, `lake build` runs the `sorry` and axiom audits and the execution tests.

## Status

- `lake build`: no errors, no warnings
- `sorry`: none (151 declarations audited at the proof-term level)
- Custom axioms: none (32 main theorems depend only on `propext`, `Classical.choice`, `Quot.sound`)

```
#print axioms thm2
-- [propext, Classical.choice, Quot.sound]
```

## Main results (correspondence with paper revision 1)

| Paper (rev. 1) | Content | Lean |
|---|---|---|
| §3.2 | Universal lower bound g_M(n) ≥ −O(log n) | `asym_lower` |
| §3.2 | Degeneracy of per-instance optima | `pointwise_degenerate` |
| §3.3 | Prefix language Pref_R and the search procedure built on it | `prefRel`, `prefixSearch_tcs`, `prefixSearch_polyTime` |
| §3.3 | Theorem 1: (a) ⇔ (b), and (a) ⇔ (c) for NP-complete R | `thm1_a_iff_b`, `thm1_a_iff_c` |
| §3.3 | Corollaries 1 and 2 | `cor1`, `cor1'`, `cor2` |
| §3.3 | For SAT-type relations, Pref coincides with the solvable region on prefix-shaped partial assignments | `prefix_mem_solvable_iff` |
| §4.3 | Proposition 1: P = NP ⇔ Σ_NP = {[0]} | `prop1` (spectrum: `asymSpectrum`) |
| §5.4 | Proposition 2: accumulation identity | `accumulation_identity` |
| §6.3 | Restricting Conjecture B to NP-complete relations is essential | `v2_style_inconsistent` |
| §6.4 | Theorem 2: Conjectures A and B imply P ≠ NP | `thm2` (residual asymmetry: opaque `residualAsym`) |
| §6.5 | Definition 9: structural asymmetry relative to a proof system | `structAsym` |
| §6.5 | Theorem 3: in the restricted settings the bridge is a theorem | `bridge_resolution` (proved uniformly in `ProofKind`, so it covers both DPLL-style and clause-learning settings) |
| §6.5 | Theorem 4(i) (Haken 1985) | `HakenLB` (a hypothesis, not an axiom) |
| §6.5 | Corollary 3: no DPLL-style or clause-learning solver is a polynomial-time total candidate solver | `no_polytime_res_solver` |
| §6.5 | In the restricted settings Conjecture A′ itself becomes a theorem | `conjA_restricted_holds` (with `ConjA_restricted`, the restricted form of `ConjA` with `structAsym` in place of the opaque `residualAsym`) |
| §6.5 | Soundness of resolution refutations (so the definitions are not vacuous) | `tree_sound`, `gen_sound` |

## Not formalized

- Polynomial equivalence of the programming language with Turing machines (the assumption above)
- The Cook–Levin theorem (the existence of an NP-complete relation is an explicit hypothesis of `thm2`)
- Per-length degeneracy of optima (only the per-instance version is formalized)
- Conjectures A and B themselves (hypotheses of Theorem 2, not axioms)
- That DPLL and CDCL runs yield resolution refutations (Beame–Kautz–Sabharwal 2004). This is what the `extract` field of `ResSolver` assumes; it *is* the definition of the restricted settings.
- Haken's lower bound itself (`HakenLB` is a hypothesis of Corollary 3)
- The existence of an NP relation implementing SAT (`ImplementsSAT` is a hypothesis), so Theorem 3 and Corollary 3 are conditional on there being one
- Completeness of resolution, Chvátal–Szemerédi (1988), and Buss (1987)

## Layout

```
DirectionalAsymmetry/
├── Concrete/
│   ├── Encoding.lean          -- binary strings and pair encoding
│   ├── Prog.lean              -- programming language and cost semantics Eval
│   ├── Interp.lean            -- fuel-bounded interpreter run and its soundness
│   ├── Poly.lean              -- polynomial bounds and closure properties
│   ├── Classes.lean           -- PolyTime, ClassP, NPRel, ClassNP, PeqNP, IsNPComplete
│   ├── TCS.lean               -- total candidate solvers, asymmetry, profiles, lower bound
│   ├── Prefix.lean            -- prefix language and the search procedure
│   ├── Characterization.lean  -- Theorem 1, Corollaries 1 and 2
│   ├── Spectrum.lean          -- asymmetry classes, spectrum, Proposition 1
│   ├── Degeneracy.lean        -- degeneracy of per-instance optima
│   └── Separation.lean        -- Conjectures A and B (as Props), Theorem 2, regression lemma
├── Restricted/                -- paper §6.5: where the bridge is a theorem
│   ├── Prop.lean              -- propositional logic: literals, clauses, CNF, satisfaction
│   ├── Resolution.lean        -- resolution, tree-like and general refutations, soundness
│   ├── Encoding.lean          -- encoding CNFs as binary strings, injectivity, length bounds
│   ├── SATRel.lean            -- ImplementsSAT
│   ├── Solvers.lean           -- ResSolver: the restricted settings
│   ├── Bridge.lean            -- Definition 9 and Theorem 3
│   ├── Pigeonhole.lean        -- the pigeonhole formulas and their unsatisfiability
│   └── Corollary.lean         -- HakenLB and Corollary 3
├── Search/                    -- solvable region, local asymmetry, accumulation, structure-revealing
│                                 transformations, and the bridge lemma (Bridge.lean)
├── Distribution.lean          -- asymmetry distributions
└── Main.lean
Legacy/                        -- v2 abstract layer (separate target; kept as the record of the
                                  inconsistency, not part of the default build)
Test/
├── NoSorryInDefs.lean         -- sorry audit
├── NoCustomAxioms.lean        -- axiom audit of the main theorems
├── Exec.lean                  -- execution tests
├── RestrictedExec.lean        -- execution tests for the §6.5 layer
└── Phase0Inconsistency.lean   -- the v2 inconsistency proof (separate target)
```

To reproduce the v2 inconsistency result:

```bash
lake build Legacy Phase0Test
# 'v2_axioms_inconsistent' depends on axioms:
#   [conjecture_A, conjecture_B, propext, Classical.choice, Quot.sound]
```

## Deviations from the specification

For v3 there are six minor deviations and three strengthened proof hints; for v4, six more (mostly name clashes with Mathlib, and a decoder defined as the inverse image of an injective encoder rather than as a parser). None changes the mathematical content. See [`VERIFICATION-v3.md`](VERIFICATION-v3.md) and [`VERIFICATION-v4.md`](VERIFICATION-v4.md).
