# Paper Structure

## Target
- Initial: arXiv preprint
- Then: computational complexity venue (CCC, Computational Complexity journal, or STOC/FOCS workshop)
- Word limit: ~12,000–15,000 words (full paper)

## Architecture

```
             Search-space structure (Def 5–6)
                     │
                     ▼
Local asymmetry → Accumulation (Prop 2) → A_M(x) (Def 3) → D_n(A) (Def 4)
                     │                        │                    │
                     │                        │                    └─ Five Worlds (§5)
                     │                        │
                     │                        └─ Boppana–Lagarias extension (§3)
                     │                               P=NP characterization (Thm 1)
                     │
                     ▼
         Meaning Transformation (Def 7)
                     │
                     ▼
              Inexhaustibility (Conj B)
                     │
            Bridge (Conj A) ←──────┘
                     │
                     ▼
              P ≠ NP (Thm 2, conditional)
                     │
              Barrier analysis (§8)
```

## Three Layers

| Layer | Content | Status |
|---|---|---|
| **Layer 1: Formal results** | Def 1–4, Thm 1, accumulation identity | Provable, Lean-verifiable |
| **Layer 2: New framework** | Def 5–7, Prop 2, Five Worlds interpretation | Definitions + propositions + interpretation |
| **Layer 3: Separation program** | Conj A, Conj B, Thm 2 (conditional) | Conjectures, conditional theorem |

## Section Outline

### 1. Introduction (~1500 words)

- **Hook**: P vs NP asks whether verification is fundamentally easier than construction. But "easier" is measured by a binary threshold (polynomial or not) that discards most of the structure.
- **Problem**: The polynomial boundary coarsens a continuous, distributional phenomenon into a yes/no question. This obscures the mechanism that generates computational difficulty.
- **What we do**: Define computational directional asymmetry $A_M(x)$ as a primitive quantity. Show P vs NP is equivalent to a question about its worst-case tail (Thm 1). Lift this to a problem-level asymmetry spectrum $\Sigma_{NP}$ where P = NP becomes complete spectral degeneracy: the collapse of all asymmetry to zero across every NP problem simultaneously. Unify existing complexity concepts (worst-case, average-case, parameterized, one-way) as statistics of the asymmetry distribution. Identify the separation program: two conjectures whose conjunction implies P ≠ NP.
- **The key shift**: For any NP problem, either solve cost exceeds verify cost, equals it, or is less. Among those where solve > verify, the *excess varies widely* across problems — from near-zero to apparently exponential. P = NP would require this entire spread to collapse to zero. The reformulation makes visible what the original set-equality formulation obscures: that P = NP is a maximally degenerate special case.
- **What we don't do**: We do not prove P ≠ NP. We identify exactly two conjectures whose conjunction implies P ≠ NP, and argue for their plausibility.
- **Relation to prior work**: Boppana–Lagarias (1986/87) defined a log-ratio asymmetry for function inversion. We generalize to solve/verify, add distributional analysis, and connect to search space structure.

### 2. Preliminaries (~800 words)

- **Def 1**: NP relation $R(x,w)$, language $L_R$, polynomial-time verifier $V$
- Standard complexity notation
- Circuit complexity $C(\cdot)$ and Turing machine time $T(\cdot)$

### 3. Computational Directional Asymmetry (~2000 words)

**§3.1 Total Candidate Solver**
- **Def 2**: Total candidate solver $M$: on input $x$, always halts, outputs candidate $w = M(x)$. Required: $x \in L_R \Rightarrow R(x, M(x)) = 1$.
- Resolves the NO-instance problem: $A_M(x)$ defined for all $x$.

**§3.2 The Asymmetry Quantity**
- **Def 3**: $A_M(x) = \log_2 T_M(x) - \log_2 T_V(x, M(x))$
- Discussion: not a property of the problem alone, but of the (algorithm, problem) pair
- **Def 3'**: Optimal asymmetry $A^*(x) = \inf_M A_M(x)$ over all total candidate solvers $M$. Note: by Blum's speed-up theorem (1967), the infimum may not be attained — there is not always a "fastest algorithm." This is why we define $A^*$ as an infimum, not a minimum. For Thm 1, the existential formulation ($\exists M$) avoids this issue.
- Relationship to Boppana–Lagarias $M(f)$ and Birget's $\alpha(s)$: our $A_M$ generalizes from $f/f^{-1}$ to solve/verify, and from worst-case scalar to instance-level quantity

**§3.3 P = NP Characterization**
- **Thm 1**: $P = NP$ iff there exists a polynomial-time total candidate solver $M$ with $\sup_{|x|=n} A_M(x) = O(\log n)$.
- Proof (both directions). This is the paper's first formal result.
- Corollary: $P \neq NP$ iff for every poly-time total candidate solver $M$, $\sup_{|x|=n} A_M(x) = \omega(\log n)$.

**§3.4 Comparison with Prior Asymmetry Measures**
- Boppana–Lagarias: $M(f) = \min_g \log C(f) / \log C(g)$ — scalar, for bijections
- Birget: $\alpha(s) = \max\{C(f^{-1}) : C(f) \leq s\}$ — worst-case envelope
- Hiltgen: provable asymmetry factor $\to 2$ (current frontier)
- Our contribution: (a) solve/verify generalizes $f/f^{-1}$, (b) instance-level distribution, (c) tail as unifying concept

### 4. The Asymmetry Distribution (~1500 words)

**§4.1 Distribution Definition**
- **Def 4**: Fix measure $\mu_n$ on size-$n$ instances. $\mathcal{D}_n^M(A) = (A_M)_* \mu_n$ (pushforward).
- Statistics: $S_n = \sup A_M(x)$, $E_n = E_{\mu_n}[A_M]$, $T_n(t) = \Pr[A_M > t]$.

**§4.2 Existing Concepts as Statistics**
| Concept | Statistic |
|---|---|
| Worst-case complexity | $S_n$ |
| Average-case complexity (Levin) | $E_n$ |
| One-way functions | Tail $T_n(t)$ with structured generation |
| Parameterized complexity | Conditional $A_M$ given parameter |

**§4.3 Problem-Level Spectrum**
- **Def 4'**: For NP language $L$, define problem-level asymmetry $A^*(L) = \limsup_n \sup_{|x|=n} A^*(x) / \log n$ (normalized growth rate).
- Asymmetry spectrum: $\Sigma_{NP} = \{A^*(L) : L \in NP\}$.
- $P = NP \iff \Sigma_{NP} = \{0\}$: the spectrum is completely degenerate.
- $P \neq NP \iff \Sigma_{NP} \neq \{0\}$: at least one problem has non-vanishing asymmetry.
- This re-expresses P vs NP as: "Does the directional asymmetry spectrum of NP collapse to a single point?"

**§4.3.1 Spectral Spread**
- The core observation (prior to any proof): even without settling P vs NP, problems in NP empirically exhibit *diverse* asymmetry. Some NP problems are solved near-optimally (matching heuristics reduce $A$ close to zero), others resist all known algorithms ($A$ remains large). This diversity is not uniform — there is *spread* (variance) in the spectrum.
- Three-way classification of any problem: $A^*(Q) < 0$ (verify harder than solve — atypical), $A^*(Q) = 0$ (symmetric — the P = NP case), $A^*(Q) > 0$ (solve harder than verify — the common case for NP-hard problems).
- The spread matters because: if all solve > verify problems had the *same* excess, one could argue this is an artifact of the verification definition (perhaps a better verifier exists). But the empirical fact that excesses *vary widely* across problems — from near-zero (2-SAT, matching) to apparently exponential (random 3-SAT, factoring) — indicates that the asymmetry is structural, not definitional.
- Formally: $\operatorname{Var}(\Sigma_{NP}) > 0$ is a stronger statement than $\Sigma_{NP} \neq \{0\}$. The former says the spectrum has genuine spread; the latter only says it's non-degenerate. For P ≠ NP, the latter suffices. But the former is what makes the degeneracy hypothesis ($\Sigma_{NP} = \{0\}$) appear implausible: it would require collapsing a structurally diverse spectrum to a single point.

**§4.4 The Information Discarded by the Polynomial Boundary**
- $V(n) = n$, $S(n) = n^{100}$: both polynomial, $A_n = O(\log n)$
- $V(n) = n^{10}$, $S(n) = 2^n$: separation candidate, $A_n = \Theta(n)$
- The polynomial boundary collapses a continuous spectrum into binary

### 5. Five Worlds as Tail Regimes (~1500 words)

- **Algorithmica**: $S_n = O(\log n)$ — no tail
- **Heuristica**: $S_n = \omega(\log n)$, $E_n = O(\log n)$ — sparse, unfindable tail (black swans)
- **Pessiland**: $E_n = \omega(\log n)$ — thick but unstructured tail
- **Minicrypt**: thick + structured tail (OWFs: can generate hard instances with known solutions)
- **Cryptomania**: thick + structured + robust tail (survives information leakage)
- Three axes: tail mass, tail controllability, tail robustness
- **Proposition**: Connection to Hirahara–Lu characterization of OWFs via information asymmetry

### 6. Search Space Structure and Local Asymmetry (~2000 words)

**§6.1 Solution Space vs Search Space**
- **Solution space**: $S_\phi = \{x : \phi(x) = 1\}$ — the answers (Alasli 2025 studies this)
- **Search space**: partial-assignment lattice $\{0,1,*\}^n$ — the exploration process

**§6.2 Solvable Region**
- **Def 5**: $R_\phi = \{p \in \{0,1,*\}^n : \exists x \supseteq p, \phi(x) = 1\}$
- Membership is NP-hard (residual SAT). Algorithm cannot efficiently "see" the space it navigates.

**§6.3 Local Search Asymmetry**
- **Def 6**: At partial assignment $p \in R_\phi$:
  - $E(p)$ = set of one-step extensions
  - $G(p) = E(p) \cap R_\phi$ = solution-preserving extensions
  - $a(p) = \log |E(p)| / |G(p)|$
- $a(p) = 0$: every direction leads toward a solution (easy)
- $a(p)$ large: most directions are dead ends (hard)

**§6.4 Accumulation Identity**
- **Prop 2**: Along a search path $p_0 \to p_1 \to \cdots \to p_d$:
  $$A_{\text{struct}} = \sum_{i=0}^{d-1} a(p_i) = \log \prod_{i=0}^{d-1} \frac{|E(p_i)|}{|G(p_i)|}$$
- Homogeneous case: $A_{\text{struct}} = d \cdot \log(b_f / b_s)$ where $b_s$ = solution-preserving branching
- Key insight: exponential search time = local uncertainty accumulated over depth

**§6.5 Information-Theoretic Reading**
- $q_i = |G(p_i)| / |E(p_i)|$ = probability of choosing a solution-preserving direction
- $a_i = -\log q_i$ = information deficit per step
- Total: $A_{\text{struct}} = -\log \prod q_i$ = total information deficit
- Exponential blowup is compound interest on uncertainty

### 7. The Separation Program (~2000 words)

**§7.1 The Gap: $A_{\text{struct}}$ vs $A_M$**
- Intelligent algorithms don't brute-force the search tree
- CDCL, propagation, learning, relaxation change $E/G$ ratios
- $A_{\text{struct}}$ (brute-force asymmetry) ≠ $A_M$ (algorithmic asymmetry)
- The question: can algorithmic techniques always collapse $A_{\text{struct}}$ to $O(\log n)$?

**§7.2 Meaning Transformation**
- **Def 7**: A representation transformation $\tau: p \mapsto \tau(p)$ is asymmetry-reducing if it enables the algorithm to better identify $G(p) \subset E(p)$, effectively reducing $a(p)$.
- Meaning = a new representation that makes solution-preserving directions distinguishable
- Examples: unit propagation (reveals forced assignments), CDCL (reveals conflict structure), LP relaxation (reveals fractional structure)

**§7.3 Conjecture A — Structural-to-Computational Bridge**
- **Conjecture A**: If, after applying all poly-time-computable asymmetry-reducing transformations available to $M$, the residual structural asymmetry satisfies $A_{\text{struct}}^M(x) = \omega(\log n)$, then $A_M(x) = \omega(\log n)$.
- Discussion: what this says and doesn't say

**§7.4 Conjecture B — Meaning-Dimension Inexhaustibility**
- **Conjecture B**: For every polynomial-time total candidate solver $M$, there exists an NP-encodable instance family $\{x_n\}$ such that $A_{\text{struct}}^M(x_n) = \omega(\log n)$ after all transformations $M$ can perform.
- Not: "a finite algorithm has finitely many tricks" (too weak — poly-time algorithms can generate diverse strategies)
- But: "polynomial resources cannot exhaust the structural diversity of NP-encodable asymmetry"
- Connection to Cook-Levin: NP-completeness guarantees the diversity of encodable structures

**§7.5 Conditional Separation**
- **Thm 2**: Conjecture A + Conjecture B $\Rightarrow$ P ≠ NP.
- Proof: by contradiction via Thm 1.

### 8. Barrier Analysis (~1200 words)

**§8.1 Relativization**
- $A_M$ definition relativizes (gives different answers with different oracles)
- The proof must use non-relativizing components
- Cook-Levin provides one: it depends on the specific encoding of TM computations
- Conjectures A and B must be proved with non-relativizing techniques

**§8.2 Natural Proofs**
- Our framework is uniform (TM-based), not circuit-based
- $A_M$ is not a truth-table property; it's a process property
- The distributional/tail structure is not "constructive + large" in the Razborov-Rudich sense
- Caveat: if instantiated via circuits, care is needed

**§8.3 Algebrization**
- The structural properties used (Cook-Levin encoding, search tree composition) are boolean/combinatorial
- No arithmetization or algebraic extension is used
- The approach does not algebrize in the standard sense

**§8.4 Displacement Risk**
- Honest assessment: proving Conj A/B may be as hard as proving P ≠ NP directly
- The value of the reformulation is not that it makes the proof easy, but that it:
  (a) identifies the exact two bridges needed
  (b) provides a conceptual framework connecting multiple areas
  (c) suggests proof strategies (topological, information-theoretic) for each bridge

### 9. Discussion (~1500 words)

**§9.1 What the Paper Achieves**
- Formal characterization of P vs NP via directional asymmetry (Thm 1)
- Distributional unification of complexity concepts
- Five Worlds as continuous tail regimes
- Asymmetry spectrum $\Sigma_{NP}$: P=NP becomes complete spectral degeneracy
- Explicit identification of two conjectures that imply P ≠ NP
- Search-space framework distinct from solution-space topology

**§9.1.1 Conceptual Dissolution**
The original formulation asks whether two complexity classes are equal: $P \stackrel{?}{=} NP$. This is a binary question about set identity, and it has resisted resolution for over fifty years.

The reformulation transforms the question into: "Does the directional asymmetry spectrum $\Sigma_{NP}$ collapse to the single point $\{0\}$?" In this formulation:
- P = NP requires that *every* NP problem has zero asymmetry — a complete spectral degeneracy.
- P ≠ NP requires only that *one* problem has positive asymmetry — spectral non-degeneracy.

The logical content is equivalent. But the *perceptual* structure has changed. In the original formulation, P = NP and P ≠ NP appear as symmetric alternatives (two classes are equal, or they aren't). In the reformulation, they are radically asymmetric: P = NP demands the simultaneous vanishing of asymmetry across all NP problems — a structurally extreme condition — while P ≠ NP requires only a single witness.

Moreover, empirically, the asymmetry spectrum has *spread*: problems range from near-zero asymmetry (polynomial-time solvable) to apparently large asymmetry (no known subexponential algorithm). P = NP would require this diverse spread to be an illusion — every apparently hard problem actually having an undiscovered polynomial algorithm that collapses its asymmetry to zero. The spectral formulation makes the implausibility of this visible in a way the original set-equality formulation does not.

This is not a proof. But it is a change of *meaning structure*: the reformulation generates a coordinate system in which the answer, while not formally derived, becomes conceptually transparent. The formal content of the remaining proof is concentrated in Conjectures A and B, which capture the two precise conditions under which spectral non-degeneracy follows from structural diversity.

**§9.2 Relation to Physical Asymmetry**
- Directional asymmetry in computation mirrors irreversibility in physics (Aaronson 2005)
- The connection is motivational, not formal: mathematical algorithms are not bound by thermodynamics
- But: the ubiquity of directional asymmetry across domains (physical, chemical, biological, computational) suggests it is a structural feature of complex systems, not an artifact of specific models

**§9.3 Future Work**
- Formal proof of Conjecture A (structural-to-computational bridge)
- Formal proof of Conjecture B (inexhaustibility), potentially via:
  - Topological obstruction (search-space homology)
  - Information-theoretic arguments (connection to Hirahara–Lu pKt asymmetry)
  - Gödel-Nishida meaning-dimension framework (to be formalized separately)
- Lean 4 formalization of Layer 1 (in progress; Layer 1 definitions pass type-checking)
- Extension to other complexity separations (BPP vs NP, #P vs FP)
- Interaction with Blum's speed-up theorem: for problems without optimal algorithms, the infimum $A^*$ may exhibit different asymptotic behavior than any single $A_M$

### 10. Conclusion (~300 words)

P vs NP is not a question about whether specific problems are hard. It is a question about whether the directional asymmetry between construction and verification can be universally eliminated. We have shown that this asymmetry is a continuous, distributional quantity whose tail structure encodes the landscape of computational complexity — from Algorithmica to Cryptomania. The separation question reduces to two bridges: whether structural asymmetry implies computational asymmetry, and whether the diversity of NP-encodable structures exceeds what any polynomial-time algorithm can exhaust. These bridges are the next frontier.

## Cross-references
- §3 uses: Def 1 (§2)
- §4 uses: Def 3 (§3)
- §5 uses: Def 4 (§4), relates to Impagliazzo (1995) and Hirahara et al. (2023/2024)
- §6 uses: Def 1 (§2), independent of §3–5
- §7 uses: Def 3 (§3), Def 6 (§6), Prop 2 (§6), Thm 1 (§3)
- §8 uses: Conj A/B (§7)
- §9 uses: all

## Author

Franny Philos Sophia
Elanare Institute
franny.philos.sophia@elanare.jp
ORCID: 0009-0004-7089-5265
