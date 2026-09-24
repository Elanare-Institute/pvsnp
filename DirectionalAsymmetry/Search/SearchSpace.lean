/-
# Def 5–6: 探索空間の構造と局所非対称性

v2 指示書 §3.1, §3.2 に対応（論文 §6.2 Def 5, §6.3 Def 6）。

**解空間 (solution space) ではなく探索空間 (search space) を扱う**のが
本論文の特徴。解空間は「何を見つけるか」、探索空間は「どう探すか」。
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Fintype.Pi

universe u

/--
部分割当。未割当を `none` で表す（`{0,1,*}^n` に対応）。
-/
def PartialAssignment (n : ℕ) := Fin n → Option Bool

instance (n : ℕ) : Fintype (PartialAssignment n) :=
  inferInstanceAs (Fintype (Fin n → Option Bool))

instance (n : ℕ) : DecidableEq (PartialAssignment n) :=
  inferInstanceAs (DecidableEq (Fin n → Option Bool))

/-- 部分割当 `p` が全割当 `x` に延長されること。 -/
def PartialAssignment.Extends {n : ℕ} (p : PartialAssignment n)
    (x : Fin n → Bool) : Prop :=
  ∀ i, p i = some (x i) ∨ p i = none

/--
Definition 5: 可解領域 (solvable region)。

`φ` を満たす全割当に延長できる部分割当の集合。

**メンバーシップは NP 困難**（残余 SAT）。つまりアルゴリズムは
自分が探索している空間を効率的に「見る」ことができない。
これは定義上の欠陥ではなく、本質的な性質である。
-/
def solvableRegion {n : ℕ} (φ : (Fin n → Bool) → Prop) :
    Set (PartialAssignment n) :=
  { p | ∃ x, p.Extends x ∧ φ x }

/--
一手で到達できる拡張の集合。

未割当の変数 `i` を一つ選び、`true`/`false` のいずれかを割り当てる。
-/
def extensions {n : ℕ} (p : PartialAssignment n) : Set (PartialAssignment n) :=
  { p' | ∃ i : Fin n, p i = none ∧ ∃ b : Bool, p' = Function.update p i (some b) }

/-- `extensions p` は有限集合（`PartialAssignment n` 自体が有限なので自明）。 -/
theorem extensions_finite {n : ℕ} (p : PartialAssignment n) :
    (extensions p).Finite :=
  Set.toFinite _

/-- `extensions p ∩ solvableRegion φ` も有限。 -/
theorem extensions_inter_solvable_finite {n : ℕ}
    (φ : (Fin n → Bool) → Prop) (p : PartialAssignment n) :
    (extensions p ∩ solvableRegion φ).Finite :=
  Set.toFinite _

/--
Definition 6: 局所探索非対称性。

`a(p) = log |E(p)| − log |G(p)|`

ここで `E(p)` は一手拡張の全体、`G(p) = E(p) ∩ R_φ` は
解を保つ拡張の全体。

- `a(p) = 0`: どの方向へ進んでも解に至る（易しい）
- `a(p)` 大: ほとんどの方向が行き止まり（難しい）

v2 §3.2 は有限性・非空性を明示引数に取る形だが、
`PartialAssignment n` が `Fintype` なので有限性は自動。
非空性は `Set.Finite.toFinset` の `card` が 0 のとき
`Real.log 0 = 0` という junk 値になるだけで全域性は保たれるため、
引数には取らない（使う命題側で非空性を仮定する）。
-/
noncomputable def localAsymmetry {n : ℕ} (φ : (Fin n → Bool) → Prop)
    (p : PartialAssignment n) : ℝ :=
  Real.log ((extensions_finite p).toFinset.card : ℝ)
    - Real.log ((extensions_inter_solvable_finite φ p).toFinset.card : ℝ)

/--
情報理論的読み: `q(p) = |G(p)| / |E(p)|` は
「解を保つ方向を選ぶ確率」（論文 §6.5）。
-/
noncomputable def solvePreservingRatio {n : ℕ} (φ : (Fin n → Bool) → Prop)
    (p : PartialAssignment n) : ℝ :=
  ((extensions_inter_solvable_finite φ p).toFinset.card : ℝ)
    / ((extensions_finite p).toFinset.card : ℝ)
