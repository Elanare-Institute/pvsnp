/-
# 分離プログラム（予想A・B と定理2）

v3 指示書 §9。論文 §6.2–6.4。

**原則 (P3)**: 独自の `axiom` をゼロにする。
予想は `def … : Prop` として定義し、定理の仮定として明示する。

v2 では Conjecture A/B を `axiom` として宣言し、しかも Conjecture B を
**すべての** NPRelation に量化していた。これは矛盾しており
（`Test/Phase0Inconsistency.lean` で実証済み）、
`conditional_p_ne_np` は空虚に成立していた。
v3 では予想Bを NP 完全 relation に限定し、両者を仮定として明示する。
-/
import DirectionalAsymmetry.Concrete.Characterization
import Mathlib.Order.Filter.AtTopBot.Defs

open Filter

/-- 論文の定義8: 残余構造的非対称性（ブラックボックス）。 -/
opaque residualAsym (R : NPRel) (M : TCS R) (n : ℕ) : ℤ

/-- `ω(log n)`（超対数的）。 -/
def Unbounded (f : ℕ → ℤ) : Prop :=
  ∀ C : ℕ, ∃ᶠ n in Filter.atTop, (C * (Nat.log 2 n + 1) : ℤ) < f n

/-- **予想A**: 構造的 → 計算的 の橋渡し。 -/
def ConjA : Prop :=
  ∀ (R : NPRel) (M : TCS R), PolyTime M.M → Unbounded (residualAsym R M) → Unbounded (profile M)

/-- **予想B**: 意味次元の汲み尽くし不可能性（NP 完全 relation に限定）。 -/
def ConjB : Prop :=
  ∀ (R : NPRel), IsNPComplete R.lang →
    ∀ (M : TCS R), PolyTime M.M → Unbounded (residualAsym R M)

/-- `LogBounded` なら `Unbounded` ではない。 -/
theorem not_unbounded_of_logBounded {f : ℕ → ℤ} (h : LogBounded f) : ¬ Unbounded f := by
  intro hu
  obtain ⟨C, hC⟩ := h
  have hfreq := hu C
  have hcontra : ∃ᶠ _n : ℕ in atTop, False := by
    refine hfreq.mono ?_
    intro n hn
    have := hC n
    omega
  simp at hcontra

/--
**定理2**: 予想A・Bと NP 完全 relation の存在から P ≠ NP。

予想は仮定として明示し、NP 完全 relation の存在（Cook–Levin）も
仮定にする（Lean では Cook–Levin を形式化しない）。
-/
theorem thm2 (hA : ConjA) (hB : ConjB) (hCL : ∃ R : NPRel, IsNPComplete R.lang) :
    ¬ PeqNP := by
  intro hPeq
  obtain ⟨R, hNPC⟩ := hCL
  -- P = NP より、多項式時間で LogBounded な TCS が存在
  obtain ⟨M, hMpoly, hMlog⟩ := thm1_a_to_b hPeq R
  -- 予想B: residual は Unbounded
  have hres := hB R hNPC M hMpoly
  -- 予想A: profile も Unbounded
  have hprof := hA R M hMpoly hres
  -- しかし profile は LogBounded
  exact not_unbounded_of_logBounded hMlog hprof

/-! ## 回帰テスト: v2 型の過剰量化は矛盾する -/

/-- v2 型: NP 完全性の仮定のない予想B。 -/
def ConjB_allRel : Prop :=
  ∀ (R : NPRel) (M : TCS R), PolyTime M.M → Unbounded (residualAsym R M)

/-- 自明な relation 上の自明な TCS（常に `[]` を返す）。 -/
def trivialTCS : TCS trivialRel where
  M := Prog.const []
  total := fun x => ⟨[], _, Prog.Eval.const [] x⟩
  correct := by
    intro x y t hev hx
    simp [trivialRel_lang] at hx
  short := by
    intro x y t hev
    rw [hev.const_inv]
    simp [trivialRel]

theorem trivialTCS_polyTime : PolyTime trivialTCS.M := polyTime_const []

/--
**v2 型の過剰量化は矛盾する**。

`trivialRel`（NP 完全ではない）と定数出力の TCS について、
`profile` は定数なので `Unbounded` になりえない。
しかし `ConjB_allRel` は `Unbounded` を主張する。

この定理が証明できること自体が、
「予想Bの量化を NP 完全 relation に限定しなければならない」ことの
形式的証拠になる。
-/
theorem v2_style_inconsistent : ConjA → ConjB_allRel → False := by
  intro hA hB
  -- ConjB_allRel を自明な TCS に適用
  have hres := hB trivialRel trivialTCS trivialTCS_polyTime
  have hprof := hA trivialRel trivialTCS trivialTCS_polyTime hres
  -- しかし profile trivialTCS は LogBounded（実際には定数）
  refine not_unbounded_of_logBounded ?_ hprof
  -- profile の各点は asym で、time も vtime も定数なので有界
  obtain ⟨C, hC⟩ := logBounded_of_polyTime (M := trivialTCS) trivialTCS_polyTime
  exact ⟨C, hC⟩
