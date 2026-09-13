/-
# Layer 3: 分離プログラム (Conjecture A, B と Theorem 2)

v2 指示書 §4 に対応（論文 §7.3–7.5）。

**重要**: Conjecture A / B は `axiom` として宣言する（未証明であることを明示）。
`conditional_p_ne_np` はこれらに依存する **条件付き** の結果であり、
P≠NP の証明ではない。
-/
import DirectionalAsymmetry.Characterization
import DirectionalAsymmetry.SearchSpace
import DirectionalAsymmetry.MeaningTransformation
import Mathlib.Order.Filter.AtTopBot.Defs

open Asymptotics Filter

universe u

variable {α : Type u} [Fintype α] [DecidableEq α] [Nonempty α]

/--
残余構造的非対称性。

「M が利用可能な全ての多項式時間変換を適用した後の、
サイズ n における構造的非対称性」。

v2 §7.6 の指摘どおり正確な定義は複雑なので、
指示書が許容している **抽象化した形**（署名のみを与え、
具体的な構成は与えない）を採る。
`opaque` により「何らかの関数が存在する」ことだけを主張し、
その中身に依存しない議論を可能にする。
-/
opaque residualStructuralAsymmetry
    {α : Type u} [Fintype α] [DecidableEq α] [Nonempty α]
    (R : NPRelation α) (M : TotalCandidateSolver α R) (n : ℕ) : ℝ

/-- 「超対数的」(ω(log n)) であることの述語。 -/
def Superlogarithmic (f : ℕ → ℝ) : Prop :=
  ∀ C : ℕ, ∃ᶠ n in atTop, f n > C * (Nat.log 2 n : ℝ)

/--
Conjecture A: 構造的 → 計算的 の橋渡し。

M が利用可能な全ての多項式時間変換を適用してもなお
構造的非対称性が ω(log n) であるならば、
計算的非対称性も ω(log n) である。

**未証明の予想**。`axiom` として宣言する。
-/
axiom conjecture_A
    {α : Type u} [Fintype α] [DecidableEq α] [Nonempty α]
    (R : NPRelation α) (M : TotalCandidateSolver α R) :
    Superlogarithmic (fun n => residualStructuralAsymmetry R M n) →
    Superlogarithmic (fun n => (maxAsymmetryAbs M n : ℝ))

/--
Conjecture B: 意味次元の汲み尽くし不可能性。

任意の多項式時間 TCS に対し、それが行える全変換の後でもなお
残余構造的非対称性が ω(log n) となる NP 符号化可能な族が存在する。

**未証明の予想**。`axiom` として宣言する。

論文 §7.4 の注記: これは「有限のアルゴリズムは有限の技しか持たない」
という弱い主張ではなく、「多項式資源では NP 符号化可能な非対称構造の
多様性を汲み尽くせない」という主張である。
-/
axiom conjecture_B
    {α : Type u} [Fintype α] [DecidableEq α] [Nonempty α]
    (R : NPRelation α) (M : TotalCandidateSolver α R) :
    IsPolynomial (worstCaseTime M.solveTime) →
    Superlogarithmic (fun n => residualStructuralAsymmetry R M n)

/--
超対数的な関数は O(log n) ではありえない。

Thm 2 の証明の核心部分。
`f n > C * log n` が無限に多くの n で成り立つなら、
`f = O(log n)` に矛盾する。
-/
theorem not_isBigO_of_superlogarithmic {f : ℕ → ℝ}
    (hf : Superlogarithmic f) (hpos : ∀ n, 0 ≤ f n) :
    ¬ (f =O[atTop] (fun n : ℕ => (Nat.log 2 n : ℝ))) := by
  intro hO
  rw [isBigO_iff] at hO
  obtain ⟨c, hc⟩ := hO
  -- c 以上の自然数 C を取る
  obtain ⟨C, hC⟩ := exists_nat_ge c
  -- Superlogarithmic より f n > C * log n が無限に多くの n で成立
  have hfreq := hf C
  -- しかし hc より f n ≤ c * log n が十分大きな全ての n で成立
  have hcontra : ∃ᶠ _n : ℕ in atTop, False := by
    refine (hfreq.and_eventually hc).mono ?_
    rintro n ⟨hgt, hle⟩
    rw [Real.norm_natCast] at hle
    rw [Real.norm_eq_abs, abs_of_nonneg (hpos n)] at hle
    have hlogn : (0 : ℝ) ≤ (Nat.log 2 n : ℝ) := Nat.cast_nonneg _
    nlinarith
  simp at hcontra

/--
Theorem 2: Conjecture A + Conjecture B ⟹ P ≠ NP。

**条件付きの結果**。A と B は `axiom` なので、
`#print axioms` では `conjecture_A`, `conjecture_B` が現れる。
A+B から P≠NP を導く部分自体は `sorry` なしで証明する。

証明: `p_ne_np_iff_superlog_asymmetry` の右辺を示せばよい。
任意の NP relation `R` と多項式時間 TCS `M` に対し、
Conjecture B で残余構造的非対称性が ω(log n)、
Conjecture A で計算的非対称性が ω(log n)、
よって O(log n) ではありえない。
-/
theorem conditional_p_ne_np (R : NPRelation α) : ClassP α ≠ ClassNP α := by
  rw [p_ne_np_iff_superlog_asymmetry]
  refine ⟨R, fun M hpoly => ?_⟩
  -- Conjecture B: 残余構造的非対称性が超対数的
  have hB := conjecture_B R M hpoly
  -- Conjecture A: 計算的非対称性も超対数的
  have hA := conjecture_A R M hB
  -- 超対数的なら O(log n) ではない
  exact not_isBigO_of_superlogarithmic hA (fun n => Nat.cast_nonneg _)
