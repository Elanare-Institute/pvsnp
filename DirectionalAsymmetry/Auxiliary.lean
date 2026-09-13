/-
# 補助補題: 対数と多項式

v2 指示書 §2.8 に対応。v1 で証明済みの 4 補題を新定義体系へ移植する。

v2 §2.8 は `Nat.log` ベースの signature を指定しているため、
v1 の `Real.log` 版をそのまま流用するのではなく、
ℕ 上で直接証明した版を主役にする（ℕ のままの方が素直）。
`Real.log` 版も v1 から引き継いで併置する。
-/
import DirectionalAsymmetry.Basic
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Log

open Asymptotics Filter

/--
`Nat.log b (n ^ m) ≤ m * Nat.log b n + m`。

Mathlib に該当補題がないので自前で用意する。
`b ^ (log b n + 1) > n` （`Nat.lt_pow_succ_log_self`）を `m` 乗して
`n ^ m < b ^ (m * (log b n + 1))` を得、`Nat.log_lt_of_lt_pow` を使う。
-/
theorem Nat.log_pow_le {b : ℕ} (hb : 1 < b) (n m : ℕ) :
    Nat.log b (n ^ m) ≤ m * Nat.log b n + m := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  rcases Nat.eq_zero_or_pos (n ^ m) with h0 | hpos
  · simp [h0]
  · have h1 : n < b ^ (Nat.log b n + 1) := Nat.lt_pow_succ_log_self hb n
    have hlt : n ^ m < b ^ (m * Nat.log b n + m) := by
      calc n ^ m < (b ^ (Nat.log b n + 1)) ^ m := Nat.pow_lt_pow_left h1 hm.ne'
        _ = b ^ ((Nat.log b n + 1) * m) := by rw [← pow_mul]
        _ = b ^ (m * Nat.log b n + m) := by ring_nf
    exact Nat.le_of_lt_succ (Nat.lt_succ_of_lt (Nat.log_lt_of_lt_pow hpos.ne' hlt))

/--
多項式関数の `Nat.log` は O(log n)（v2 §2.8、論文の補助補題）。

`f n ≤ c * n ^ k + c` から `log₂ (f n) ≤ (k + 2) * log₂ n + log₂ c` 程度。
十分大きな `n` では `f n ≤ n ^ (k + 2)` に押し込めるので
`Nat.log 2 (f n) ≤ (k + 2) * Nat.log 2 n` が従う。
-/
theorem natLog_polynomial_is_O_log (f : ℕ → ℕ) (hf : IsPolynomial f) :
    (fun n => (Nat.log 2 (f n) : ℝ)) =O[atTop] (fun n : ℕ => (Nat.log 2 n : ℝ)) := by
  obtain ⟨c, k, hck⟩ := hf
  rw [isBigO_iff]
  refine ⟨2 * (k : ℝ) + 4, ?_⟩
  filter_upwards [eventually_ge_atTop (max c 2)] with n hn
  have hc : c ≤ n := le_trans (le_max_left _ _) hn
  have h2 : 2 ≤ n := le_trans (le_max_right _ _) hn
  -- n ≥ 2 なので log₂ n ≥ 1。これで加法項 (k+2) を吸収できる
  have hlogn1 : 1 ≤ Nat.log 2 n := Nat.log_pos (by norm_num) h2
  -- f n ≤ n ^ (k + 2)
  have hbound : f n ≤ n ^ (k + 2) := by
    refine le_trans (hck n) ?_
    have hnk : 0 < n ^ k := Nat.pow_pos (by omega)
    have h1 : c * n ^ k ≤ n * n ^ k := Nat.mul_le_mul_right _ hc
    have h2' : c ≤ n * n ^ k := le_trans hc (Nat.le_mul_of_pos_right _ hnk)
    calc c * n ^ k + c ≤ n * n ^ k + n * n ^ k := Nat.add_le_add h1 h2'
      _ = 2 * (n * n ^ k) := by ring
      _ ≤ n * (n * n ^ k) := by gcongr
      _ = n ^ (k + 2) := by ring
  -- Nat.log の単調性と Nat.log_pow
  have hlog : Nat.log 2 (f n) ≤ (k + 2) * Nat.log 2 n + (k + 2) := by
    calc Nat.log 2 (f n) ≤ Nat.log 2 (n ^ (k + 2)) := Nat.log_mono_right hbound
      _ ≤ (k + 2) * Nat.log 2 n + (k + 2) := Nat.log_pow_le (by norm_num) n (k + 2)
  have hcast : ((Nat.log 2 (f n) : ℕ) : ℝ) ≤ (2 * (k : ℝ) + 4) * (Nat.log 2 n : ℝ) := by
    have h := (Nat.cast_le (α := ℝ)).mpr hlog
    have h1 : (1 : ℝ) ≤ (Nat.log 2 n : ℝ) := by exact_mod_cast hlogn1
    push_cast at h ⊢
    nlinarith
  rw [Real.norm_natCast, Real.norm_natCast]
  exact hcast

/--
2つの多項式関数の `Nat.log` の差は O(log n)（v2 §2.8）。

v2 の signature は `Int.natAbs (Int.log 2 (f n) - Int.log 2 (g n))` だが、
Mathlib の `IsBigO` はノルム経由（ℝ 上 `‖·‖ = |·|`）なので
`natAbs` ラッパーは不要。ℝ 値の差として述べる。
これが Thm 1 の核心的補題。
-/
theorem natLog_diff_polynomials_is_O_log (f g : ℕ → ℕ)
    (hf : IsPolynomial f) (hg : IsPolynomial g) :
    (fun n => (Nat.log 2 (f n) : ℝ) - (Nat.log 2 (g n) : ℝ))
      =O[atTop] (fun n : ℕ => (Nat.log 2 n : ℝ)) :=
  (natLog_polynomial_is_O_log f hf).sub (natLog_polynomial_is_O_log g hg)

/-- `natAbs` 版（v2 §2.6 の `maxAsymmetryAbs` に合わせた形）。 -/
theorem natAbs_log_diff_is_O_log (f g : ℕ → ℕ)
    (hf : IsPolynomial f) (hg : IsPolynomial g) :
    (fun n => (((Nat.log 2 (f n) : ℤ) - (Nat.log 2 (g n) : ℤ)).natAbs : ℝ))
      =O[atTop] (fun n : ℕ => (Nat.log 2 n : ℝ)) := by
  -- `natAbs` を通した値のノルムは、差のノルムに等しい
  -- `natAbs` を通した実数値は、差の絶対値＝ノルムに等しい
  refine (isBigO_norm_left (f' := fun n : ℕ =>
    (Nat.log 2 (f n) : ℝ) - (Nat.log 2 (g n) : ℝ))).mpr
      (natLog_diff_polynomials_is_O_log f g hf hg) |>.congr_left ?_
  intro n
  rw [Real.norm_eq_abs]
  symm
  -- (z.natAbs : ℝ) = |(z : ℝ)| を ℤ 経由で示す
  rw [← Int.cast_natCast, Int.natCast_natAbs, Int.cast_abs]
  push_cast
  ring

/--
指数関数の対数は少なくとも線形に成長する（v2 §2.8）。

「非対称性が超対数的になりうる」ことの基盤。
-/
theorem log_exponential_is_linear (b : ℕ) (hb : 2 ≤ b) (n : ℕ) :
    n ≤ Nat.log 2 (b ^ n) := by
  calc n = Nat.log 2 (2 ^ n) := (Nat.log_pow (by norm_num) n).symm
    _ ≤ Nat.log 2 (b ^ n) := Nat.log_mono_right (Nat.pow_le_pow_left hb n)

/-- v1 から引き継ぎ: `Real.log` 版の多項式補題。 -/
theorem log_polynomial_is_O_log (f : ℕ → ℕ) (hf : IsPolynomial f) :
    (fun n => Real.log (f n)) =O[atTop] (fun n : ℕ => Real.log n) := by
  obtain ⟨c, k, hck⟩ := hf
  rw [isBigO_iff]
  refine ⟨(k : ℝ) + 2, ?_⟩
  filter_upwards [eventually_ge_atTop (max c 2)] with n hn
  have hc : c ≤ n := le_trans (le_max_left _ _) hn
  have h2 : 2 ≤ n := le_trans (le_max_right _ _) hn
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast le_trans (by norm_num) h2
  have hlogn : 0 ≤ Real.log n := Real.log_nonneg hn1
  have hbound : f n ≤ n ^ (k + 2) := by
    refine le_trans (hck n) ?_
    have hnk : 0 < n ^ k := Nat.pow_pos (by omega)
    have h1 : c * n ^ k ≤ n * n ^ k := Nat.mul_le_mul_right _ hc
    have h2' : c ≤ n * n ^ k := le_trans hc (Nat.le_mul_of_pos_right _ hnk)
    calc c * n ^ k + c ≤ n * n ^ k + n * n ^ k := Nat.add_le_add h1 h2'
      _ = 2 * (n * n ^ k) := by ring
      _ ≤ n * (n * n ^ k) := by gcongr
      _ = n ^ (k + 2) := by ring
  have hfn : (f n : ℝ) ≤ ((n : ℝ)) ^ (k + 2) := by exact_mod_cast hbound
  have hlog : Real.log (f n) ≤ Real.log (((n : ℝ)) ^ (k + 2)) := by
    rcases Nat.eq_zero_or_pos (f n) with h0 | hpos
    · simp [h0]
      positivity
    · exact Real.log_le_log (by exact_mod_cast hpos) hfn
  rw [Real.log_pow] at hlog
  calc ‖Real.log (f n)‖ = |Real.log (f n)| := rfl
    _ ≤ (k + 2 : ℕ) * Real.log n := by
        rw [abs_le]
        refine ⟨?_, hlog⟩
        have : 0 ≤ Real.log (f n) := by
          rcases Nat.eq_zero_or_pos (f n) with h0 | hpos
          · simp [h0]
          · exact Real.log_nonneg (by exact_mod_cast hpos)
        nlinarith [hlogn]
    _ = ((k : ℝ) + 2) * Real.log n := by push_cast; ring
    _ = ((k : ℝ) + 2) * ‖Real.log n‖ := by
        rw [Real.norm_eq_abs, abs_of_nonneg hlogn]

/-- v1 から引き継ぎ: `Real.log` 版の差の補題。 -/
theorem log_diff_polynomials_is_O_log (f g : ℕ → ℕ)
    (hf : IsPolynomial f) (hg : IsPolynomial g) :
    (fun n => Real.log (f n) - Real.log (g n)) =O[atTop] (fun n : ℕ => Real.log n) :=
  (log_polynomial_is_O_log f hf).sub (log_polynomial_is_O_log g hg)
