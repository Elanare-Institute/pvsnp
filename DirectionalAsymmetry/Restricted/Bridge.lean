/-
# 定義9と定理3: 制限された設定での「橋」

v4 指示書 §6.2。論文 §6.5「Where the Bridge Is a Theorem」。

一般の設定では予想（Conjecture A′）のままの主張が、ソルバーの型を
限定した設定（DPLL 型・節学習型）では**定理**になる。
-/
import DirectionalAsymmetry.Restricted.Solvers

open Encoding RestrictedEncoding

/--
論文の定義9: 証明体系 `S` に相対的な構造的非対称性。

`minSize` が 0 のときも `Nat.log 2 0 = 0` で問題なく定義される。
-/
noncomputable def structAsym (S : ProofKind) (F : CNF) : ℕ := Nat.log 2 (minSize S F)

/-- `log (c * t) ≤ log c + log t + 1`。 -/
theorem log_mul_le (a b : ℕ) : Nat.log 2 (a * b) ≤ Nat.log 2 a + Nat.log 2 b + 1 := by
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · simp
  rcases Nat.eq_zero_or_pos b with rfl | hb
  · simp
  by_contra hcon
  push Not at hcon
  have h2 : 2 ^ (Nat.log 2 (a * b)) ≤ a * b := Nat.pow_log_le_self 2 (by positivity)
  have h3 : a * b < 2 ^ (Nat.log 2 a + 1) * 2 ^ (Nat.log 2 b + 1) :=
    Nat.mul_lt_mul_of_lt_of_lt (Nat.lt_pow_succ_log_self (by norm_num) a)
      (Nat.lt_pow_succ_log_self (by norm_num) b)
  rw [← pow_add] at h3
  have h4 : 2 ^ (Nat.log 2 a + Nat.log 2 b + 2) ≤ 2 ^ (Nat.log 2 (a * b)) :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  have heq : (2:ℕ) ^ (Nat.log 2 a + 1 + (Nat.log 2 b + 1))
      = 2 ^ (Nat.log 2 a + Nat.log 2 b + 2) := by ring_nf
  omega

/--
**定理3**（論文の定理3）。

制限された設定では、構造的非対称性が計算的非対称性の下界を与える
（`O(log n)` の誤差を除いて）。

これが「橋」である: 一般の設定では予想（Conjecture A′）でしかない
「構造的非対称性 → 計算的非対称性」の含意が、ここでは**定理**になる。

証明:
1. `extract` から `minSize S F ≤ c * time M x`。
2. `log` の単調性と `log_mul_le` で `structAsym ≤ log(time) + log c + 1`。
3. v3 の `vtime_log_bound` で `log(vtime) ≤ C'(log|x| + 1)`。
4. `asym = log(time) − log(vtime)` に代入。
-/
theorem bridge_resolution (S : ProofKind) (R : NPRel) (_hR : ImplementsSAT R)
    (M : ResSolver S R) :
    ∃ C : ℕ, ∀ x, ¬ Satisfiable (decodeCNF x) →
      (structAsym S (decodeCNF x) : ℤ) - C * (Nat.log 2 x.length + 1) ≤ asym M.tcs x := by
  -- 検証時間の log 上界（x によらない）
  obtain ⟨Cv, hCv⟩ := vtime_log_bound R M.tcs
  -- 定数は Cv と log c + 1 をまとめたもの
  refine ⟨Cv + Nat.log 2 M.c + 1, fun x hx => ?_⟩
  -- minSize ≤ c * time
  have h1 : minSize S (decodeCNF x) ≤ M.c * TCS.time M.tcs x :=
    M.minSize_le_time x hx
  -- structAsym ≤ log(c) + log(time) + 1
  have h2 : structAsym S (decodeCNF x)
      ≤ Nat.log 2 M.c + Nat.log 2 (TCS.time M.tcs x) + 1 := by
    unfold structAsym
    exact le_trans (Nat.log_mono_right h1) (log_mul_le _ _)
  -- log(vtime) ≤ Cv (log|x| + 1)
  have h3 := hCv x
  -- 整数に持ち上げて結論
  unfold asym
  have h2Z : (structAsym S (decodeCNF x) : ℤ)
      ≤ (Nat.log 2 M.c : ℤ) + (Nat.log 2 (TCS.time M.tcs x) : ℤ) + 1 := by
    exact_mod_cast h2
  have h3Z : (Nat.log 2 (vtime R x (M.tcs.out x)) : ℤ)
      ≤ (Cv : ℤ) * ((Nat.log 2 x.length : ℤ) + 1) := by
    exact_mod_cast h3
  have hlog1 : (1:ℤ) ≤ (Nat.log 2 x.length : ℤ) + 1 := by
    have : (0:ℤ) ≤ (Nat.log 2 x.length : ℤ) := Int.natCast_nonneg _
    omega
  push_cast
  nlinarith [Int.natCast_nonneg (Nat.log 2 M.c)]
