/-
# 各点最適値の退化（論文 rev1 §3.2 の Uniformity の注）

v3 指示書 §8（推奨ボーナス）。

入力 `x` の答えを定数としてプログラムに埋め込めば、
`asym M x` は常に `O(log |x|)` になる。これが
「インスタンスごとの最適化」の正体であり、
P = NP か否かに**関係なく**成立する。

したがって定義3' は各点最適値 `inf_M A_M(x)` ではなく、
一様な最悪ケース・プロファイル `g_M` でなければならない。
-/
import DirectionalAsymmetry.Concrete.TCS

open Encoding Prog

/--
**各点最適値の退化**。

任意の `x` について、`asym M x ≤ C(log |x| + 1)` となる TCS `M` が
存在する（`C` は `x` に依存しない）。

構成: `M := ite (eqConst x) (const w) M₀.M`。
`w` は `x ∈ R.lang` なら証拠、そうでなければ `[]`。
-/
theorem pointwise_degenerate (R : NPRel) (M₀ : TCS R) :
    ∃ C : ℕ, ∀ x : BStr, ∃ M : TCS R, asym M x ≤ C * (Nat.log 2 x.length + 1) := by
  classical
  -- 定数 C は R.q の多項式とプリミティブのコストだけで決まる
  -- const w のコストは 1 + |w| ≤ 1 + R.q |x|、eqConst x のコストは 2 + 2|x|
  -- vtime ≥ 1 なので log vtime ≥ 0、よって asym ≤ log (time)
  obtain ⟨cq, kq, hcq⟩ := R.q_poly
  -- time M x = (2 + 2|x|) + (1 + |w|) + 1 ≤ 2|x| + R.q|x| + 5
  set T : ℕ → ℕ := fun n => 2 * n + (cq * (n + 1) ^ kq) + 5 with hT
  have hTpoly : PolyBound T := by
    refine PolyBound.add (PolyBound.add
      (PolyBound.mul (PolyBound.const 2) PolyBound.id) ?_) (PolyBound.const 5)
    exact ⟨cq, kq, fun n => le_refl _⟩
  obtain ⟨C, hC⟩ := log_poly_le hTpoly
  refine ⟨C, fun x => ?_⟩
  -- x の答えを w として埋め込む
  set w : BStr := if h : x ∈ R.lang then h.choose else [] with hw
  have hwshort : w.length ≤ R.q x.length := by
    rw [hw]
    by_cases h : x ∈ R.lang
    · rw [dif_pos h]; exact R.bound _ _ h.choose_spec
    · rw [dif_neg h]; simp
  -- M := ite (eqConst x) (const w) M₀.M
  have hxw : Eval (Prog.ite (Prog.eqConst x) (Prog.const w) M₀.M) x w
      ((2 + x.length + x.length) + (1 + w.length) + 1) :=
    Eval.ite_true (by simpa using Eval.eqConst x x) (Eval.const w x)
  have htotal : ∀ y, ∃ z t, Eval (Prog.ite (Prog.eqConst x) (Prog.const w) M₀.M) y z t := by
    intro y
    by_cases hy : y = x
    · subst hy; exact ⟨w, _, hxw⟩
    · obtain ⟨z, t, he⟩ := M₀.total y
      exact ⟨z, _, Eval.ite_false (Eval.eqConst x y) (by simp [hy]) he⟩
  have hcorrect : ∀ y z t, Eval (Prog.ite (Prog.eqConst x) (Prog.const w) M₀.M) y z t →
      y ∈ R.lang → R.rel y z := by
    intro y z t hev hy
    rcases hev.ite_inv with ⟨tc, tf, hc, hf, -⟩ | ⟨r, tc, tg, hc, hne, hg, -⟩
    · have hyx : y = x := by have := hc.eqConst_inv; simp at this; exact this
      subst hyx
      rw [hf.const_inv, hw, dif_pos hy]
      exact hy.choose_spec
    · exact M₀.correct y z tg hg hy
  have hshort : ∀ y z t, Eval (Prog.ite (Prog.eqConst x) (Prog.const w) M₀.M) y z t →
      z.length ≤ R.q y.length := by
    intro y z t hev
    rcases hev.ite_inv with ⟨tc, tf, hc, hf, -⟩ | ⟨r, tc, tg, hc, hne, hg, -⟩
    · have hyx : y = x := by have := hc.eqConst_inv; simp at this; exact this
      subst hyx
      rw [hf.const_inv]
      exact hwshort
    · exact M₀.short y z tg hg
  set M : TCS R := { M := Prog.ite (Prog.eqConst x) (Prog.const w) M₀.M
                     total := htotal, correct := hcorrect, short := hshort } with hM
  refine ⟨M, ?_⟩
  -- 非対称性の上界
  unfold asym
  have hMtime : M.time x = (2 + x.length + x.length) + (1 + w.length) + 1 :=
    TCS.time_eq (M := M) hxw
  rw [hMtime]
  have h1 : (2 + x.length + x.length) + (1 + w.length) + 1 ≤ T x.length := by
    show _ ≤ 2 * x.length + (cq * (x.length + 1) ^ kq) + 5
    have h := hcq x.length
    have := hwshort
    omega
  have h2 : Nat.log 2 ((2 + x.length + x.length) + (1 + w.length) + 1)
      ≤ C * (Nat.log 2 x.length + 1) :=
    le_trans (Nat.log_mono_right h1) (hC x.length)
  have h2Z : (Nat.log 2 ((2 + x.length + x.length) + (1 + w.length) + 1) : ℤ)
      ≤ (C : ℤ) * ((Nat.log 2 x.length : ℤ) + 1) := by exact_mod_cast h2
  have h3 := Int.natCast_nonneg (Nat.log 2 (vtime R x (M.out x)))
  omega
