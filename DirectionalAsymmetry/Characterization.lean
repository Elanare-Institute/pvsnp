/-
# Theorem 1: P=NP の非対称性による特性化

v2 指示書 §2.6, §2.7 に対応（論文 §3.3 Thm 1）。

自前 `IsBigO` ではなく Mathlib の `Asymptotics.IsBigO` を使う。
ノルム経由の定義なので非対称性が負値を取る問題が自動的に解決する。
-/
import DirectionalAsymmetry.Complexity
import DirectionalAsymmetry.Auxiliary
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Order.Filter.AtTopBot.Defs

open Asymptotics Filter

universe u

variable {α : Type u} [Fintype α] [DecidableEq α] [Nonempty α]

/-- 「非対称性が O(log n)」であることの述語（可読性のため名前を付ける）。 -/
def LogBoundedAsymmetry {R : NPRelation α} (M : TotalCandidateSolver α R) : Prop :=
  (fun n => (maxAsymmetryAbs M n : ℝ)) =O[atTop] (fun n : ℕ => (Nat.log 2 n : ℝ))

/--
P ⊆ NP。

`ClassP` は「ある `NPRelation R` と TCS が存在して…」という形なので、
その `R` をそのまま `ClassNP` の証人に使えばよい。
-/
theorem p_sub_np : ClassP α ⊆ ClassNP α := by
  rintro L ⟨R, M, hRL, -, -⟩
  exact ⟨R, hRL⟩

/--
Theorem 1 (⟸ 方向): 多項式時間 TCS が存在すれば言語は P に属する。

v2 §2.6 の `log_bounded_implies_in_p` に対応。
判定条件は `TotalCandidateSolver.decide_iff` から従う。
-/
theorem log_bounded_implies_in_p
    (R : NPRelation α) (M : TotalCandidateSolver α R)
    (hPoly : IsPolynomial (worstCaseTime M.solveTime)) :
    R.language ∈ ClassP α :=
  ⟨R, M, rfl, fun x => M.decide_iff x, hPoly⟩

/--
Theorem 1 (⟹ 方向): P = NP ならば、任意の NP relation に対して
多項式時間 TCS が存在し、その非対称性の worst-case が O(log n) に収まる。

v2 §2.6 の `p_eq_np_implies_log_bounded` に対応。
-/
theorem asymmetry_log_bounded_of_polys {R : NPRelation α}
    (M : TotalCandidateSolver α R)
    (hsolve : IsPolynomial (worstCaseTime M.solveTime)) :
    LogBoundedAsymmetry M := by
  have hverify : IsPolynomial (worstCaseVerifyOn M) := worstCaseVerifyOn_poly M
  unfold LogBoundedAsymmetry
  have hsum := (natLog_polynomial_is_O_log _ hsolve).add
               (natLog_polynomial_is_O_log _ hverify)
  refine Asymptotics.IsBigO.trans (g := fun n : ℕ =>
      (Nat.log 2 (worstCaseTime M.solveTime n) : ℝ)
        + (Nat.log 2 (worstCaseVerifyOn M n) : ℝ)) ?_ hsum
  rw [isBigO_iff]
  refine ⟨1, ?_⟩
  filter_upwards with n
  have hb := maxAsymmetryAbs_le M n
  have hb' : (maxAsymmetryAbs M n : ℝ)
      ≤ (Nat.log 2 (worstCaseTime M.solveTime n) : ℝ)
        + (Nat.log 2 (worstCaseVerifyOn M n) : ℝ) := by
    unfold worstCaseTime
    exact_mod_cast hb
  rw [Real.norm_natCast, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  linarith

/--
別の NP relation 上の TCS を、同じ言語を定める relation `R` 上へ移送する。

`ClassP` から得られる TCS は `R` とは別の relation `R'` に対するものなので、
`R` 上の TCS に作り直す必要がある（v2 §2.6 が見落としている点）。
`solveTime` はそのまま引き継ぐので多項式性は保存される。
証拠は `Classical.choose` で取るため `noncomputable`。
-/
noncomputable def transportSolver {R R' : NPRelation α}
    (M' : TotalCandidateSolver α R') (_hL : R'.language = R.language) :
    TotalCandidateSolver α R where
  solve x := haveI := Classical.dec (x ∈ R.language)
             if h : x ∈ R.language then h.choose else []
  solveTime := M'.solveTime
  solveTime_pos := M'.solveTime_pos
  correct x hx := by
    simp only [dif_pos hx]
    exact hx.choose_spec
  solve_short x := by
    by_cases hx : x ∈ R.language
    · simp only [dif_pos hx]
      exact R.witnessShort x _ hx.choose_spec
    · simp [dif_neg hx]

theorem p_eq_np_implies_log_bounded
    (h : ClassP α = ClassNP α) (R : NPRelation α) :
    ∃ M : TotalCandidateSolver α R,
      IsPolynomial (worstCaseTime M.solveTime) ∧ LogBoundedAsymmetry M := by
  -- R.language ∈ ClassNP、よって h より ClassP
  have hmem : R.language ∈ ClassP α := by
    rw [h]; exact ⟨R, rfl⟩
  obtain ⟨R', M', hR'L, -, hpoly'⟩ := hmem
  -- R' 上の TCS を R 上へ移送（solveTime は不変）
  refine ⟨transportSolver M' hR'L, hpoly', ?_⟩
  exact asymmetry_log_bounded_of_polys _ hpoly'

/--
系: P ≠ NP ⟺ ある NP relation が存在して、
任意の多項式時間 TCS の worst-case 非対称性が超対数的。

v2 §2.6 の `p_ne_np_iff_superlog_asymmetry` に対応。
-/
theorem p_ne_np_iff_superlog_asymmetry :
    ClassP α ≠ ClassNP α ↔
    ∃ R : NPRelation α, ∀ M : TotalCandidateSolver α R,
      IsPolynomial (worstCaseTime M.solveTime) → ¬ LogBoundedAsymmetry M := by
  constructor
  · intro hne
    by_contra hcon
    push Not at hcon
    -- 全ての R について、O(log n) 非対称性を持つ多項式時間 TCS が存在する
    refine hne (Set.eq_of_subset_of_subset p_sub_np ?_)
    rintro L ⟨R, rfl⟩
    obtain ⟨M, hpoly, -⟩ := hcon R
    exact log_bounded_implies_in_p R M hpoly
  · rintro ⟨R, hR⟩ heq
    obtain ⟨M, hpoly, hlog⟩ := p_eq_np_implies_log_bounded heq R
    exact hR M hpoly hlog
