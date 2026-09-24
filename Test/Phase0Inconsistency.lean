/-
# Phase 0: v2 公理系の矛盾の実証

v3 指示書 §2.1 に従い、v2 の `axiom conjecture_A` / `axiom conjecture_B` が
自明な relation に適用されたとき `False` を導くかを検証する。

方針: rel ≡ False の自明な NPRelation と、定数出力・solveTime ≡ 1 の TCS を作る。
このとき `maxAsymmetryAbs M n` は定数（実際には 0）なので超対数的ではありえない。
しかし conjecture_B → conjecture_A の連鎖は超対数性を主張する。よって矛盾。
-/
import Legacy.Separation

universe u

open Asymptotics Filter

section
variable {α : Type u} [Fintype α] [DecidableEq α] [Nonempty α]

/-- 自明な NP relation: 証拠を持つ入力が存在しない。 -/
def trivialRelV2 (α : Type u) [Fintype α] [DecidableEq α] [Nonempty α] :
    NPRelation α where
  rel _ _ := False
  decRel _ _ := isFalse (fun h => h)
  verifyTime _ _ := 1
  verifyTime_pos _ _ := Nat.one_pos
  witnessBound _ := 0
  witnessBoundPoly := ⟨0, 0, by intro n; simp⟩
  witnessShort _ _ h := h.elim
  verifyTimePoly := ⟨1, 0, by intro n; simp⟩

/-- 自明な TCS: 常に [] を返し、時間は常に 1。 -/
def trivialSolverV2 (α : Type u) [Fintype α] [DecidableEq α] [Nonempty α] :
    TotalCandidateSolver α (trivialRelV2 α) where
  solve _ := []
  solveTime _ := 1
  solveTime_pos _ := Nat.one_pos
  correct x hx := by
    obtain ⟨w, hw⟩ := hx
    exact hw.elim
  solve_short _ := by simp

/-- 自明な TCS は多項式時間。 -/
theorem trivialSolverV2_poly :
    IsPolynomial (worstCaseTime (α := α) (trivialSolverV2 α).solveTime) := by
  refine ⟨1, 0, fun n => ?_⟩
  unfold worstCaseTime
  simp only [trivialSolverV2]
  exact le_trans (Finset.sup_le fun _ _ => le_refl 1) (by simp)

/-- 自明な TCS の非対称性は恒等的に 0。 -/
theorem trivialSolverV2_asym_zero (n : ℕ) :
    maxAsymmetryAbs (α := α) (trivialSolverV2 α) n = 0 := by
  unfold maxAsymmetryAbs maxAsymmetry directionalAsymmetry
  have : ((inputsOfSize α n).sup' (inputsOfSize_nonempty α n)
      (fun x => ((Nat.log 2 ((trivialSolverV2 α).solveTime x) : ℤ)
        - (Nat.log 2 ((trivialRelV2 α).verifyTime x ((trivialSolverV2 α).solve x)) : ℤ)))) = 0 := by
    refine le_antisymm (Finset.sup'_le _ _ fun x _ => ?_) ?_
    · simp [trivialSolverV2, trivialRelV2]
    · obtain ⟨x, hx⟩ := inputsOfSize_nonempty α n
      refine le_trans ?_ (Finset.le_sup' _ hx)
      simp [trivialSolverV2, trivialRelV2]
  rw [this]
  rfl

/-- 定数 0 の関数は超対数的ではない。 -/
theorem not_superlog_zero : ¬ Superlogarithmic (fun _ : ℕ => (0 : ℝ)) := by
  intro h
  have hfreq := h 0
  have : ∃ᶠ _n : ℕ in atTop, False := by
    refine hfreq.mono ?_
    intro n hn
    simp at hn
  simp at this

/-- **Phase 0 の結論**: v2 の公理系は矛盾している。 -/
theorem v2_axioms_inconsistent : False := by
  -- Bool を具体的なアルファベットとして使う
  have hpoly : IsPolynomial (worstCaseTime (trivialSolverV2 Bool).solveTime) :=
    trivialSolverV2_poly
  -- Conjecture B: 残余構造的非対称性が超対数的
  have hB := conjecture_B (trivialRelV2 Bool) (trivialSolverV2 Bool) hpoly
  -- Conjecture A: 計算的非対称性も超対数的
  have hA := conjecture_A (trivialRelV2 Bool) (trivialSolverV2 Bool) hB
  -- しかし計算的非対称性は恒等的に 0
  have hzero : (fun n => ((maxAsymmetryAbs (trivialSolverV2 Bool) n : ℕ) : ℝ))
      = (fun _ : ℕ => (0 : ℝ)) := by
    funext n
    rw [trivialSolverV2_asym_zero]
    norm_num
  rw [hzero] at hA
  exact not_superlog_zero hA

end

-- Phase 0 の監査: 矛盾がどの公理に依存するかを表示
#print axioms v2_axioms_inconsistent
