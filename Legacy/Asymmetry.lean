/-
# Def 3, 3': 計算的方向非対称性

v2 指示書 §2.3, §2.4 に対応（論文 §3.2 Def 3, Def 3'）。

A_M(x) = log₂ T_M(x) − log₂ T_V(x, M(x))

v1 からの変更: `solveCost` / `verifyCost` を別引数で取るのをやめ、
`M : TotalCandidateSolver` に統合した。検証される証拠が `M.solve x` に
一意に定まるため、v1 で必要だった `verifyCostOf`（証拠上の最小値を取る
恣意的な選択）が不要になった。
-/
import Legacy.TotalCandidateSolver
import Mathlib.Data.Int.Log
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Order.ConditionallyCompleteLattice.Indexed

universe u

variable {α : Type u} [Fintype α] [DecidableEq α] [Nonempty α]

/--
Definition 3: 計算的方向非対称性。

`A_M(x) = log₂ T_M(x) − log₂ T_V(x, M(x))`

v2 §2.3 は `Int.log 2` と書いているが、`Int.log` は `Semifield` 上の
関数で ℕ には直接適用できない（ℚ や ℝ へのキャストが要る）。
一方 `Int.log_natCast : Int.log b (↑n) = Nat.log b n` が示すとおり、
自然数上では `Int.log` と `Nat.log` は一致する。
よって無駄なキャストを避け `Nat.log 2` を使い、結果を ℤ にキャストする。

ℤ 値なので `sup'`/`iInf` が扱いやすく、
v2 §2.6 の `natAbs` による評価とも整合する。
（実数版は `directionalAsymmetryReal` として別に用意する。）

verifier は M の出力を検査するだけで、accept する必要はない。
NO インスタンスでも `verifyTime` は定義されているので A_M は全域。
-/
def directionalAsymmetry {R : NPRelation α} (M : TotalCandidateSolver α R)
    (x : List α) : ℤ :=
  (Nat.log 2 (M.solveTime x) : ℤ) - (Nat.log 2 (R.verifyTime x (M.solve x)) : ℤ)

/--
実数版の方向非対称性。

v2 §7.1（v1 からの引き継ぎ）の「Real.log で定義し Nat.log に降ろす」
方針に対応する版。`Int.log` 版とは floor の分だけずれる。
-/
noncomputable def directionalAsymmetryReal {R : NPRelation α}
    (M : TotalCandidateSolver α R) (x : List α) : ℝ :=
  Real.logb 2 (M.solveTime x) - Real.logb 2 (R.verifyTime x (M.solve x))

/--
サイズ `n` における worst-case 方向非対称性。

v2 §2.3 は `(hn : (inputsOfSize α n).Nonempty)` を明示引数に取る形だが、
それだと `fun n => maxAsymmetry M n` が `ℕ → ℤ` にならず
`IsBigO` に渡せない（v1 で判明した不具合 A と同型）。
`[Nonempty α]` から非空性を内部で解決し、素直な `ℕ → ℤ` にしている。
-/
def maxAsymmetry {R : NPRelation α} (M : TotalCandidateSolver α R) (n : ℕ) : ℤ :=
  (inputsOfSize α n).sup' (inputsOfSize_nonempty α n)
    (fun x => directionalAsymmetry M x)

/--
`IsBigO` に渡すための ℕ 値版（v2 §2.6 が `.natAbs` を要求する形）。

非対称性は負値を取りうるので絶対値を取る。
-/
def maxAsymmetryAbs {R : NPRelation α} (M : TotalCandidateSolver α R) (n : ℕ) : ℕ :=
  (maxAsymmetry M n).natAbs

/--
Definition 3': 最適非対称性 `A*(x) = inf_M A_M(x)`。

Blum の speed-up 定理により下限は達成されるとは限らないので
`inf`（`iInf`）で定義する。

`TotalCandidateSolver α R` が非空であることは
`NPRelation.bruteForceSolver` により保証済み（v2 §7.5 の落とし穴 5）。
なお ℤ 上の `iInf` は族が下に有界でない場合 junk 値を返すが、
`A_M(x)` が下に有界かどうかは自明でないため、
この定義を使う命題では有界性を仮定に入れる必要がある。
-/
noncomputable def optimalAsymmetry (R : NPRelation α) (x : List α) : ℤ :=
  ⨅ M : TotalCandidateSolver α R, directionalAsymmetry M x

/-- 各 TCS の非対称性は最適非対称性以上（下に有界な場合）。 -/
theorem optimalAsymmetry_le {R : NPRelation α} (M : TotalCandidateSolver α R)
    (x : List α)
    (hbdd : BddBelow (Set.range fun M : TotalCandidateSolver α R =>
      directionalAsymmetry M x)) :
    optimalAsymmetry R x ≤ directionalAsymmetry M x :=
  ciInf_le hbdd M

section Bounds

variable {R : NPRelation α}

/-- 各点の非対称性は solve 側の log で上から押さえられる。 -/
theorem directionalAsymmetry_le (M : TotalCandidateSolver α R) (x : List α) :
    directionalAsymmetry M x ≤ (Nat.log 2 (M.solveTime x) : ℤ) := by
  unfold directionalAsymmetry
  omega

/-- 各点の非対称性は verify 側の log で下から押さえられる。 -/
theorem neg_le_directionalAsymmetry (M : TotalCandidateSolver α R) (x : List α) :
    -(Nat.log 2 (R.verifyTime x (M.solve x)) : ℤ) ≤ directionalAsymmetry M x := by
  unfold directionalAsymmetry
  omega

/--
worst-case 非対称性は、solve 時間の worst-case の log で上から押さえられる。

`Nat.log` の単調性と `Finset.sup` の性質から従う。
-/
theorem maxAsymmetry_le_log_worstCaseTime (M : TotalCandidateSolver α R) (n : ℕ) :
    maxAsymmetry M n ≤ (Nat.log 2 ((inputsOfSize α n).sup M.solveTime) : ℤ) := by
  refine Finset.sup'_le _ _ (fun x hx => ?_)
  refine le_trans (directionalAsymmetry_le M x) ?_
  exact_mod_cast Nat.log_mono_right (Finset.le_sup (f := M.solveTime) hx)

/--
M が出力する証拠に対する worst-case 検証時間。

`M.solve x` の長さが `R.witnessBound n` 以下とは限らない（NO インスタンス
では任意の出力が許される）ので、`inputsOfSizePairs` では捕まえられない。
そこで「サイズ n の入力に対し M の出力を検証する時間」を直接定義する。
-/
def worstCaseVerifyOn (M : TotalCandidateSolver α R) (n : ℕ) : ℕ :=
  (inputsOfSize α n).sup (fun x => R.verifyTime x (M.solve x))

/-- worst-case 非対称性は verify 側の log で下から押さえられる。 -/
theorem neg_log_le_maxAsymmetry (M : TotalCandidateSolver α R) (n : ℕ) :
    -(Nat.log 2 (worstCaseVerifyOn M n) : ℤ) ≤ maxAsymmetry M n := by
  obtain ⟨x, hx⟩ := inputsOfSize_nonempty α n
  refine le_trans ?_ (Finset.le_sup' (f := fun x => directionalAsymmetry M x) hx)
  refine le_trans ?_ (neg_le_directionalAsymmetry M x)
  simp only [neg_le_neg_iff]
  exact_mod_cast Nat.log_mono_right (Finset.le_sup
    (f := fun x => R.verifyTime x (M.solve x)) hx)

/--
worst-case 非対称性の絶対値は、solve 側と verify 側の log の和で押さえられる。

これが Thm 1 (⟹) の核心。両者が多項式なら和の log は O(log n)。
-/
theorem maxAsymmetryAbs_le (M : TotalCandidateSolver α R) (n : ℕ) :
    (maxAsymmetryAbs M n : ℤ)
      ≤ (Nat.log 2 ((inputsOfSize α n).sup M.solveTime) : ℤ)
        + (Nat.log 2 (worstCaseVerifyOn M n) : ℤ) := by
  have h1 := maxAsymmetry_le_log_worstCaseTime M n
  have h2 := neg_log_le_maxAsymmetry M n
  unfold maxAsymmetryAbs
  rw [Int.natCast_natAbs]
  rw [abs_le]
  constructor <;> omega

/--
M が出力する証拠に対する worst-case 検証時間は多項式。

`solve_short`（M の出力は `witnessBound` 以下の長さ）により、
各 `(x, M.solve x)` が `inputsOfSizePairs α n (witnessBound n)` に属するので、
`R.verifyTimePoly` の押さえがそのまま使える。

**この補題が `solve_short` を要求した理由**であり、
これなしでは Thm 1 (⟹) は反例を持つ。
-/
theorem worstCaseVerifyOn_poly (M : TotalCandidateSolver α R) :
    IsPolynomial (worstCaseVerifyOn M) := by
  obtain ⟨c, k, hck⟩ := R.verifyTimePoly
  refine ⟨c, k, fun n => le_trans ?_ (hck n)⟩
  refine Finset.sup_le (fun x hx => ?_)
  have hxlen : x.length = n := mem_inputsOfSize.mp hx
  refine Finset.le_sup' (f := fun p : List α × List α => R.verifyTime p.1 p.2)
    (b := (x, M.solve x)) (Finset.mem_product.mpr ⟨hx, mem_witnessesUpTo.mpr ?_⟩)
  have h := M.solve_short x
  rw [hxlen] at h
  exact h

end Bounds
