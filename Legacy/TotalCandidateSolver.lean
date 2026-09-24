/-
# Def 1–2: NP relation と Total Candidate Solver

v2 指示書 §2.1, §2.2 に対応（論文 §2 Def 1, §3.1 Def 2）。

v2 の中心的な設計変更: v1 では `Algorithm`（`time : List α → ℕ`）と
`Verifier`（`time : List α → List α → ℕ`）が別構造体で型が合わなかった。
TCS は「入力から候補証拠を出す全域関数」なので、検証側の証拠が
`M.solve x` に一意に定まり、この不整合が解消する。
-/
import Legacy.Basic

universe u

variable {α : Type u}

/--
Definition 1: NP relation。

`rel x w` は「`w` が `x` の証拠である」という関係。
検証の多項式時間性と証拠長の多項式有界性を構造体に内蔵する。
-/
structure NPRelation (α : Type u) [Fintype α] [DecidableEq α] [Nonempty α] where
  /-- 関係 R(x, w) -/
  rel : List α → List α → Prop
  /-- R は決定可能 -/
  decRel : ∀ x w, Decidable (rel x w)
  /-- 検証時間 -/
  verifyTime : List α → List α → ℕ
  /-- 検証時間は正（`Real.log 0 = 0` という junk 値を避ける。v2 §7.2） -/
  verifyTime_pos : ∀ x w, 0 < verifyTime x w
  /-- 入力サイズに対する証拠長の上界 -/
  witnessBound : ℕ → ℕ
  /-- 証拠長の上界は多項式 -/
  witnessBoundPoly : IsPolynomial witnessBound
  /-- 証拠は多項式長に収まる -/
  witnessShort : ∀ x w, rel x w → w.length ≤ witnessBound x.length
  /-- 検証は多項式時間 -/
  verifyTimePoly : IsPolynomial (fun n =>
    (inputsOfSizePairs α n (witnessBound n)).sup' (inputsOfSizePairs_nonempty α n _)
      (fun p => verifyTime p.1 p.2))

attribute [instance] NPRelation.decRel

section

variable [Fintype α] [DecidableEq α] [Nonempty α]

/-- NP relation が定める言語 `L_R = { x | ∃ w, R(x, w) }`。 -/
def NPRelation.language (R : NPRelation α) : Language α :=
  { x | ∃ w, R.rel x w }

@[simp] theorem NPRelation.mem_language {R : NPRelation α} {x : List α} :
    x ∈ R.language ↔ ∃ w, R.rel x w := Iff.rfl

/--
Definition 2: Total Candidate Solver。

常に停止し、YES インスタンスでは valid な証拠を出力する。
NO インスタンスでの出力は任意（`R.rel x (solve x)` が偽になるだけ）。

correctness を YES 方向のみ要求する点が本質的で、これにより
「解く」側の計算が全域関数として扱える。
-/
structure TotalCandidateSolver (α : Type u) [Fintype α] [DecidableEq α] [Nonempty α]
    (R : NPRelation α) where
  /-- 解を求める関数: 入力 → 候補証拠 -/
  solve : List α → List α
  /-- 実行時間 -/
  solveTime : List α → ℕ
  /-- 実行時間は正 -/
  solveTime_pos : ∀ x, 0 < solveTime x
  /-- YES インスタンスでの正当性 -/
  correct : ∀ x, x ∈ R.language → R.rel x (solve x)
  /--
  出力する候補証拠は多項式長に収まる。

  **v2 仕様からの追加（検証で必要性が判明）**:
  この制約がないと Thm 1 (⟹) は **反例を持つ**。
  `R.verifyTimePoly` は長さ `witnessBound n` 以下の証拠に対してしか
  検証時間を縛らないので、NO インスタンスで `solve` が
  極端に長い出力を返すと `verifyTime x (solve x)` が非有界になり、
  非対称性が超対数的に負へ振れてしまう。

  反例（実際に Lean で構成・確認済み）:
  `rel := fun _ _ => False`（YES インスタンス無し、`correct` は空虚に成立）、
  `verifyTime x w := 2 ^ w.length`、`witnessBound := 0`、
  `solve x := List.replicate (2 ^ x.length) true`、`solveTime := 1`。
  このとき `verifyTimePoly` は空虚に成立するが
  `maxAsymmetry M n = -(2 ^ n)` となり `maxAsymmetryAbs` は指数的。

  意味論的にも自然な制約: 証拠は `witnessBound` 以下の長さしか
  意味を持たないので、それより長い出力を返す solver は
  切り詰めればよく、一般性を失わない。
  -/
  solve_short : ∀ x, (solve x).length ≤ R.witnessBound x.length

/--
TCS は必ず存在する（v2 §7.5 の落とし穴 5 への対処）。

`optimalAsymmetry` の `iInf` が空な族の上で発散しないために、
`TotalCandidateSolver α R` が非空であることを示す必要がある。

構成: `Classical.choice` で各 YES インスタンスから証拠を選ぶ
brute-force solver。計算量は度外視（`solveTime` は抽象フィールドなので
何を入れてもよく、ここでは 1 とする）。存在性のみが目的。

`x ∈ R.language` は一般に決定不能（それが NP たる所以）なので
`Classical.dec` を使う。したがって `noncomputable`。
-/
noncomputable def NPRelation.bruteForceSolver (R : NPRelation α) :
    TotalCandidateSolver α R where
  solve x := haveI := Classical.dec (x ∈ R.language)
             if h : x ∈ R.language then h.choose else []
  solveTime _ := 1
  solveTime_pos _ := Nat.one_pos
  correct x hx := by
    simp only [dif_pos hx]
    exact hx.choose_spec
  solve_short x := by
    by_cases hx : x ∈ R.language
    · simp only [dif_pos hx]
      exact R.witnessShort x _ hx.choose_spec
    · simp [dif_neg hx]

instance (R : NPRelation α) : Nonempty (TotalCandidateSolver α R) :=
  ⟨R.bruteForceSolver⟩

end
