/-
# Def 4: 非対称性分布とスペクトル

v2 指示書 §3.4 に対応（論文 §4 Def 4, §4.3 Def 4'）。

非対称性 A_M の押し出し測度として分布を定義し、
worst-case / average-case / one-way function / パラメータ化複雑性を
同一分布の異なる統計量として統一する（論文 §4.2）。
-/
import DirectionalAsymmetry.Asymmetry
import DirectionalAsymmetry.Complexity
import Mathlib.MeasureTheory.Measure.Map
import Mathlib.MeasureTheory.Measure.Count
import Mathlib.Algebra.BigOperators.Group.Finset.Defs

universe u

variable {α : Type u} [Fintype α] [DecidableEq α] [Nonempty α]

open MeasureTheory

/--
Definition 4: 非対称性分布（押し出し測度）。

サイズ n のインスタンス上の測度 `μ` を `A_M` で押し出す。
有限アルファベットなので `MeasurableSpace` は離散 (`⊤`) で問題ない。
-/
noncomputable def asymmetryDistribution [MeasurableSpace (List α)]
    {R : NPRelation α} (M : TotalCandidateSolver α R)
    (μ : Measure (List α)) : Measure ℤ :=
  μ.map (fun x => directionalAsymmetry M x)

/--
離散 σ-代数を使った版。

有限アルファベット上のリストは可算なので、離散 σ-代数 (`⊤`) が自然。
この場合 `A_M` は自動的に可測になる。
-/
noncomputable def asymmetryDistributionDiscrete {R : NPRelation α}
    (M : TotalCandidateSolver α R)
    (μ : @Measure (List α) ⊤) : Measure ℤ :=
  @Measure.map (List α) ℤ ⊤ _ (fun x => directionalAsymmetry M x) μ

/-!
### 統計量（論文 §4.1）

分布の統計量として既存の複雑性概念が復元される。
-/

/-- 統計量 `S_n = sup A_M(x)`: worst-case 複雑性に対応。 -/
def statSup {R : NPRelation α} (M : TotalCandidateSolver α R) (n : ℕ) : ℤ :=
  maxAsymmetry M n

/--
統計量 `E_n = E[A_M]`: average-case 複雑性（Levin）に対応。

有限集合上の期待値なので `Finset.sum` で直接定義する
（測度論を経由する必要がない）。
-/
noncomputable def statMean {R : NPRelation α} (M : TotalCandidateSolver α R)
    (μ : List α → ℝ) (n : ℕ) : ℝ :=
  ∑ x ∈ inputsOfSize α n, μ x * (directionalAsymmetry M x : ℝ)

/-- 統計量 `T_n(t) = Pr[A_M > t]`: one-way function の裾に対応。 -/
noncomputable def statTail {R : NPRelation α} (M : TotalCandidateSolver α R)
    (μ : List α → ℝ) (n : ℕ) (t : ℤ) : ℝ :=
  ∑ x ∈ (inputsOfSize α n).filter (fun x => t < directionalAsymmetry M x), μ x

/--
Definition 4': 問題レベルの非対称性（正規化成長率）。

`A*(L) = limsup_n (sup_{|x|=n} A*(x)) / log n`

論文 §4.3。ここでは `M` を固定した版として定義する
（`optimalAsymmetry` 版は下に有界性の議論が要るため）。
-/
noncomputable def problemAsymmetry {R : NPRelation α}
    (M : TotalCandidateSolver α R) : EReal :=
  Filter.limsup (fun n : ℕ => ((maxAsymmetry M n : ℝ) / (Nat.log 2 n : ℝ) : EReal))
    Filter.atTop

/--
非対称性スペクトル `Σ_NP`（論文 §4.3）。

`P = NP ⟺ Σ_NP = {0}`（完全なスペクトル退化）という
再定式化の中心的対象。
-/
def asymmetrySpectrum (α : Type u) [Fintype α] [DecidableEq α] [Nonempty α] :
    Set EReal :=
  { a | ∃ (R : NPRelation α) (M : TotalCandidateSolver α R),
      problemAsymmetry M = a }
