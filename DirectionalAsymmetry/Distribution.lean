/-
# 非対称性分布（論文 §4.1 の定義4）

v3 指示書 §10。具体版の `asym` の押し出し測度として定義し直す。

worst-case / average-case を同一分布の異なる統計量として扱う
（論文 §4.2）。
-/
import DirectionalAsymmetry.Concrete.TCS
import Mathlib.MeasureTheory.Measure.Map
import Mathlib.MeasureTheory.Measure.Count

open MeasureTheory Encoding

/-- `BStr` は可算なので離散 σ-代数を入れる。 -/
instance : MeasurableSpace BStr := ⊤

/--
Definition 4: 非対称性分布（押し出し測度）。

長さ `n` の入力上の測度 `μ` を `asym M` で押し出す。
`asym` は具体コストモデル（`Eval`）から導出された値なので、
v2 の抽象版と違い「タダの計算」が入り込む余地がない。
-/
noncomputable def asymDistribution {R : NPRel} (M : TCS R)
    (μ : Measure BStr) : Measure ℤ :=
  μ.map (asym M)

/-- 一様（計数）測度による分布。 -/
noncomputable def asymDistributionCount {R : NPRel} (M : TCS R) (n : ℕ) : Measure ℤ :=
  asymDistribution M (Measure.count.restrict (inputsOfSize n : Set BStr))

/--
worst-case 非対称性は分布のサポートの上限（= `profile`）。

論文 §4.2 の「worst-case は分布の一統計量」を形式的に確認する。
-/
theorem profile_eq_sup {R : NPRel} (M : TCS R) (n : ℕ) :
    profile M n = (inputsOfSize n).sup' (inputsOfSize_nonempty n) (fun x => asym M x) := rfl

/-- 分布のサポートは `profile` 以下。 -/
theorem asym_le_profile {R : NPRel} (M : TCS R) {x : BStr} {n : ℕ} (hx : x.length = n) :
    asym M x ≤ profile M n := le_profile M hx
