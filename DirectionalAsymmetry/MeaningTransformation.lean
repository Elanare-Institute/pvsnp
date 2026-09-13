/-
# Def 7: 意味変換 (Asymmetry-Reducing Transformation)

v2 指示書 §3.5 に対応（論文 §7.2 Def 7）。

「意味」とは、解を保つ方向を識別可能にする新しい表現のこと。
例: unit propagation（強制割当の露出）、CDCL（衝突構造の露出）、
LP 緩和（分数構造の露出）。
-/
import DirectionalAsymmetry.SearchSpace

universe u

/--
Definition 7: 非対称性減少変換。

部分割当の表現を変換し、局所非対称性を下げるもの。

v2 §3.5 の `costPoly : IsPolynomial (fun n => cost default)` は
束縛変数 `n` を使っておらず（`cost default` は `n` に依存しない）
意図した多項式性を表していない。仕様も「簡略化」と注記している。

ここでは `n` を構造体パラメータとして固定したうえで、
「コストは部分割当によらず一様な上界 `costBound` を持ち、
`costBound` が `n` の多項式として与えられる」という形にする。
-/
structure AsymmetryReducingTransform (n : ℕ) where
  /-- 部分割当上の変換 -/
  transform : PartialAssignment n → PartialAssignment n
  /-- 変換の計算コスト -/
  cost : PartialAssignment n → ℕ
  /-- コストの一様上界 -/
  costBound : ℕ
  /-- 実際にコストは上界以下 -/
  cost_le : ∀ p, cost p ≤ costBound

/--
変換族が多項式コストであること。

サイズ `n` ごとに変換 `τ n` が与えられるとき、
そのコスト上界が `n` の多項式であることを要求する。
（単一の `n` では「多項式」が意味を持たないので族として述べる。）
-/
def PolyTimeTransformFamily (τ : ∀ n : ℕ, AsymmetryReducingTransform n) : Prop :=
  IsPolynomial (fun n => (τ n).costBound)

/--
変換がある点で非対称性を減少させること。

v2 §3.5 は有限性・非空性の仮定を補う必要があると注記していたが、
`localAsymmetry` を全域関数として定義した（有限性は `Fintype` から自動、
`log 0 = 0` で全域）ため、そのまま述べられる。
-/
def ReducesAsymmetry {n : ℕ} (φ : (Fin n → Bool) → Prop)
    (τ : AsymmetryReducingTransform n) (p : PartialAssignment n) : Prop :=
  localAsymmetry φ (τ.transform p) ≤ localAsymmetry φ p

/-- 恒等変換は（自明に）非対称性を減少させる。コストは 0。 -/
def AsymmetryReducingTransform.id (n : ℕ) : AsymmetryReducingTransform n where
  transform := _root_.id
  cost _ := 0
  costBound := 0
  cost_le _ := le_refl 0

theorem reducesAsymmetry_id {n : ℕ} (φ : (Fin n → Bool) → Prop)
    (p : PartialAssignment n) :
    ReducesAsymmetry φ (AsymmetryReducingTransform.id n) p :=
  le_refl _

/-- 恒等変換の族は多項式コスト。 -/
theorem polyTimeTransformFamily_id :
    PolyTimeTransformFamily AsymmetryReducingTransform.id :=
  ⟨0, 0, fun n => by simp [AsymmetryReducingTransform.id]⟩
