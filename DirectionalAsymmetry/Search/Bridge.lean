/-
# ブリッジ補題: `Pref_R` は solvable region の一般化

v3 指示書 §10 のボーナス。論文 §3.3 の主張を SAT 型の関係について示す。

`prefixSearch` がループ中に保つ不変量
「`enc x u` について `∃ v, R.rel x (u ++ v)`」は、
SAT の可解領域メンバーシップ `prefixPA n u ∈ solvableRegion φ` と
同じものである、というのがこの補題の内容。
-/
import DirectionalAsymmetry.Search.SearchSpace

/--
`u` を先頭から割り当てた部分割当。

`i < |u|` なら `u[i]`、それ以外は未割当（`none`）。
-/
def prefixPA (n : ℕ) (u : List Bool) : PartialAssignment n :=
  fun i => u[i.val]?

/-- `u` の長さ以内の位置は `u` の値で割り当てられる。 -/
theorem prefixPA_lt {n : ℕ} {u : List Bool} (i : Fin n) (h : i.val < u.length) :
    prefixPA n u i = some u[i.val] := by
  simp [prefixPA, List.getElem?_eq_getElem h]

/-- `u` の長さ以上の位置は未割当。 -/
theorem prefixPA_ge {n : ℕ} {u : List Bool} (i : Fin n) (h : u.length ≤ i.val) :
    prefixPA n u i = none := by
  simp [prefixPA, List.getElem?_eq_none_iff.mpr h]

/--
**ブリッジ補題**。

なお指示書 §10 は仮定 `hu : u.length ≤ n` を置いているが、
証明には使わない（`prefixPA` が `u` の範囲外を `none` にするため、
`u` が `n` より長くても主張は成り立つ）。仕様に合わせて引数は残し、
未使用であることを `_hu` で明示する。

`prefixPA n u` が `φ` の可解領域に属する ⟺
`u` を延長して長さ `n` にした割当で `φ` が成り立つものがある。

左辺は探索空間（Layer 2）の概念、右辺は `prefRel`（Layer 1）の
不変量と同じ形。両者が一致することが「`Pref_R` は solvable region の
一般化」の意味である。
-/
theorem prefix_mem_solvable_iff {n : ℕ} (φ : (Fin n → Bool) → Prop)
    (u : List Bool) (_hu : u.length ≤ n) :
    prefixPA n u ∈ solvableRegion φ ↔
      ∃ x : Fin n → Bool, (∀ i : Fin n, ∀ h : i.val < u.length,
        x i = u[i.val]) ∧ φ x := by
  constructor
  · rintro ⟨x, hext, hφ⟩
    refine ⟨x, fun i h => ?_, hφ⟩
    rcases hext i with hi | hi
    · rw [prefixPA_lt i h] at hi
      exact (Option.some.inj hi).symm
    · rw [prefixPA_lt i h] at hi
      exact absurd hi (by simp)
  · rintro ⟨x, hx, hφ⟩
    refine ⟨x, fun i => ?_, hφ⟩
    by_cases h : i.val < u.length
    · left
      rw [prefixPA_lt i h, hx i h]
    · right
      exact prefixPA_ge i (by omega)

/--
不変量の対応。

`prefixSearch` のループ不変量「`∃ v, R.rel x (u ++ v)`」は、
SAT の場合に `prefixPA n u ∈ solvableRegion φ` と一致する。
-/
theorem solvable_iff_extendable {n : ℕ} (φ : (Fin n → Bool) → Prop)
    (u : List Bool) (hu : u.length ≤ n) :
    prefixPA n u ∈ solvableRegion φ ↔
      ∃ x : Fin n → Bool, (∀ i : Fin n, ∀ h : i.val < u.length,
        x i = u[i.val]) ∧ φ x :=
  prefix_mem_solvable_iff φ u hu
