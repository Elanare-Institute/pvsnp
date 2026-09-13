/-
# Prop 2: 累積等式 (Accumulation Identity)

v2 指示書 §3.3 に対応（論文 §6.4 Prop 2）。

探索経路に沿った局所非対称性の総和が構造的非対称性に等しい:
  A_struct = Σ a(p_i) = log ∏ |E(p_i)| / |G(p_i)|

「指数的な探索時間 = 局所的な不確実性が深さ方向に累積したもの」
という本論文の中心的洞察を形式化する。
-/
import DirectionalAsymmetry.SearchSpace
import Mathlib.Algebra.BigOperators.Group.Finset.Defs

universe u

/--
探索経路: 部分割当の列。

v2 §3.3 の `SearchPath` は `consecutive` の向きが
`path i.castSucc ∈ extensions (path (Fin.succ i))` と
`path (Fin.succ i) ∈ extensions (path i.castSucc)` の選言になっていたが、
論文 §6.4 は root → leaf の下向き経路を想定しているので
向きを一つに固定する（曖昧さを残すと Prop 2 が述べられない）。
-/
structure SearchPath (n : ℕ) (d : ℕ) where
  /-- 経路上の部分割当の列 -/
  path : Fin (d + 1) → PartialAssignment n
  /-- 連続する点は一手拡張の関係にある（root → leaf 方向） -/
  consecutive : ∀ i : Fin d,
    path i.succ ∈ extensions (path i.castSucc)

/--
経路に沿った構造的非対称性。

各点の局所非対称性の総和として **定義する**。
v2 §3.3 は `structuralAsymmetry` を未定義のまま
`accumulation_identity` で参照していたので、ここで定義を与える。
-/
noncomputable def structuralAsymmetry {n d : ℕ} (φ : (Fin n → Bool) → Prop)
    (sp : SearchPath n d) : ℝ :=
  ∑ i : Fin d, localAsymmetry φ (sp.path i.castSucc)

/--
Proposition 2: 累積等式。

`structuralAsymmetry` を局所非対称性の和として定義したので、
この形では定義展開により成立する（`rfl`）。

**本質的な内容は次の `structuralAsymmetry_eq_log_prod`** の方であり、
「和の形」と「積の対数の形」が一致することが論文の主張
（log の加法性）である。
-/
theorem accumulation_identity {n d : ℕ} (φ : (Fin n → Bool) → Prop)
    (sp : SearchPath n d) :
    structuralAsymmetry φ sp =
      ∑ i : Fin d, localAsymmetry φ (sp.path i.castSucc) := rfl

/--
累積等式の実質的な内容: 局所非対称性の和は、比の積の対数に等しい。

`Σ (log |E(pᵢ)| − log |G(pᵢ)|) = log ∏ (|E(pᵢ)| / |G(pᵢ)|)`

これが論文 §6.4 の主張（log の加法性）。
各 `|E|`, `|G|` が正であることを仮定する（`G` が空だと log 0 = 0 の
junk 値になり等式が崩れるため）。
-/
theorem structuralAsymmetry_eq_log_prod {n d : ℕ} (φ : (Fin n → Bool) → Prop)
    (sp : SearchPath n d)
    (hE : ∀ i : Fin d, 0 < (extensions_finite (sp.path i.castSucc)).toFinset.card)
    (hG : ∀ i : Fin d,
      0 < (extensions_inter_solvable_finite φ (sp.path i.castSucc)).toFinset.card) :
    structuralAsymmetry φ sp =
      Real.log (∏ i : Fin d,
        (((extensions_finite (sp.path i.castSucc)).toFinset.card : ℝ)
          / ((extensions_inter_solvable_finite φ (sp.path i.castSucc)).toFinset.card : ℝ))) := by
  rw [Real.log_prod]
  · unfold structuralAsymmetry localAsymmetry
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Real.log_div]
    · exact_mod_cast (hE i).ne'
    · exact_mod_cast (hG i).ne'
  · intro i _
    have h1 : (0 : ℝ) < (extensions_finite (sp.path i.castSucc)).toFinset.card := by
      exact_mod_cast hE i
    have h2 : (0 : ℝ) <
        (extensions_inter_solvable_finite φ (sp.path i.castSucc)).toFinset.card := by
      exact_mod_cast hG i
    positivity
