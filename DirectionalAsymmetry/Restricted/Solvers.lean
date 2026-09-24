/-
# 制限された設定のソルバー類

v4 指示書 §6.1。

`extract` フィールドが**設定の定義そのもの**である。
具体的な DPLL・CDCL の実装がこの類に入ること（探索木が木状 resolution の
反証になる、節学習が一般 resolution の反証を作る）は、論文では
Beame–Kautz–Sabharwal (2004) を引いて述べている事実であり、
v4 では形式化しない。

分岐の選び方などの内部には一切制約を置かない（`tcs.M` は任意の `Prog`）。
論文の「分岐の選び方には任意の計算を許す」に対応する。
-/
import DirectionalAsymmetry.Restricted.SATRel

open Encoding RestrictedEncoding

/--
設定 `S` のソルバー。

充足不能な入力での実行から、実行時間の定数倍以下のサイズの
`S`-反証が取り出せる TCS。
-/
structure ResSolver (S : ProofKind) (R : NPRel) where
  tcs     : TCS R
  c       : ℕ
  extract : ∀ x, ¬ Satisfiable (decodeCNF x) →
              ∃ π : Refutation S (decodeCNF x), π.size ≤ c * TCS.time tcs x

namespace ResSolver

variable {S : ProofKind} {R : NPRel}

/-- 充足不能な入力では、最小反証サイズが実行時間で抑えられる。 -/
theorem minSize_le_time (M : ResSolver S R) (x : BStr)
    (hx : ¬ Satisfiable (decodeCNF x)) :
    minSize S (decodeCNF x) ≤ M.c * TCS.time M.tcs x := by
  obtain ⟨π, hπ⟩ := M.extract x hx
  exact le_trans (minSize_le π) hπ

end ResSolver
