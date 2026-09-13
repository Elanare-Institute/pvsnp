/-
# DirectionalAsymmetry

P vs NP を「方向非対称性」の枠組みで再定式化する論文の
Layer 1–3 の Lean 4 形式化（指示書 v2）。

Layer 1 の目的は定義の整合性確認とステートメントの型チェックであり、
P≠NP に関する数学的主張を支持するものではない。
Layer 3 の Conjecture A/B は `axiom` として宣言されており、
`conditional_p_ne_np` はそれらに依存する条件付きの結果である。
-/
import DirectionalAsymmetry.Main
