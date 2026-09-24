/-
# DirectionalAsymmetry (v3: 具体コストモデル版)

論文 "Computational Directional Asymmetry" rev1 の Lean 4 形式化。

v3 の三原則:
- (P1) 時間は実行から導出する（`Prog` の深い埋め込み + `Eval` のコスト意味論）
- (P2) 最適性は一様に扱う（`profile` は長さ n の最悪ケース）
- (P3) 独自の `axiom` をゼロにする（予想A・Bは `Prop` として仮定に明示）

`thm2` は予想A・Bを**仮定とする含意**であり、P≠NP の証明ではない。
-/
import DirectionalAsymmetry.Main
