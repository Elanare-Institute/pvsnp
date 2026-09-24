/-
# Legacy: v2 抽象層（ビルド対象外）

v3 では `DirectionalAsymmetry/Concrete/` が本体。
この層は **v2 の公理系が矛盾していたことの記録**として残してある
（`Test/Phase0Inconsistency.lean` がこれを参照する）。

v2 の問題点:
1. `solveTime` が抽象フィールドで、計算がタダになる
2. `optimalAsymmetry` が各点 `iInf` で退化する
3. `conjecture_A` / `conjecture_B` が `axiom` かつ**矛盾している**
-/
import Legacy.Main
