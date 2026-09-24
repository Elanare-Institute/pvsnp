/-
# 実行テスト（v3 指示書 §11「実行テストの最低ライン」）

`native_decide` は `Lean.ofReduceBool` 公理が混入するので使わない。
`decide` / `rfl` のみで検証する。
-/
import DirectionalAsymmetry.Concrete.Prefix

open Prog Encoding

namespace ExecTest

/-! ## 玩具の relation: `rel x w := (w = [true])` -/

/-- 検証器: `enc x w ↦ [w = [true]]` -/
def V0 : Prog := Prog.comp Prog.snd (Prog.eqConst [true])

/-- `Pref` の decider: `enc (enc x u) v ↦ [u = [] ∨ u = [true]]` -/
def D0 : Prog := Prog.comp Prog.snd
  (Prog.ite (Prog.eqConst []) (Prog.const [true]) (Prog.eqConst [true]))

/-! ### プリミティブの実行 -/

example : run 10 Prog.id [true, false] = some ([true, false], 5) := by rfl
example : run 10 (Prog.eqConst [true]) [true] = some ([true], 4) := by rfl
example : run 10 (Prog.pair Prog.id (Prog.const [])) [true]
    = some ([true, true, false], 8) := by rfl

/-- `enc` / `dec` の往復。 -/
example : dec (enc [true, false] [true]) = ([true, false], [true]) := by rfl

/-! ### 検証器と decider の実行 -/

/-- `V0` は証拠 `[true]` を受理する。 -/
example : run 30 V0 (enc [true, false] [true]) = some ([true], 13) := by rfl

/-- `V0` は証拠 `[false]` を拒否する。 -/
example : run 30 V0 (enc [true, false] [false]) = some ([false], 13) := by rfl

/-- `D0` は空の接頭辞を受理する。 -/
example : run 30 D0 (enc (enc [true, false] []) []) = some ([true], 18) := by rfl

/-! ### prefix 探索の実行 -/

/--
**探索の実行**: `prefixSearch D0 V0` は入力 `[true,false]` に対して
証拠 `[true]` を返す。
-/
example : run 200 (prefixSearch D0 V0) [true, false] = some ([true], 168) := by rfl

/-- 空入力でも証拠 `[true]` を返す。 -/
example : run 200 (prefixSearch D0 V0) [] = some ([true], 104) := by rfl

/-! ### `run` のステップ数が `Eval` のコストと一致することの確認 -/

/--
健全性より、`run` が返したステップ数は `Eval` のコストと一致する。

`run_sound` は `run fuel P x = some (y, t) → Eval P x y t` なので、
上の `rfl` で得た `t` がそのまま `Eval` のコストになる。
-/
example : Eval (prefixSearch D0 V0) [true, false] [true] 168 :=
  run_sound 200 _ _ _ _ (by rfl)

example : Eval (prefixSearch D0 V0) [] [true] 104 :=
  run_sound 200 _ _ _ _ (by rfl)

example : Eval V0 (enc [true, false] [true]) [true] 13 :=
  run_sound 30 _ _ _ _ (by rfl)

/-- 決定性より、コストは一意。上の 168 以外のコストはありえない。 -/
example (t : ℕ) (h : Eval (prefixSearch D0 V0) [true, false] [true] t) : t = 168 :=
  h.time_unique (run_sound 200 _ _ _ _ (by rfl)) ▸ rfl

end ExecTest
