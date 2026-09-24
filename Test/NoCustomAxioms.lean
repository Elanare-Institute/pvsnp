/-
# 回帰テスト: 主要定理が標準公理のみに依存することの検査

v3 指示書 §11「`#print axioms` の対象がすべて
`[propext, Classical.choice, Quot.sound]` の部分集合」に対応。

v2 では `conjecture_A` / `conjecture_B` が `axiom` として宣言され、
しかもそれらは**矛盾していた**（`Test/Phase0Inconsistency.lean` 参照）。
v3 では独自の `axiom` をゼロにし、予想は `Prop` として仮定に明示する。

標準3公理以外に依存する宣言が下のリストに現れると **ビルドが失敗する**。
-/
import DirectionalAsymmetry

open Lean

namespace DirectionalAsymmetry.Test

/-- Lean/Mathlib の標準公理。 -/
def standardAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

/-- 標準公理以外への依存を集める。 -/
def customAxioms [Monad m] [MonadEnv m] (n : Name) : m (List Name) := do
  let axs ← collectAxioms n
  return axs.toList.filter (fun a => !standardAxioms.contains a)

/--
主要定理（指示書 §11 の `#print axioms` 対象）。

`residualAsym` は `opaque` なのでそれ自体は実装を持たないが、
`thm2` は `residualAsym` の**中身に依存しない**形で述べられており、
`opaque` は公理を導入しない（`Classical.choice` のみ）。
-/
def auditTargets : List Name :=
  [``thm1_a_to_b, ``thm1_b_to_a, ``thm1_c_to_a,
   ``thm1_a_iff_b, ``thm1_a_iff_c,
   ``cor1, ``cor1', ``cor2,
   ``prop1,
   ``pointwise_degenerate,
   ``thm2, ``v2_style_inconsistent,
   -- 中核となる補題も監査対象にする
   ``prefixSearch_polyTime, ``prefixSearch_tcs,
   ``polyTime_of_logBounded, ``logBounded_of_polyTime, ``asym_lower,
   ``Prog.run_sound, ``Prog.Eval.deterministic, ``Prog.Eval.size_le,
   ``p_sub_np, ``inP_of_reduces,
   -- Layer 2
   ``accumulation_identity, ``structuralAsymmetry_eq_log_prod,
   -- v4: 制限された設定（論文 §6.5）
   ``tree_sound, ``gen_sound, ``tree_to_gen,
   ``RestrictedEncoding.decodeCNF_encodeCNF,
   ``bridge_resolution, ``php_unsat,
   ``hakenLB_tree, ``no_polytime_res_solver]

open Elab Command in
/-- 監査を実行する。 -/
elab "run_axiom_audit" : command => do
  let mut bad : List (Name × List Name) := []
  for n in auditTargets do
    let cs ← liftTermElabM (customAxioms n)
    if !cs.isEmpty then
      bad := (n, cs) :: bad
  if !bad.isEmpty then
    throwError "独自公理に依存する宣言がある: {bad}"
  logInfo m!"公理監査 OK: {auditTargets.length} 件がすべて \
    [propext, Classical.choice, Quot.sound] の部分集合"

run_axiom_audit

end DirectionalAsymmetry.Test
