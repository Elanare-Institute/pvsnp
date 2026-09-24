/-
# 回帰テスト: sorry が混入していないことの検査

テキスト上の grep ではなく `#print axioms` 相当の検査を行い、
証明項レベルで `sorryAx` 非依存であることを確認する。

`sorryAx` に依存する宣言が下のリストに現れると **ビルドが失敗する**。
-/
import DirectionalAsymmetry

open Lean

namespace DirectionalAsymmetry.Test

/-- 定数が `sorryAx` に依存するか。 -/
def dependsOnSorry [Monad m] [MonadEnv m] (n : Name) : m Bool := do
  return (← collectAxioms n).contains ``sorryAx

/-- v3 の全宣言（sorry なしであるべき）。 -/
def mustBeSorryFree : List Name :=
  [-- Phase A: 符号化
   ``BStr, ``Encoding.enc, ``Encoding.dec,
   ``Encoding.dec_enc, ``Encoding.enc_length,
   ``Encoding.dec_fst_length_le, ``Encoding.dec_snd_length_le,
   -- Phase A: プログラムとコスト意味論
   ``Prog, ``Prog.Eval,
   ``Prog.Eval.deterministic, ``Prog.Eval.cost_pos, ``Prog.Eval.size_le,
   ``Prog.Eval.comp_inv, ``Prog.Eval.pair_inv, ``Prog.Eval.ite_inv,
   ``Prog.Eval.loop_inv,
   -- Phase A: インタプリタ
   ``Prog.run, ``Prog.run_sound,
   -- Phase B: 多項式と計算量クラス
   ``PolyBound, ``PolyBound.add, ``PolyBound.mul, ``PolyBound.comp,
   ``PolyTime, ``Decides, ``ClassP, ``NPRel, ``NPRel.lang, ``ClassNP,
   ``PeqNP, ``Reduces, ``IsNPComplete,
   ``polyTime_comp, ``polyTime_pair, ``polyTime_ite,
   ``p_sub_np, ``inP_of_reduces, ``trivialRel,
   -- Phase C: TCS と非対称性
   ``TCS, ``TCS.out, ``TCS.time, ``vtime, ``asym, ``profile, ``LogBounded,
   ``inputsOfSize, ``mem_inputsOfSize, ``inputsOfSize_nonempty,
   ``log_poly_le, ``lt_two_pow_succ_of_log_le,
   ``asym_lower, ``logBounded_of_polyTime,
   ``polyTime_of_logBounded, ``lang_inP_of_polyTime_tcs,
   -- Phase D: prefix 探索と定理1
   ``prefRel, ``prefRel_mem_iff,
   ``initS, ``ext, ``notP, ``prefixSearch,
   ``body_preserves, ``loop_reaches, ``loop_reaches_cost,
   ``prefixSearch_tcs, ``prefixSearch_polyTime,
   ``thm1_a_to_b, ``thm1_b_to_a, ``thm1_c_to_a,
   ``thm1_a_iff_b, ``thm1_a_iff_c,
   ``cor1, ``cor1', ``cor2,
   -- Phase E: スペクトル
   ``Profile, ``AsymClass, ``cls, ``zeroClass,
   ``achievable, ``classOf, ``asymSpectrum,
   ``zeroClass_le, ``cls_le_zero_iff, ``cls_eq_zero_iff,
   ``classOf_eq_some_zero_iff, ``prop1,
   -- Phase F: 退化（ボーナス）
   ``pointwise_degenerate,
   -- Phase G: 分離
   ``residualAsym, ``Unbounded, ``ConjA, ``ConjB,
   ``not_unbounded_of_logBounded, ``thm2,
   ``ConjB_allRel, ``trivialTCS, ``v2_style_inconsistent,
   -- Layer 2（維持）
   ``PartialAssignment, ``solvableRegion, ``localAsymmetry,
   ``structuralAsymmetry, ``accumulation_identity,
   ``structuralAsymmetry_eq_log_prod,
   ``AsymmetryReducingTransform, ``StructureRevealingTransform,
   ``prefixPA, ``prefix_mem_solvable_iff,
   -- 分布
   ``asymDistribution, ``profile_eq_sup,
   -- v4: 命題論理と resolution
   ``Lit, ``Lit.compl, ``Clause, ``CNF, ``Satisfiable,
   ``resStep, ``resStep_eval,
   ``TreeDeriv, ``TreeDeriv.size, ``TreeRefutation, ``tree_sound,
   ``GenRefutation, ``GenRefutation.size, ``gen_sound,
   ``TreeDeriv.postorder, ``TreeDeriv.postorder_valid, ``tree_to_gen,
   ``minTreeSize, ``minGenSize, ``minSize, ``minSize_le, ``refutation_sound,
   -- v4: 符号化
   ``RestrictedEncoding.encNat, ``RestrictedEncoding.encodeCNF,
   ``RestrictedEncoding.decodeCNF, ``RestrictedEncoding.decodeCNF_encodeCNF,
   ``RestrictedEncoding.encodeCNF_injective,
   ``RestrictedEncoding.encodeCNF_length_le,
   -- v4: 設定と定理3
   ``ImplementsSAT, ``not_mem_lang_of_unsat,
   ``ResSolver, ``ResSolver.minSize_le_time,
   ``structAsym, ``bridge_resolution,
   -- v4: 鳩の巣原理と系3
   ``phVar, ``php, ``php_unsat, ``php_encode_length_le,
   ``php_encode_polyBound, ``php_encode_length_ge,
   ``HakenLB, ``hakenLB_tree, ``structAsym_php_ge,
   ``log_lt_div, ``no_polytime_res_solver]

open Elab Command in
/-- 監査を実行する。 -/
elab "run_sorry_audit" : command => do
  let mut bad : List Name := []
  for n in mustBeSorryFree do
    if ← liftTermElabM (dependsOnSorry n) then
      bad := n :: bad
  if !bad.isEmpty then
    throwError "sorry に依存する宣言がある: {bad}"
  logInfo m!"sorry 監査 OK: {mustBeSorryFree.length} 件がすべて sorry-free"

run_sorry_audit

end DirectionalAsymmetry.Test
