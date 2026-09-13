/-
# 回帰テスト: 定義層に sorry が混入していないことの検査

Layer 1 の最低要件は「`def`/`structure` が sorry なしで型チェックを通ること」
（指示書 §5.3, §6）。テキスト上の grep ではなく `#print axioms` 相当の
検査を行い、証明項レベルで `sorryAx` 非依存であることを確認する。

`sorryAx` に依存する宣言が下の第1リストに現れると **ビルドが失敗する**。
-/
import DirectionalAsymmetry

open Lean

namespace DirectionalAsymmetry.Test

/-- 定数が `sorryAx` に依存するか。 -/
def dependsOnSorry [Monad m] [MonadEnv m] (n : Name) : m Bool := do
  return (← collectAxioms n).contains ``sorryAx

/-- sorry なしであるべき宣言（定義層 + 証明済み定理）。 -/
def mustBeSorryFree : List Name :=
  [-- Layer 1 定義層
   ``Language, ``IsPolynomial,
   ``inputsOfSize, ``inputsOfSize_nonempty, ``mem_inputsOfSize,
   ``witnessesUpTo, ``mem_witnessesUpTo, ``witnessesUpTo_nonempty,
   ``inputsOfSizePairs, ``inputsOfSizePairs_nonempty,
   ``NPRelation, ``NPRelation.language, ``TotalCandidateSolver,
   ``NPRelation.bruteForceSolver,
   ``directionalAsymmetry, ``directionalAsymmetryReal,
   ``maxAsymmetry, ``maxAsymmetryAbs, ``optimalAsymmetry,
   ``worstCaseVerifyOn, ``worstCaseTime,
   ``TotalCandidateSolver.decide, ``ClassP, ``ClassNP,
   -- Layer 1 証明済み定理
   ``TotalCandidateSolver.decide_iff,
   ``optimalAsymmetry_le,
   ``maxAsymmetry_le_log_worstCaseTime,
   ``neg_log_le_maxAsymmetry,
   ``maxAsymmetryAbs_le,
   ``worstCaseVerifyOn_poly,
   ``p_sub_np,
   ``log_bounded_implies_in_p,
   ``asymmetry_log_bounded_of_polys,
   ``p_eq_np_implies_log_bounded,
   ``p_ne_np_iff_superlog_asymmetry,
   -- 補助補題（v1 から移植 + 新規）
   ``Nat.log_pow_le,
   ``natLog_polynomial_is_O_log,
   ``natLog_diff_polynomials_is_O_log,
   ``natAbs_log_diff_is_O_log,
   ``log_exponential_is_linear,
   ``log_polynomial_is_O_log,
   ``log_diff_polynomials_is_O_log,
   -- Layer 2 定義層
   ``PartialAssignment, ``solvableRegion, ``extensions,
   ``extensions_finite, ``extensions_inter_solvable_finite,
   ``localAsymmetry, ``solvePreservingRatio,
   ``_root_.SearchPath, ``structuralAsymmetry,
   ``AsymmetryReducingTransform, ``ReducesAsymmetry,
   ``PolyTimeTransformFamily,
   ``asymmetryDistribution, ``statSup, ``statMean, ``statTail,
   ``problemAsymmetry, ``asymmetrySpectrum,
   -- Layer 2 証明済み定理
   ``accumulation_identity,
   ``structuralAsymmetry_eq_log_prod,
   ``reducesAsymmetry_id,
   ``polyTimeTransformFamily_id,
   -- Layer 3: A+B からの導出自体は sorry なし
   ``Superlogarithmic,
   ``not_isBigO_of_superlogarithmic]

/--
`axiom` である Conjecture A/B に依存する宣言。

`sorryAx` ではなく `conjecture_A` / `conjecture_B` に依存する。
これは「未証明の予想を明示的に仮定している」ことの表明であり、
`sorry` による誤魔化しとは区別される。
-/
def dependsOnConjectures : List Name :=
  [``conditional_p_ne_np]

/-- 現時点で未証明の定理（今は空。将来 sorry を置いたらここに追加）。 -/
def knownSorry : List Name := []

open Elab Command in
/-- 上記2リストを検査し、違反があればビルドを失敗させる。 -/
elab "#audit_sorry" : command => do
  let mut errs : Array String := #[]
  for n in mustBeSorryFree do
    if ← dependsOnSorry n then
      errs := errs.push s!"{n} が sorryAx に依存している"
  for n in knownSorry do
    unless ← dependsOnSorry n do
      errs := errs.push s!"{n} に sorryAx がない（証明できたなら期待リストを更新せよ）"
  -- Conjecture 依存の宣言: sorryAx は無いが conjecture_A/B には依存すべき
  for n in dependsOnConjectures do
    if ← dependsOnSorry n then
      errs := errs.push s!"{n} が sorryAx に依存している（axiom のみのはず）"
    let ax ← collectAxioms n
    unless ax.contains ``conjecture_A && ax.contains ``conjecture_B do
      errs := errs.push s!"{n} が conjecture_A/B に依存していない"
  unless errs.isEmpty do
    throwError "sorry 監査に失敗:\n{errs.toList}"
  logInfo s!"sorry 監査 OK: {mustBeSorryFree.length} 件が sorry-free, \
{dependsOnConjectures.length} 件が Conjecture A/B 依存, \
{knownSorry.length} 件が既知の未証明"

#audit_sorry

end DirectionalAsymmetry.Test
