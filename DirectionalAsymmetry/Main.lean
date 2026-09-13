/-
# 全体のインポートと主要宣言の型確認

v2 指示書 §1 の `Main.lean`（全体のインポートと #check）に対応。
-/
import DirectionalAsymmetry.Basic
import DirectionalAsymmetry.TotalCandidateSolver
import DirectionalAsymmetry.Asymmetry
import DirectionalAsymmetry.Complexity
import DirectionalAsymmetry.Characterization
import DirectionalAsymmetry.Auxiliary
import DirectionalAsymmetry.Distribution
import DirectionalAsymmetry.SearchSpace
import DirectionalAsymmetry.Accumulation
import DirectionalAsymmetry.MeaningTransformation
import DirectionalAsymmetry.Separation

/-
以下の `#check` は v2 指示書 §1 が `Main.lean` に要求する
「全体のインポートと #check」に対応する。
ビルドログを汚さないよう `guard_msgs` ではなく
`section` 内で型のみ確認する形にしてある。
-/
section Check

set_option linter.unusedVariables false

variable {α : Type} [Fintype α] [DecidableEq α] [Nonempty α]

-- Layer 1: 定義
noncomputable example := @NPRelation
noncomputable example := @TotalCandidateSolver
noncomputable example := @directionalAsymmetry
noncomputable example := @maxAsymmetry
noncomputable example := @optimalAsymmetry
noncomputable example := @ClassP
noncomputable example := @ClassNP

-- Layer 1: 定理
noncomputable example := @p_sub_np
noncomputable example := @log_bounded_implies_in_p
noncomputable example := @p_eq_np_implies_log_bounded
noncomputable example := @p_ne_np_iff_superlog_asymmetry

-- Layer 2: 定義
noncomputable example := @PartialAssignment
noncomputable example := @solvableRegion
noncomputable example := @localAsymmetry
noncomputable example := @structuralAsymmetry
noncomputable example := @accumulation_identity
noncomputable example := @AsymmetryReducingTransform
noncomputable example := @asymmetryDistribution

-- Layer 3
noncomputable example := @residualStructuralAsymmetry
noncomputable example := @conditional_p_ne_np

end Check
