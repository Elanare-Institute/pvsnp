/-
# 全体のインポートと主要宣言の型確認（v3）

v3 指示書 §1 の構成に対応。
-/
import DirectionalAsymmetry.Concrete.Encoding
import DirectionalAsymmetry.Concrete.Prog
import DirectionalAsymmetry.Concrete.Interp
import DirectionalAsymmetry.Concrete.Poly
import DirectionalAsymmetry.Concrete.Classes
import DirectionalAsymmetry.Concrete.TCS
import DirectionalAsymmetry.Concrete.Prefix
import DirectionalAsymmetry.Concrete.Characterization
import DirectionalAsymmetry.Concrete.Spectrum
import DirectionalAsymmetry.Concrete.Degeneracy
import DirectionalAsymmetry.Concrete.Separation
import DirectionalAsymmetry.Search.SearchSpace
import DirectionalAsymmetry.Search.Accumulation
import DirectionalAsymmetry.Search.MeaningTransformation
import DirectionalAsymmetry.Search.Bridge
import DirectionalAsymmetry.Distribution

section Check

set_option linter.unusedVariables false

-- Phase A: 計算モデル
noncomputable example := @Prog
noncomputable example := @Prog.Eval
noncomputable example := @Prog.Eval.deterministic
noncomputable example := @Prog.Eval.size_le
noncomputable example := @Prog.run_sound

-- Phase B: 計算量クラス
noncomputable example := @PolyTime
noncomputable example := @ClassP
noncomputable example := @NPRel
noncomputable example := @ClassNP
noncomputable example := @PeqNP
noncomputable example := @IsNPComplete
noncomputable example := @p_sub_np
noncomputable example := @inP_of_reduces

-- Phase C: TCS と非対称性
noncomputable example := @TCS
noncomputable example := @asym
noncomputable example := @profile
noncomputable example := @LogBounded
noncomputable example := @asym_lower
noncomputable example := @logBounded_of_polyTime
noncomputable example := @polyTime_of_logBounded
noncomputable example := @lang_inP_of_polyTime_tcs

-- Phase D: 定理1
noncomputable example := @prefRel
noncomputable example := @prefRel_mem_iff
noncomputable example := @prefixSearch
noncomputable example := @prefixSearch_tcs
noncomputable example := @prefixSearch_polyTime
noncomputable example := @thm1_a_to_b
noncomputable example := @thm1_b_to_a
noncomputable example := @thm1_c_to_a
noncomputable example := @thm1_a_iff_b
noncomputable example := @thm1_a_iff_c
noncomputable example := @cor1
noncomputable example := @cor1'
noncomputable example := @cor2

-- Phase E: スペクトル
noncomputable example := @AsymClass
noncomputable example := @classOf
noncomputable example := @asymSpectrum
noncomputable example := @prop1

-- Phase F: 退化
noncomputable example := @pointwise_degenerate

-- Phase G: 分離
noncomputable example := @ConjA
noncomputable example := @ConjB
noncomputable example := @thm2
noncomputable example := @v2_style_inconsistent

-- Layer 2
noncomputable example := @PartialAssignment
noncomputable example := @solvableRegion
noncomputable example := @accumulation_identity
noncomputable example := @StructureRevealingTransform
noncomputable example := @prefixPA
noncomputable example := @prefix_mem_solvable_iff
noncomputable example := @asymDistribution

end Check
