/-
# SAT を実装する NP 関係

v4 指示書 §5。

v3 の `NPRel` は検証器 `V : Prog` を要求する。CNF の評価器を DSL で
書くのは大仕事なので、v4 では **SAT を実装する NPRel を仮定として受け取る**。

そのような `R` が存在すること（CNF 評価器を `Prog` として書き、
多項式時間を示すこと）はボーナス（§9.1）であり、v4 では扱わない。
-/
import DirectionalAsymmetry.Restricted.Encoding
import DirectionalAsymmetry.Concrete.TCS

open Encoding RestrictedEncoding

/-- `R` が SAT を実装していること。 -/
structure ImplementsSAT (R : NPRel) : Prop where
  rel_iff : ∀ x w, R.rel x w ↔ (decodeCNF x).eval (decodeAssign w)

/--
充足不能な CNF の符号は `R.lang` に属さない。

`ImplementsSAT` から直ちに従う（指示書 §5 の注）。
-/
theorem not_mem_lang_of_unsat {R : NPRel} (hR : ImplementsSAT R) {x : BStr}
    (hx : ¬ Satisfiable (decodeCNF x)) : x ∉ R.lang := by
  rintro ⟨w, hw⟩
  exact hx ⟨decodeAssign w, (hR.rel_iff x w).mp hw⟩
