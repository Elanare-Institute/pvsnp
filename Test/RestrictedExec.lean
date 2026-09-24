/-
# v4 の実行テスト

v4 指示書 §10 の最低ライン:
- `{ {x}, {¬x} }` の木状反証を手で作り、サイズが 3 であること
- `tree_sound` から充足不能が出ること
- `php 1` / `php 2` の充足不能性

`native_decide` は使わない（v3 と同じ）。
-/
import DirectionalAsymmetry.Restricted.Corollary

namespace RestrictedExecTest

/-! ## 最小の反証: `{ {x}, {¬x} }` -/

/-- 変数 0 についての単位節の対。 -/
def F0 : CNF := [{Lit.pos 0}, {Lit.neg 0}]

/-- `resStep 0 {pos 0} {neg 0} = ∅`。 -/
example : resStep 0 {Lit.pos 0} {Lit.neg 0} = (∅ : Clause) := by decide

/-- 手で作った木状反証: 二つの公理を変数 0 で導出する。 -/
def tau0 : TreeDeriv F0 (resStep 0 {Lit.pos 0} {Lit.neg 0}) :=
  TreeDeriv.res 0 (by decide) (by decide)
    (TreeDeriv.ax {Lit.pos 0} (by decide))
    (TreeDeriv.ax {Lit.neg 0} (by decide))

/-- **サイズは 3**（公理2つ + 導出1つ）。 -/
example : tau0.size = 3 := by decide

/-- `tau0` は空節の導出、すなわち反証（空節との等式で型を合わせる）。 -/
def refut0 : TreeRefutation F0 :=
  have h : resStep 0 {Lit.pos 0} {Lit.neg 0} = (∅ : Clause) := by decide
  cast (by rw [h]) tau0

/-- **健全性から `F0` は充足不能**。 -/
theorem F0_unsat : ¬ Satisfiable F0 := tree_sound refut0

/-- 一般反証にも変換できる。 -/
example : ∃ π : GenRefutation F0, π.size ≤ refut0.size := tree_to_gen refut0

/-! ## 鳩の巣原理 -/

/-- `php 1`（2羽の鳩、1つの穴）は充足不能。 -/
example : ¬ Satisfiable (php 1) := php_unsat 1

/-- `php 2`（3羽の鳩、2つの穴）は充足不能。 -/
example : ¬ Satisfiable (php 2) := php_unsat 2

/-- `php 0`（1羽の鳩、0個の穴）も充足不能（空節を含む）。 -/
example : ¬ Satisfiable (php 0) := php_unsat 0

/-- `php 1` の節の中身を確認（鳩 0 は穴 0 に入る）。 -/
example : phPigeonClause 1 0 = {Lit.pos 0} := by decide

/-- 符号化長は `n` 以上（`n = 2` で確認）。 -/
example : 2 ≤ (RestrictedEncoding.encodeCNF (php 2)).length := php_encode_length_ge 2

/-- `php 1` の節数。 -/
example : (php 1).length = 3 := by decide

/-! ## 符号化の往復 -/

open RestrictedEncoding in
/--
2進符号化: `encNat 5 = [1,0,1]`（下位ビットから）。

`encNat` は整礎再帰なので `decide` では簡約されない。
等式補題で展開する。
-/
example : encNat 5 = [true, false, true] := by
  rw [encNat, encNat, encNat, encNat]; norm_num

open RestrictedEncoding in
/-- 復号は符号化の逆（`F0` で確認）。 -/
example : decodeCNF (encodeCNF F0) = F0 := decodeCNF_encodeCNF F0

end RestrictedExecTest
