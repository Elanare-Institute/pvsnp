/-
# 二進列と対の符号化

v3 指示書 §3.1。

`enc a b` は `a` の各ビット `c` を `[true, c]` に展開し、
区切りの `false` を置いてから `b` をそのまま並べる self-delimiting 符号。
`dec` は全域（不正な入力でも何かを返す）。
-/
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Tactic

/-- 計算の対象となるデータ型: 二進列。 -/
abbrev BStr := List Bool

namespace Encoding

/-- 対の符号化。 -/
def enc (a b : BStr) : BStr := a.flatMap (fun c => [true, c]) ++ false :: b

/-- 全域の復号。`true :: c :: rest` は `a` の 1 ビット、`false :: rest` は区切り。 -/
def dec : BStr → BStr × BStr
  | [] => ([], [])
  | false :: rest => ([], rest)
  | true :: [] => ([], [])
  | true :: c :: rest => let (a, b) := dec rest; (c :: a, b)

@[simp] theorem dec_nil : dec [] = ([], []) := rfl
@[simp] theorem dec_false (rest : BStr) : dec (false :: rest) = ([], rest) := rfl
@[simp] theorem dec_true_cons (c : Bool) (rest : BStr) :
    dec (true :: c :: rest) = ((dec rest).1.cons c, (dec rest).2) := by
  simp [dec]

/-- 符号化と復号は逆。 -/
@[simp] theorem dec_enc (a b : BStr) : dec (enc a b) = (a, b) := by
  induction a with
  | nil => simp [enc]
  | cons c a ih =>
      simp only [enc, List.flatMap_cons, List.cons_append, List.append_assoc] at *
      simp [dec_true_cons, ih]

/-- 符号化の長さは線形。 -/
theorem enc_length (a b : BStr) : (enc a b).length = 2 * a.length + 1 + b.length := by
  have h : (a.flatMap (fun c => [true, c])).length = 2 * a.length := by
    induction a with
    | nil => simp
    | cons c a ih => simp [List.flatMap_cons] at *; omega
  simp [enc, h]
  omega

/-- 復号の第一成分は元より長くならない。 -/
theorem dec_fst_length_le (y : BStr) : (dec y).1.length ≤ y.length := by
  induction y using dec.induct with
  | case1 => simp
  | case2 rest => simp
  | case3 => simp [dec]
  | case4 c rest ih =>
      simp only [dec_true_cons, List.length_cons]
      omega

/-- 復号の第二成分は元より長くならない。 -/
theorem dec_snd_length_le (y : BStr) : (dec y).2.length ≤ y.length := by
  induction y using dec.induct with
  | case1 => simp
  | case2 rest => simp
  | case3 => simp [dec]
  | case4 c rest ih =>
      simp only [dec_true_cons, List.length_cons]
      omega

/-- `enc` は単射（第一成分）。 -/
theorem enc_left_length_le (a b : BStr) : a.length ≤ (enc a b).length := by
  rw [enc_length]; omega

/-- `enc` は単射（第二成分）。 -/
theorem enc_right_length_le (a b : BStr) : b.length ≤ (enc a b).length := by
  rw [enc_length]; omega

/--
`enc a b` は self-delimiting: 前方一致から第一成分と残りが一意に決まる。

`a` の各ビットが `[true, c]` に展開され、区切りの `false` で `a` が
終わるので、`enc a b ++ s` の先頭を読めば `a` が復元できる。
-/
theorem enc_append_inj : ∀ (a a' b b' s t : BStr),
    enc a b ++ s = enc a' b' ++ t → a = a' ∧ b ++ s = b' ++ t := by
  intro a
  induction a with
  | nil =>
      intro a' b b' s t h
      cases a' with
      | nil => simpa [enc] using h
      | cons c a'' => simp [enc] at h
  | cons c a ih =>
      intro a' b b' s t h
      cases a' with
      | nil => simp [enc] at h
      | cons c' a'' =>
          simp only [enc, List.flatMap_cons, List.cons_append, List.append_assoc,
            List.cons.injEq, true_and] at h
          obtain ⟨hcc, hrest⟩ := h
          obtain ⟨ha, hb⟩ := ih a'' b b' s t (by
            simpa [enc, List.append_assoc] using hrest)
          exact ⟨by rw [hcc, ha], hb⟩

end Encoding
