/-
# CNF と割り当ての BStr 符号化

v4 指示書 §4。v3 の `BStr := List Bool` と対の符号化 `enc` / `dec` を使う。

## 設計

指示書は `decodeCNF (encodeCNF F) = F` を要求する。そこで
**符号化を単射にし、復号を「符号化の逆像を取る」形で定義する**。

- 変数番号は2進で符号化する（指示書の要求。単進だと長さが
  `n` に比例してしまい、鳩の巣原理の式で多項式性が崩れる）。
- 復号は `Classical.choice` を使う（全域で、不正な入力には既定値）。
  DSL のプログラムとしての復号器は不要（`ImplementsSAT` は
  `rel` の外延的な性質としてしか使われない）。
-/
import DirectionalAsymmetry.Restricted.Resolution
import DirectionalAsymmetry.Concrete.Encoding

open Encoding

namespace RestrictedEncoding

/-! ## 自然数の2進符号化 -/

/-- `n` を2進で符号化する（下位ビットから、`n = 0` は空リスト）。 -/
def encNat : ℕ → BStr
  | 0 => []
  | n + 1 => decide ((n + 1) % 2 = 1) :: encNat ((n + 1) / 2)
  decreasing_by omega

/-- 2進符号化の長さは `log₂ n + 1` 以下。 -/
theorem encNat_length_le (n : ℕ) : (encNat n).length ≤ Nat.log 2 n + 1 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
      match n with
      | 0 => simp [encNat]
      | m + 1 =>
          rw [encNat]
          simp only [List.length_cons]
          have hlt : (m + 1) / 2 < m + 1 := by omega
          have hrec := ih ((m + 1) / 2) hlt
          rcases Nat.eq_zero_or_pos ((m + 1) / 2) with h | h
          · -- (m+1)/2 = 0 つまり m = 0
            have hm : m = 0 := by omega
            subst hm
            norm_num [encNat]
          · have hge : 2 ≤ m + 1 := by omega
            have hlog : Nat.log 2 ((m + 1) / 2) + 1 = Nat.log 2 (m + 1) := by
              rw [Nat.log_div_base 2 (m + 1)]
              have h1 : 1 ≤ Nat.log 2 (m + 1) := by
                rw [Nat.le_log_iff_pow_le (by norm_num) (by omega)]
                simpa using hge
              omega
            omega

/-! ## リテラル・節・CNF の符号化

リストの符号化は、要素ごとに「継続ビット `true` + 要素」を置き、
最後に `false` を置く self-delimiting 形式にする。
-/

/-- リテラルの符号化: 符号ビット + 変数番号の2進表現（self-delimiting）。 -/
def encLit (l : Lit) : BStr :=
  match l with
  | .pos v => true :: enc (encNat v) []
  | .neg v => false :: enc (encNat v) []

/-- リストの self-delimiting 符号化。 -/
def encList {α : Type} (f : α → BStr) : List α → BStr
  | [] => [false]
  | a :: as => true :: (f a ++ encList f as)

/-- 節の符号化（`Finset` なので `toList` 経由。順序は `toList` が決める）。 -/
noncomputable def encClause (C : Clause) : BStr := encList encLit C.toList

/-- CNF の符号化。 -/
noncomputable def encodeCNF (F : CNF) : BStr := encList encClause F

/-! ## 復号

`encodeCNF` の逆像を取る形で定義する。単射性は使わず、
「`encodeCNF F` の形なら `F` を返す」ことだけを保証する。
-/

open Classical in
/-- 全域の復号。不正な入力には空の CNF を返す。 -/
noncomputable def decodeCNF (x : BStr) : CNF :=
  if h : ∃ F : CNF, encodeCNF F = x then h.choose else []

/-- 割り当ての符号化（変数 `v` の値を位置 `v` に置く）。 -/
def encodeAssign (vars : Finset Var) (a : Assignment) : BStr :=
  (List.range (vars.sup id + 1)).map a

/-- 全域の復号。範囲外は `false`。 -/
def decodeAssign (w : BStr) : Assignment :=
  fun v => w.getD v false

/-! ## 往復補題 -/

/-- `encList` も前方一致から一意（終端の `false` があるため）。 -/
theorem encList_prefix_inj {α : Type} {f : α → BStr}
    (hpre : ∀ a b : α, ∀ s t : BStr, f a ++ s = f b ++ t → a = b ∧ s = t) :
    ∀ (l1 l2 : List α) (s t : BStr),
      encList f l1 ++ s = encList f l2 ++ t → l1 = l2 ∧ s = t := by
  intro l1
  induction l1 with
  | nil =>
      intro l2 s t h
      cases l2 with
      | nil => simpa [encList] using h
      | cons b bs => simp [encList] at h
  | cons a as ih =>
      intro l2 s t h
      cases l2 with
      | nil => simp [encList] at h
      | cons b bs =>
          simp only [encList, List.cons_append, List.append_assoc,
            List.cons.injEq, true_and] at h
          obtain ⟨hab, hrest⟩ := hpre a b _ _ h
          obtain ⟨hl, hs⟩ := ih bs s t hrest
          exact ⟨by rw [hab, hl], hs⟩

/--
**復号は符号化の逆**。

`decodeCNF` を逆像で定義したので、単射性を経由せずに直接示せる
（`h.choose` が `encodeCNF · = encodeCNF F` を満たす別の `F'` に
なる可能性は、単射性がないと排除できないので、単射性を使う）。
-/
theorem encList_injective {α : Type} {f : α → BStr}
    (hpre : ∀ a b : α, ∀ s t : BStr, f a ++ s = f b ++ t → a = b ∧ s = t) :
    Function.Injective (encList f) := by
  intro l1 l2 h
  exact (encList_prefix_inj hpre l1 l2 [] [] (by simpa using h)).1

/-- `encNat` は単射。 -/
theorem encNat_injective : Function.Injective encNat := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
      intro n h
      match m, n with
      | 0, 0 => rfl
      | 0, k + 1 => rw [encNat, encNat] at h; simp at h
      | k + 1, 0 => rw [encNat, encNat] at h; simp at h
      | j + 1, k + 1 =>
          rw [encNat, encNat] at h
          simp only [List.cons.injEq] at h
          obtain ⟨hbit, hrest⟩ := h
          have hdiv : (j + 1) / 2 = (k + 1) / 2 := ih _ (by omega) hrest
          have hmod : (j + 1) % 2 = (k + 1) % 2 := by
            simp only [decide_eq_decide] at hbit
            omega
          omega

/-- `encLit` は単射で、しかも前方一致から一意に決まる。 -/
theorem encLit_prefix_inj (a b : Lit) (s t : BStr)
    (h : encLit a ++ s = encLit b ++ t) : a = b ∧ s = t := by
  -- 先頭ビットで符号が決まり、続く enc (encNat v) [] は self-delimiting
  cases a with
  | pos v =>
    cases b with
    | pos w =>
        simp only [encLit, List.cons_append, List.cons.injEq, true_and] at h
        obtain ⟨h1, h2⟩ := enc_append_inj _ _ _ _ _ _ h
        simp only [List.nil_append] at h2
        exact ⟨by rw [encNat_injective h1], h2⟩
    | neg w => simp [encLit] at h
  | neg v =>
    cases b with
    | pos w => simp [encLit] at h
    | neg w =>
        simp only [encLit, List.cons_append, List.cons.injEq, true_and] at h
        obtain ⟨h1, h2⟩ := enc_append_inj _ _ _ _ _ _ h
        simp only [List.nil_append] at h2
        exact ⟨by rw [encNat_injective h1], h2⟩

/-- `encClause` は前方一致から一意。 -/
theorem encClause_prefix_inj (A B : Clause) (s t : BStr)
    (h : encClause A ++ s = encClause B ++ t) : A = B ∧ s = t := by
  unfold encClause at h
  obtain ⟨hl, hs⟩ := encList_prefix_inj encLit_prefix_inj _ _ _ _ h
  refine ⟨?_, hs⟩
  rw [← Finset.toList_toFinset A, ← Finset.toList_toFinset B, hl]

/-- `encodeCNF` は単射。 -/
theorem encodeCNF_injective : Function.Injective encodeCNF :=
  encList_injective encClause_prefix_inj

/-- **往復補題**: 復号は符号化の逆。 -/
@[simp] theorem decodeCNF_encodeCNF (F : CNF) : decodeCNF (encodeCNF F) = F := by
  unfold decodeCNF
  have hex : ∃ G : CNF, encodeCNF G = encodeCNF F := ⟨F, rfl⟩
  rw [dif_pos hex]
  exact encodeCNF_injective hex.choose_spec

/-! ## 長さの評価 -/

/--
CNF の大きさ。

リテラルの出現総数と、変数番号の大きさ（2進の桁数に効く）を合わせた量。
鳩の巣原理の式で多項式になるよう、変数番号の**最大値**を足す。
-/
noncomputable def cnfSize (F : CNF) : ℕ :=
  (F.map (fun C => C.card)).sum + (F.map (fun C => C.sup (fun l => l.var))).sum

/-- リテラルの符号化長は、変数番号の log で抑えられる。 -/
theorem encLit_length (l : Lit) :
    (encLit l).length = 2 * (encNat l.var).length + 2 := by
  cases l <;> simp [encLit, enc_length, Lit.var]

/-- リテラルの符号化長は `2 log₂ v + 4` 以下。 -/
theorem encLit_length_le (l : Lit) :
    (encLit l).length ≤ 2 * Nat.log 2 l.var + 4 := by
  rw [encLit_length]
  have := encNat_length_le l.var
  omega

/-- リストの符号化長は、要素の符号化長の総和 + 要素数 + 1。 -/
theorem encList_length {α : Type} (f : α → BStr) (l : List α) :
    (encList f l).length = (l.map (fun a => (f a).length)).sum + l.length + 1 := by
  induction l with
  | nil => simp [encList]
  | cons a as ih =>
      simp only [encList, List.length_cons, List.length_append, List.map_cons,
        List.sum_cons, ih]
      omega

/--
節の符号化長の上界。

各リテラルは `2 log₂ v + 4` 以下、リテラル数は `C.card`。
変数番号は `B` で抑えられているとする。
-/
theorem encClause_length_le (C : Clause) (B : ℕ)
    (hB : ∀ l ∈ C, l.var ≤ B) :
    (encClause C).length ≤ C.card * (2 * Nat.log 2 B + 5) + 1 := by
  unfold encClause
  rw [encList_length]
  have hsum : (C.toList.map (fun l => (encLit l).length)).sum
      ≤ C.toList.length * (2 * Nat.log 2 B + 4) := by
    refine le_trans (List.sum_le_card_nsmul _ (2 * Nat.log 2 B + 4) ?_) ?_
    · intro y hy
      obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hy
      refine le_trans (encLit_length_le l) ?_
      have := hB l (Finset.mem_toList.mp hl)
      have := Nat.log_mono_right (b := 2) this
      omega
    · simp
  rw [Finset.length_toList] at hsum ⊢
  have hexp : C.card * (2 * Nat.log 2 B + 5)
      = C.card * (2 * Nat.log 2 B + 4) + C.card := by ring
  omega

/-- CNF の符号化長の上界。 -/
theorem encodeCNF_length_le (F : CNF) (B W : ℕ)
    (hB : ∀ C ∈ F, ∀ l ∈ C, l.var ≤ B)
    (hW : ∀ C ∈ F, C.card ≤ W) :
    (encodeCNF F).length ≤ F.length * (W * (2 * Nat.log 2 B + 5) + 2) + 1 := by
  unfold encodeCNF
  rw [encList_length]
  have hsum : (F.map (fun C => (encClause C).length)).sum
      ≤ F.length * (W * (2 * Nat.log 2 B + 5) + 1) := by
    refine le_trans (List.sum_le_card_nsmul _ (W * (2 * Nat.log 2 B + 5) + 1) ?_) ?_
    · intro y hy
      obtain ⟨C, hC, rfl⟩ := List.mem_map.mp hy
      refine le_trans (encClause_length_le C B (hB C hC)) ?_
      have := hW C hC
      have : C.card * (2 * Nat.log 2 B + 5) ≤ W * (2 * Nat.log 2 B + 5) :=
        Nat.mul_le_mul_right _ this
      omega
    · simp
  have : F.length * (W * (2 * Nat.log 2 B + 5) + 1) + F.length
      = F.length * (W * (2 * Nat.log 2 B + 5) + 2) := by ring
  omega

end RestrictedEncoding
