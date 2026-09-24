/-
# Resolution: 導出規則、木状反証、一般反証、健全性

v4 指示書 §3。

**原則 (P3)**: 定義が空虚でないことを確かめる。
resolution の反証について**健全性**（反証があれば充足不能）を必ず証明する。
これがないと「反証」の定義を誤っても定理3は通ってしまう。
-/
import DirectionalAsymmetry.Restricted.Prop

/--
`x` についての導出。

`C` に `pos x`、`D` に `neg x` があるとき、両方からそれを除いて合わせる。
-/
def resStep (x : Var) (C D : Clause) : Clause :=
  (C.erase (.pos x)) ∪ (D.erase (.neg x))

/--
**導出規則の健全性（中核）**。

`C` と `D` がともに真なら、その導出も真。

`x` の値で場合分けする:
- `a x = true` なら `neg x` は偽なので、`D` を真にするリテラルは
  `neg x` 以外。それは `D.erase (neg x)` に残る。
- `a x = false` なら同様に `C` 側。
-/
theorem resStep_eval {a : Assignment} {x : Var} {C D : Clause}
    (hC : C.eval a) (hD : D.eval a) : (resStep x C D).eval a := by
  obtain ⟨lc, hlcC, hlc⟩ := hC
  obtain ⟨ld, hldD, hld⟩ := hD
  unfold resStep Clause.eval
  by_cases hx : a x = true
  · -- neg x は偽なので ld ≠ neg x
    have hne : ld ≠ Lit.neg x := by
      rintro rfl
      simp [hx] at hld
    exact ⟨ld, Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨hne, hldD⟩), hld⟩
  · -- pos x は偽なので lc ≠ pos x
    have hne : lc ≠ Lit.pos x := by
      rintro rfl
      simp at hlc
      exact hx hlc
    exact ⟨lc, Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hne, hlcC⟩), hlc⟩

/-! ## 木状 resolution -/

/-- 木状 resolution の導出木。根のラベルが導出された節。 -/
inductive TreeDeriv (F : CNF) : Clause → Type where
  | ax  (C : Clause) (h : C ∈ F) : TreeDeriv F C
  | res (x : Var) {C D : Clause}
        (hC : Lit.pos x ∈ C) (hD : Lit.neg x ∈ D)
        (l : TreeDeriv F C) (r : TreeDeriv F D) :
        TreeDeriv F (resStep x C D)

namespace TreeDeriv

/-- 導出木のノード数。 -/
def size {F : CNF} : {C : Clause} → TreeDeriv F C → ℕ
  | _, .ax _ _ => 1
  | _, .res _ _ _ l r => l.size + r.size + 1

theorem size_pos {F : CNF} {C : Clause} (τ : TreeDeriv F C) : 0 < τ.size := by
  cases τ with
  | ax => simp [size]
  | res => simp [size]

/--
導出された節は、`F` を満たす任意の割り当てで真。

導出木に関する帰納法。
-/
theorem eval_of_sat {F : CNF} {a : Assignment} (ha : F.eval a) :
    ∀ {C : Clause}, TreeDeriv F C → C.eval a := by
  intro C τ
  induction τ with
  | ax C h => exact ha C h
  | res x hC hD l r ihl ihr => exact resStep_eval ihl ihr

end TreeDeriv

/-- 木状反証（空節の導出木）。 -/
abbrev TreeRefutation (F : CNF) := TreeDeriv F ∅

/-- **木状反証の健全性**。 -/
theorem tree_sound {F : CNF} (τ : TreeRefutation F) : ¬ Satisfiable F := by
  rintro ⟨a, ha⟩
  exact Clause.eval_empty a (TreeDeriv.eval_of_sat ha τ)

/-! ## 一般 resolution -/

/--
一般 resolution の反証。

節の列で、各節は公理か、それより前の二つの節の導出。最後は空節。
-/
structure GenRefutation (F : CNF) where
  steps : List Clause
  /-- 各段は公理か、前の二段からの導出。 -/
  valid : ∀ i : Fin steps.length,
    steps.get i ∈ F ∨
    ∃ (j k : Fin steps.length) (x : Var),
      j.val < i.val ∧ k.val < i.val ∧
      Lit.pos x ∈ steps.get j ∧ Lit.neg x ∈ steps.get k ∧
      steps.get i = resStep x (steps.get j) (steps.get k)
  /-- 最後は空節。 -/
  ends : steps.getLast? = some ∅

namespace GenRefutation

/-- 反証のサイズ（段数）。 -/
def size {F : CNF} (π : GenRefutation F) : ℕ := π.steps.length

theorem size_pos {F : CNF} (π : GenRefutation F) : 0 < π.size := by
  unfold size
  have he := π.ends
  rcases hl : π.steps with _ | ⟨c, cs⟩
  · rw [hl] at he; simp at he
  · simp

/--
各段は `F` を満たす任意の割り当てで真。

段の添字に関する強帰納法。
-/
theorem eval_of_sat {F : CNF} {a : Assignment} (ha : F.eval a) (π : GenRefutation F) :
    ∀ i : Fin π.steps.length, (π.steps.get i).eval a := by
  -- 添字の値に関する強帰納法
  have key : ∀ n : ℕ, ∀ i : Fin π.steps.length, i.val = n → (π.steps.get i).eval a := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
        intro i hi
        rcases π.valid i with hax | ⟨j, k, x, hj, hk, hpj, hnk, heq⟩
        · exact ha _ hax
        · rw [heq]
          refine resStep_eval (ih j.val (by omega) j rfl) (ih k.val (by omega) k rfl)
  intro i
  exact key i.val i rfl

/-- **一般反証の健全性**。 -/
theorem sound {F : CNF} (π : GenRefutation F) : ¬ Satisfiable F := by
  rintro ⟨a, ha⟩
  -- 最後の段は空節で、それが真になってしまう
  have hlen : 0 < π.steps.length := π.size_pos
  let last : Fin π.steps.length := ⟨π.steps.length - 1, by omega⟩
  have hlast : π.steps.get last = ∅ := by
    have := π.ends
    rw [List.getLast?_eq_getElem?] at this
    simp only [List.getElem?_eq_some_iff] at this
    obtain ⟨h1, h2⟩ := this
    simpa [last, List.get_eq_getElem] using h2
  have := π.eval_of_sat ha last
  rw [hlast] at this
  exact Clause.eval_empty a this

end GenRefutation

/-- **一般反証の健全性**（別名）。 -/
theorem gen_sound {F : CNF} (π : GenRefutation F) : ¬ Satisfiable F := π.sound

/-! ## 木から一般への変換 -/

/--
導出木を後順（post-order）で並べたリスト。

各ノードの子は、そのノードより前に現れる。
-/
def TreeDeriv.postorder {F : CNF} : {C : Clause} → TreeDeriv F C → List Clause
  | C, .ax _ _ => [C]
  | _, @TreeDeriv.res _ x C D _hC _hD l r =>
      l.postorder ++ r.postorder ++ [resStep x C D]

theorem TreeDeriv.postorder_length {F : CNF} :
    ∀ {C : Clause} (τ : TreeDeriv F C), τ.postorder.length = τ.size
  | _, .ax _ _ => by simp [postorder, size]
  | _, @TreeDeriv.res _ x C D hC hD l r => by
      simp only [postorder, size, List.length_append, List.length_singleton,
        postorder_length l, postorder_length r]

/-- 後順リストの最後は根のラベル。 -/
theorem TreeDeriv.postorder_getLast {F : CNF} :
    ∀ {C : Clause} (τ : TreeDeriv F C), τ.postorder.getLast? = some C
  | _, .ax C h => by simp [postorder]
  | _, @TreeDeriv.res _ x C D hC hD l r => by
      simp only [postorder, List.getLast?_append, List.getLast?_singleton]
      rfl

/-- 後順リストは空でない。 -/
theorem TreeDeriv.postorder_ne_nil {F : CNF} {C : Clause} (τ : TreeDeriv F C) :
    τ.postorder ≠ [] := by
  intro h
  have := τ.postorder_getLast
  rw [h] at this
  simp at this

/-!
## 木から一般への変換

`GenRefutation.valid` は `Fin` の添字で「前の二段」を指すが、
添字の付け替えは扱いにくい。そこで「その段より前の段全体（`take i`）に
属する」という形の同値な条件を経由する。
-/

/-- `steps` の各段が、公理か、**それより前の段**からの導出であること。 -/
def GenValidOn (F : CNF) (steps : List Clause) : Prop :=
  ∀ i : ℕ, ∀ h : i < steps.length,
    steps[i] ∈ F ∨
    ∃ (x : Var) (C D : Clause),
      C ∈ steps.take i ∧ D ∈ steps.take i ∧
      Lit.pos x ∈ C ∧ Lit.neg x ∈ D ∧ steps[i] = resStep x C D

/-- 後ろに段を足しても、前半の正当性は保たれる。 -/
theorem genValidOn_append {F : CNF} {pre post : List Clause}
    (hpre : GenValidOn F pre)
    (hpost : ∀ i : ℕ, ∀ h : i < post.length,
      post[i] ∈ F ∨
      ∃ (x : Var) (C D : Clause),
        C ∈ pre ++ post.take i ∧ D ∈ pre ++ post.take i ∧
        Lit.pos x ∈ C ∧ Lit.neg x ∈ D ∧ post[i] = resStep x C D) :
    GenValidOn F (pre ++ post) := by
  intro i hi
  by_cases hlt : i < pre.length
  · -- 前半
    rw [List.getElem_append_left hlt]
    rcases hpre i hlt with hax | ⟨x, C, D, hC, hD, hpC, hnD, heq⟩
    · exact Or.inl hax
    · refine Or.inr ⟨x, C, D, ?_, ?_, hpC, hnD, heq⟩
      · rw [List.take_append]
        exact List.mem_append_left _ hC
      · rw [List.take_append]
        exact List.mem_append_left _ hD
  · -- 後半
    push Not at hlt
    have hi2 : i - pre.length < post.length := by
      simp only [List.length_append] at hi; omega
    rw [List.getElem_append_right hlt]
    rcases hpost (i - pre.length) hi2 with hax | ⟨x, C, D, hC, hD, hpC, hnD, heq⟩
    · exact Or.inl hax
    · refine Or.inr ⟨x, C, D, ?_, ?_, hpC, hnD, heq⟩
      · rw [List.take_append]
        rw [List.take_of_length_le hlt] at *
        exact hC
      · rw [List.take_append]
        rw [List.take_of_length_le hlt] at *
        exact hD

/-- 後順リストの全要素は、その導出木に現れる節。特に根のラベルは最後にある。 -/
theorem TreeDeriv.root_mem_postorder {F : CNF} :
    ∀ {C : Clause} (τ : TreeDeriv F C), C ∈ τ.postorder := by
  intro C τ
  have h := τ.postorder_getLast
  exact List.mem_of_getLast? h

/--
**後順リストは正当**。

各段は公理か、それより前の段からの導出。
根のラベルが最後に来るので、`res` の段では左右の部分木の根が
すでに前に出ている。
-/
theorem TreeDeriv.postorder_valid {F : CNF} :
    ∀ {C : Clause} (τ : TreeDeriv F C), GenValidOn F τ.postorder
  | _, .ax C h => by
      intro i hi
      simp only [postorder, List.length_singleton] at hi
      have : i = 0 := by omega
      subst this
      exact Or.inl (by simpa [postorder] using h)
  | _, @TreeDeriv.res _ x C D hC hD l r => by
      have hl := l.postorder_valid
      have hr := r.postorder_valid
      -- postorder = (l.postorder ++ r.postorder) ++ [resStep x C D]
      have hstruct : (TreeDeriv.res x hC hD l r).postorder
          = (l.postorder ++ r.postorder) ++ [resStep x C D] := by
        simp [postorder]
      rw [hstruct]
      -- 前半 (l ++ r) の正当性
      have hlr : GenValidOn F (l.postorder ++ r.postorder) := by
        refine genValidOn_append hl (fun i hi => ?_)
        rcases hr i hi with hax | ⟨y, A, B, hA, hB, hpA, hnB, heq⟩
        · exact Or.inl hax
        · exact Or.inr ⟨y, A, B, List.mem_append_right _ hA,
            List.mem_append_right _ hB, hpA, hnB, heq⟩
      -- 最後の一段を足す
      refine genValidOn_append hlr (fun i hi => ?_)
      simp only [List.length_singleton] at hi
      have : i = 0 := by omega
      subst this
      refine Or.inr ⟨x, C, D, ?_, ?_, hC, hD, by simp⟩
      · simp only [List.take_zero, List.append_nil]
        exact List.mem_append_left _ l.root_mem_postorder
      · simp only [List.take_zero, List.append_nil]
        exact List.mem_append_right _ r.root_mem_postorder

/-- `GenValidOn`（take 版）から `GenRefutation.valid`（Fin 版）への変換。 -/
theorem genValid_of_genValidOn {F : CNF} {steps : List Clause}
    (h : GenValidOn F steps) :
    ∀ i : Fin steps.length,
      steps.get i ∈ F ∨
      ∃ (j k : Fin steps.length) (x : Var),
        j.val < i.val ∧ k.val < i.val ∧
        Lit.pos x ∈ steps.get j ∧ Lit.neg x ∈ steps.get k ∧
        steps.get i = resStep x (steps.get j) (steps.get k) := by
  intro i
  rcases h i.val i.isLt with hax | ⟨x, C, D, hC, hD, hpC, hnD, heq⟩
  · left; simpa [List.get_eq_getElem] using hax
  · right
    -- take i に属する ⇒ i より前の添字がある
    obtain ⟨jv, hjv, hjget⟩ := List.mem_iff_getElem.mp hC
    obtain ⟨kv, hkv, hkget⟩ := List.mem_iff_getElem.mp hD
    have hjlen : jv < steps.length := by
      have := List.length_take_le i.val steps
      have h2 : (steps.take i.val).length = min i.val steps.length := List.length_take ..
      omega
    have hklen : kv < steps.length := by
      have := List.length_take_le i.val steps
      have h2 : (steps.take i.val).length = min i.val steps.length := List.length_take ..
      omega
    have hjlt : jv < i.val := by
      have := List.length_take_le i.val steps
      have h2 : (steps.take i.val).length = min i.val steps.length := List.length_take ..
      omega
    have hklt : kv < i.val := by
      have := List.length_take_le i.val steps
      have h2 : (steps.take i.val).length = min i.val steps.length := List.length_take ..
      omega
    refine ⟨⟨jv, hjlen⟩, ⟨kv, hklen⟩, x, hjlt, hklt, ?_, ?_, ?_⟩
    · rw [List.get_eq_getElem, ← List.getElem_take (h := hjv), hjget]; exact hpC
    · rw [List.get_eq_getElem, ← List.getElem_take (h := hkv), hkget]; exact hnD
    · rw [List.get_eq_getElem, heq, List.get_eq_getElem, List.get_eq_getElem,
        ← List.getElem_take (h := hjv), ← List.getElem_take (h := hkv), hjget, hkget]

/--
**木状反証から一般反証への変換**。

木を後順で並べればよい。サイズは変わらない（`≤` で述べる）。
-/
theorem tree_to_gen {F : CNF} (τ : TreeRefutation F) :
    ∃ π : GenRefutation F, π.size ≤ τ.size := by
  refine ⟨⟨τ.postorder, genValid_of_genValidOn τ.postorder_valid, τ.postorder_getLast⟩, ?_⟩
  unfold GenRefutation.size
  rw [τ.postorder_length]

/-! ## 最小サイズと証明体系の種類 -/

/-- 木状反証の最小サイズ。反証がなければ `sInf ∅ = 0`。 -/
noncomputable def minTreeSize (F : CNF) : ℕ := sInf { k | ∃ τ : TreeRefutation F, τ.size = k }

/-- 一般反証の最小サイズ。 -/
noncomputable def minGenSize (F : CNF) : ℕ := sInf { k | ∃ π : GenRefutation F, π.size = k }

theorem minTreeSize_le {F : CNF} (τ : TreeRefutation F) : minTreeSize F ≤ τ.size :=
  Nat.sInf_le ⟨τ, rfl⟩

theorem minGenSize_le {F : CNF} (π : GenRefutation F) : minGenSize F ≤ π.size :=
  Nat.sInf_le ⟨π, rfl⟩

/-- 証明体系の種類。 -/
inductive ProofKind where
  | treeLike
  | general
  deriving DecidableEq, Repr

/-- 種類ごとの反証の型。 -/
def Refutation : ProofKind → CNF → Type
  | .treeLike, F => TreeRefutation F
  | .general,  F => GenRefutation F

/-- 反証のサイズ。 -/
def Refutation.size : {S : ProofKind} → {F : CNF} → Refutation S F → ℕ
  | .treeLike, _, τ => TreeDeriv.size τ
  | .general,  _, π => GenRefutation.size π

/-- 最小反証サイズ。 -/
noncomputable def minSize : ProofKind → CNF → ℕ
  | .treeLike, F => minTreeSize F
  | .general,  F => minGenSize F

theorem minSize_le {S : ProofKind} {F : CNF} (π : Refutation S F) :
    minSize S F ≤ π.size := by
  cases S with
  | treeLike => exact minTreeSize_le π
  | general => exact minGenSize_le π

/-- **どの種類でも反証は健全**。 -/
theorem refutation_sound {S : ProofKind} {F : CNF} (π : Refutation S F) :
    ¬ Satisfiable F := by
  cases S with
  | treeLike => exact tree_sound π
  | general => exact gen_sound π

/--
一般反証の最小サイズは木状反証の最小サイズ以下（木状反証が存在するとき）。

木状 resolution は一般 resolution の特別な場合なので、
一般の方が短い反証を持ちうる。
-/
theorem minGenSize_le_minTreeSize {F : CNF} (h : Nonempty (TreeRefutation F)) :
    minGenSize F ≤ minTreeSize F := by
  -- minTreeSize は達成される（ℕ の整列性）
  have hne : { k | ∃ τ : TreeRefutation F, τ.size = k }.Nonempty := by
    obtain ⟨τ⟩ := h
    exact ⟨τ.size, τ, rfl⟩
  obtain ⟨τ, hτ⟩ := Nat.sInf_mem hne
  obtain ⟨π, hπ⟩ := tree_to_gen τ
  calc minGenSize F ≤ π.size := minGenSize_le π
    _ ≤ τ.size := hπ
    _ = minTreeSize F := hτ
