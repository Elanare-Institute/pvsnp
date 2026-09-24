/-
# 鳩の巣原理の式

v4 指示書 §7。

`n+1` 羽の鳩を `n` 個の穴に入れる。充足不能であり、
Haken (1985) により一般 resolution の反証は指数サイズ。
-/
import DirectionalAsymmetry.Restricted.Encoding
import DirectionalAsymmetry.Concrete.Poly

open RestrictedEncoding

/-- 変数 `p(i, j)`: 鳩 `i`（`0 ≤ i ≤ n`）が穴 `j`（`0 ≤ j < n`）に入る。 -/
def phVar (n i j : ℕ) : Var := i * n + j

/-- `phVar n` は（`j < n` の範囲で）単射。 -/
theorem phVar_inj {n i j i' j' : ℕ} (hj : j < n) (hj' : j' < n)
    (h : phVar n i j = phVar n i' j') : i = i' ∧ j = j' := by
  unfold phVar at h
  have hn : 0 < n := by omega
  -- i * n + j を n で割ると商 i、余り j
  have hdiv : ∀ p q : ℕ, q < n → (p * n + q) / n = p := by
    intro p q hq
    have hc : p * n + q = q + n * p := by ring
    rw [hc, Nat.add_mul_div_left _ _ hn, Nat.div_eq_of_lt hq]
    omega
  have hi : i = i' := by
    rw [← hdiv i j hj, ← hdiv i' j' hj', h]
  subst hi
  refine ⟨rfl, ?_⟩
  -- i が等しいので i*n を消去して j = j'
  simp only [Nat.add_right_inj] at h
  exact h

/-- (1) 鳩 `i` はどこかの穴に入る。 -/
def phPigeonClause (n i : ℕ) : Clause :=
  (Finset.range n).image (fun j => Lit.pos (phVar n i j))

/-- (2) 穴 `j` に鳩 `i` と `i'` は同時に入らない。 -/
def phHoleClause (n j i i' : ℕ) : Clause :=
  {Lit.neg (phVar n i j), Lit.neg (phVar n i' j)}

/--
鳩の巣原理の CNF。

`n+1` 羽（`0..n`）の鳩、`n` 個（`0..n-1`）の穴。
-/
def php (n : ℕ) : CNF :=
  ((List.range (n + 1)).map (fun i => phPigeonClause n i)) ++
  ((List.range n).flatMap (fun j =>
    (List.range (n + 1)).flatMap (fun i =>
      ((List.range (n + 1)).filter (fun i' => i < i')).map (fun i' =>
        phHoleClause n j i i'))))

/-- (1) の節は `php n` に属する。 -/
theorem phPigeonClause_mem (n i : ℕ) (hi : i < n + 1) :
    phPigeonClause n i ∈ php n := by
  unfold php
  refine List.mem_append_left _ ?_
  exact List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩

/-- (2) の節は `php n` に属する。 -/
theorem phHoleClause_mem (n j i i' : ℕ) (hj : j < n) (hi : i < n + 1)
    (hi' : i' < n + 1) (hlt : i < i') :
    phHoleClause n j i i' ∈ php n := by
  unfold php
  refine List.mem_append_right _ ?_
  refine List.mem_flatMap.mpr ⟨j, List.mem_range.mpr hj, ?_⟩
  refine List.mem_flatMap.mpr ⟨i, List.mem_range.mpr hi, ?_⟩
  refine List.mem_map.mpr ⟨i', ?_, rfl⟩
  exact List.mem_filter.mpr ⟨List.mem_range.mpr hi', by simpa using hlt⟩

/--
**鳩の巣原理の式は充足不能**。

割り当てが (1) をすべて満たせば、各鳩に穴を一つ選ぶ関数が作れる。
鳩は `n+1` 羽、穴は `n` 個なので、二羽が同じ穴に入る。
それは (2) に反する。
-/
theorem php_unsat (n : ℕ) : ¬ Satisfiable (php n) := by
  rintro ⟨a, ha⟩
  -- 各鳩 i に対し、a が真にする穴 j を選ぶ
  have hchoice : ∀ i : Fin (n + 1), ∃ j : Fin n, a (phVar n i.val j.val) = true := by
    intro i
    have hmem := ha _ (phPigeonClause_mem n i.val i.isLt)
    obtain ⟨l, hl, hlt⟩ := hmem
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hl
    exact ⟨⟨j, List.mem_range.mp (by simpa using hj)⟩, by simpa using hlt⟩
  choose f hf using hchoice
  -- 鳩の巣原理: n+1 > n なので二羽が同じ穴
  have hcard : Fintype.card (Fin n) < Fintype.card (Fin (n + 1)) := by simp
  obtain ⟨p, q, hpq, hfeq⟩ := Fintype.exists_ne_map_eq_of_card_lt f hcard
  -- p < q として一般性を失わない
  rcases Nat.lt_or_ge p.val q.val with hlt | hge
  · have hmem := ha _ (phHoleClause_mem n (f p).val p.val q.val
      (f p).isLt p.isLt q.isLt hlt)
    obtain ⟨l, hl, hlt2⟩ := hmem
    simp only [phHoleClause, Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl
    · simp only [Lit.eval_neg, Bool.not_eq_true'] at hlt2
      rw [hf p] at hlt2; simp at hlt2
    · simp only [Lit.eval_neg, Bool.not_eq_true'] at hlt2
      rw [hfeq] at hlt2
      rw [hf q] at hlt2; simp at hlt2
  · have hlt : q.val < p.val := by
      rcases Nat.lt_or_ge q.val p.val with h | h
      · exact h
      · exact absurd (Fin.ext (by omega)) hpq
    have hmem := ha _ (phHoleClause_mem n (f p).val q.val p.val
      (f p).isLt q.isLt p.isLt hlt)
    obtain ⟨l, hl, hlt2⟩ := hmem
    simp only [phHoleClause, Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl
    · simp only [Lit.eval_neg, Bool.not_eq_true'] at hlt2
      -- 穴は f p = f q なので、鳩 q の選択と一致
      rw [hfeq, hf q] at hlt2; simp at hlt2
    · simp only [Lit.eval_neg, Bool.not_eq_true'] at hlt2
      rw [hf p] at hlt2; simp at hlt2

/-! ## 符号化長の評価 -/

/-- `php n` の変数番号は `(n+1)*n` 未満。 -/
theorem php_var_le (n : ℕ) : ∀ C ∈ php n, ∀ l ∈ C, l.var ≤ (n + 1) * n := by
  intro C hC l hl
  unfold php at hC
  rcases List.mem_append.mp hC with hpig | hhole
  · -- (1) の節
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hpig
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hl
    have hjn : j < n := List.mem_range.mp (by simpa using hj)
    have hin : i < n + 1 := List.mem_range.mp hi
    simp only [Lit.var, phVar]
    calc i * n + j ≤ i * n + n := by omega
      _ ≤ (n + 1) * n := by
          have : i * n + n = (i + 1) * n := by ring
          rw [this]
          exact Nat.mul_le_mul_right _ (by omega)
  · -- (2) の節
    obtain ⟨j, hj, hrest⟩ := List.mem_flatMap.mp hhole
    obtain ⟨i, hi, hrest2⟩ := List.mem_flatMap.mp hrest
    obtain ⟨i', hi', rfl⟩ := List.mem_map.mp hrest2
    have hjn : j < n := List.mem_range.mp hj
    have hin : i < n + 1 := List.mem_range.mp hi
    have hi'n : i' < n + 1 := List.mem_range.mp (List.mem_filter.mp hi').1
    simp only [phHoleClause, Finset.mem_insert, Finset.mem_singleton] at hl
    have hbound : ∀ p : ℕ, p < n + 1 → phVar n p j ≤ (n + 1) * n := by
      intro p hp
      simp only [phVar]
      calc p * n + j ≤ p * n + n := by omega
        _ ≤ (n + 1) * n := by
            have : p * n + n = (p + 1) * n := by ring
            rw [this]
            exact Nat.mul_le_mul_right _ (by omega)
    rcases hl with rfl | rfl
    · simpa [Lit.var] using hbound i hin
    · simpa [Lit.var] using hbound i' hi'n

/-- `php n` の節の大きさは `n` 以下（(1) は `n`、(2) は 2）。 -/
theorem php_card_le (n : ℕ) : ∀ C ∈ php n, C.card ≤ n + 2 := by
  intro C hC
  unfold php at hC
  rcases List.mem_append.mp hC with hpig | hhole
  · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hpig
    unfold phPigeonClause
    refine le_trans (Finset.card_image_le) ?_
    simp
  · obtain ⟨j, hj, hrest⟩ := List.mem_flatMap.mp hhole
    obtain ⟨i, hi, hrest2⟩ := List.mem_flatMap.mp hrest
    obtain ⟨i', hi', rfl⟩ := List.mem_map.mp hrest2
    unfold phHoleClause
    refine le_trans (Finset.card_insert_le _ _) ?_
    simp

/-- `php n` の節数は `(n+1) + n(n+1)(n+1)` 以下。 -/
theorem php_length_le (n : ℕ) : (php n).length ≤ (n + 1) + n * ((n + 1) * (n + 1)) := by
  unfold php
  rw [List.length_append, List.length_map, List.length_range]
  refine Nat.add_le_add_left ?_ _
  rw [List.length_flatMap]
  refine le_trans (List.sum_le_card_nsmul _ ((n + 1) * (n + 1)) ?_) ?_
  · intro y hy
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hy
    rw [List.length_flatMap]
    refine le_trans (List.sum_le_card_nsmul _ (n + 1) ?_) ?_
    · intro z hz
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hz
      rw [List.length_map]
      exact le_trans (List.length_filter_le _ _) (by simp)
    · simp
  · simp

/--
**`php n` の符号化長は `n` の多項式**。

節数・節の大きさ・変数番号がすべて `n` の多項式なので、
`encodeCNF_length_le` から従う。
-/
theorem php_encode_length_le (n : ℕ) :
    (encodeCNF (php n)).length
      ≤ ((n + 1) + n * ((n + 1) * (n + 1)))
        * ((n + 2) * (2 * Nat.log 2 ((n + 1) * n) + 5) + 2) + 1 := by
  refine le_trans (encodeCNF_length_le (php n) ((n + 1) * n) (n + 2)
    (php_var_le n) (php_card_le n)) ?_
  exact Nat.add_le_add_right (Nat.mul_le_mul_right _ (php_length_le n)) 1

/-- 符号化長は `n` の多項式で抑えられる（`PolyBound` の形）。 -/
theorem php_encode_polyBound :
    PolyBound (fun n => (encodeCNF (php n)).length) := by
  -- 上の上界が n の多項式であることを示す
  refine PolyBound.of_le (T := fun n =>
    ((n + 1) + n * ((n + 1) * (n + 1)))
      * ((n + 2) * (2 * ((n + 1) * n) + 5) + 2) + 1) ?_ (fun n => ?_)
  · -- 多項式の積と和
    refine PolyBound.add (PolyBound.mul ?_ ?_) (PolyBound.const 1)
    · refine ⟨2, 3, fun n => ?_⟩
      show n + 1 + n * ((n + 1) * (n + 1)) ≤ 2 * (n + 1) ^ 3
      have h1 : n + 1 ≤ (n + 1) ^ 3 := by
        have : (n + 1) ^ 1 ≤ (n + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
        simpa using this
      have h2 : n * ((n + 1) * (n + 1)) ≤ (n + 1) ^ 3 := by
        have : n * ((n + 1) * (n + 1)) ≤ (n + 1) * ((n + 1) * (n + 1)) :=
          Nat.mul_le_mul_right _ (by omega)
        calc n * ((n + 1) * (n + 1)) ≤ (n + 1) * ((n + 1) * (n + 1)) := this
          _ = (n + 1) ^ 3 := by ring
      omega
    · refine ⟨16, 4, fun n => ?_⟩
      show (n + 2) * (2 * ((n + 1) * n) + 5) + 2 ≤ 16 * (n + 1) ^ 4
      have hb : 2 * ((n + 1) * n) + 5 ≤ 7 * (n + 1) ^ 2 := by
        have : (n + 1) * n ≤ (n + 1) ^ 2 := by
          have : (n + 1) * n ≤ (n + 1) * (n + 1) := Nat.mul_le_mul_left _ (by omega)
          calc (n + 1) * n ≤ (n + 1) * (n + 1) := this
            _ = (n + 1) ^ 2 := by ring
        have h1 : (1:ℕ) ≤ (n + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
        omega
      have hc : (n + 2) * (2 * ((n + 1) * n) + 5) ≤ 2 * (n + 1) * (7 * (n + 1) ^ 2) := by
        refine Nat.mul_le_mul ?_ hb
        omega
      have h1 : (1:ℕ) ≤ (n + 1) ^ 4 := Nat.one_le_pow _ _ (by omega)
      have h3 : (n + 1) ^ 3 ≤ (n + 1) ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
      calc (n + 2) * (2 * ((n + 1) * n) + 5) + 2
          ≤ 2 * (n + 1) * (7 * (n + 1) ^ 2) + 2 := by omega
        _ = 14 * (n + 1) ^ 3 + 2 := by ring
        _ ≤ 14 * (n + 1) ^ 4 + 2 * (n + 1) ^ 4 := by
            have := Nat.mul_le_mul_left 14 h3
            omega
        _ = 16 * (n + 1) ^ 4 := by ring
  · -- log((n+1)n) ≤ (n+1)n
    refine le_trans (php_encode_length_le n) ?_
    refine Nat.add_le_add_right (Nat.mul_le_mul_left _ ?_) 1
    refine Nat.add_le_add_right (Nat.mul_le_mul_left _ ?_) 2
    have := Nat.log_le_self 2 ((n + 1) * n)
    omega

/-- 符号化長は `n` 以上（`n` とともに無限に大きくなる）。 -/
theorem php_encode_length_ge (n : ℕ) : n ≤ (encodeCNF (php n)).length := by
  -- 節数が n 以上で、encList は各節につき 1 ビット以上使う
  have hlen : n ≤ (php n).length := by
    unfold php
    rw [List.length_append, List.length_map, List.length_range]
    omega
  unfold encodeCNF
  rw [encList_length]
  omega
