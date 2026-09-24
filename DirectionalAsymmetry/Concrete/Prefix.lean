/-
# prefix relation と prefix 探索

v3 指示書 §6。論文 §3.3 の Pref_R に対応。

定理1（⟹）の実質: P = NP から (prefRel R).lang の decider D を得て、
`prefixSearch D R.V` という**実際の探索アルゴリズム**を構成する。
v2 の `transportSolver`（コストゼロの移送）は使わない。
-/
import DirectionalAsymmetry.Concrete.TCS

open Encoding Prog

/-- `R.q` を単調な多項式 `c(n+1)^k` で押さえる係数。 -/
noncomputable def qConst (R : NPRel) : ℕ := R.q_poly.choose

/-- `R.q` を単調な多項式 `c(n+1)^k` で押さえる指数。 -/
noncomputable def qExp (R : NPRel) : ℕ := R.q_poly.choose_spec.choose

theorem qBound (R : NPRel) (n : ℕ) : R.q n ≤ qConst R * (n + 1) ^ qExp R :=
  R.q_poly.choose_spec.choose_spec n

/-- 押さえる多項式は単調。 -/
theorem qBound_mono (R : NPRel) {m n : ℕ} (h : m ≤ n) :
    qConst R * (m + 1) ^ qExp R ≤ qConst R * (n + 1) ^ qExp R :=
  Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)

/--
prefix relation `Pref_R`。

`y = enc x u` に対し、証拠 `v` は「`u ++ v` が `x` の証拠」を意味する。
したがって `enc x u ∈ (prefRel R).lang ↔ ∃ v, R.rel x (u ++ v)`。
-/
noncomputable def prefRel (R : NPRel) : NPRel where
  rel y v := R.rel (dec y).1 ((dec y).2 ++ v)
  -- enc (enc x u) v ↦ enc x (u ++ v) ↦ R.V
  -- fst で enc x u を取り、そこから x と u を取り出す。
  V := Prog.comp
        (Prog.pair
          (Prog.comp Prog.fst Prog.fst)
          (Prog.comp (Prog.pair (Prog.comp Prog.fst Prog.snd) Prog.snd) Prog.append))
        R.V
  V_poly := polyTime_comp
    (polyTime_pair (polyTime_comp polyTime_fst polyTime_fst)
      (polyTime_comp (polyTime_pair (polyTime_comp polyTime_fst polyTime_snd) polyTime_snd)
        polyTime_append))
    R.V_poly
  V_decides := by
    intro y v out t hev
    obtain ⟨m, tp, tv, hp, hv, -⟩ := hev.comp_inv
    obtain ⟨a, b, ta, tb, ha, hb, hm, -⟩ := hp.pair_inv
    -- a = fst (fst (enc y v)) = (dec y).1
    obtain ⟨m1, t1, t2, h1, h2, -⟩ := ha.comp_inv
    rw [h1.fst_inv, dec_enc] at h2
    rw [h2.fst_inv] at hm
    -- b = append (pair (fst (snd ...)) snd ...) = (dec y).2 ++ v
    obtain ⟨m2, s1, s2, hs1, hs2, -⟩ := hb.comp_inv
    obtain ⟨c1, c2, u1, u2, hc1, hc2, hmc, -⟩ := hs1.pair_inv
    obtain ⟨m3, r1, r2, hr1, hr2, -⟩ := hc1.comp_inv
    rw [hr1.fst_inv, dec_enc] at hr2
    rw [hr2.snd_inv] at hmc
    rw [hc2.snd_inv, dec_enc] at hmc
    subst hmc
    rw [hs2.append_inv, dec_enc] at hm
    subst hm
    exact R.V_decides _ _ _ _ hv
  q := fun n => qConst R * (n + 1) ^ qExp R
  q_poly := ⟨_, _, fun n => le_refl _⟩
  bound := by
    intro y v hrel
    -- |v| ≤ |(dec y).2 ++ v| ≤ R.q |(dec y).1| ≤ c(|(dec y).1|+1)^k ≤ c(|y|+1)^k
    have h1 : ((dec y).2 ++ v).length ≤ R.q (dec y).1.length := R.bound _ _ hrel
    have h2 : R.q (dec y).1.length ≤ qConst R * ((dec y).1.length + 1) ^ qExp R :=
      qBound R _
    have h3 : qConst R * ((dec y).1.length + 1) ^ qExp R
        ≤ qConst R * (y.length + 1) ^ qExp R :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by have := dec_fst_length_le y; omega) _)
    simp only [List.length_append] at h1
    omega

/-- `prefRel` の言語の特徴づけ。 -/
theorem prefRel_mem_iff (R : NPRel) (x u : BStr) :
    enc x u ∈ (prefRel R).lang ↔ ∃ v, R.rel x (u ++ v) := by
  simp only [NPRel.mem_lang, prefRel, dec_enc]

/-! ## prefix 探索プログラム -/

/-- `x ↦ enc x []` -/
def initS : Prog := Prog.pair Prog.id (Prog.const [])

/-- `enc x u ↦ enc x (u ++ [b])` -/
def ext (b : Bool) : Prog :=
  Prog.pair Prog.fst (Prog.comp (Prog.pair Prog.snd (Prog.const [b])) Prog.append)

/-- 真偽を反転する。 -/
def notP : Prog := Prog.ite Prog.id (Prog.const [false]) (Prog.const [true])

/--
prefix 探索。

```
M(x):
  if D(enc x []) ≠ [true] then return []
  s := enc x []
  while V(s) ≠ [true]:
    s := if D(enc x (u ++ [0])) = [true] then enc x (u ++ [0]) else enc x (u ++ [1])
  return snd s
```
-/
def prefixSearch (D V : Prog) : Prog :=
  Prog.ite (Prog.comp initS D)
    (Prog.comp initS
      (Prog.comp (Prog.loop (Prog.comp V notP)
                    (Prog.ite (Prog.comp (ext false) D) (ext false) (ext true)))
                 Prog.snd))
    (Prog.const [])

section ProgLemmas

theorem eval_initS (x : BStr) : ∃ t, Eval initS x (enc x []) t :=
  ⟨_, Eval.pair (Eval.id x) (Eval.const [] x)⟩

/-- `fst` を `enc a b` に適用すると `a` が返る。 -/
theorem eval_fst_enc (a b : BStr) : ∃ t, Eval Prog.fst (enc a b) a t := by
  have h := Eval.fst (enc a b)
  rw [dec_enc] at h
  exact ⟨_, h⟩

/-- `snd` を `enc a b` に適用すると `b` が返る。 -/
theorem eval_snd_enc (a b : BStr) : ∃ t, Eval Prog.snd (enc a b) b t := by
  have h := Eval.snd (enc a b)
  rw [dec_enc] at h
  exact ⟨_, h⟩

/-- `append` を `enc a b` に適用すると `a ++ b` が返る。 -/
theorem eval_append_enc (a b : BStr) : ∃ t, Eval Prog.append (enc a b) (a ++ b) t := by
  have h := Eval.append (enc a b)
  rw [dec_enc] at h
  exact ⟨_, h⟩

theorem eval_ext (b : Bool) (x u : BStr) :
    ∃ t, Eval (ext b) (enc x u) (enc x (u ++ [b])) t := by
  have h1 := eval_fst_enc x u
  have hs := eval_snd_enc x u
  have h3 := eval_append_enc u [b]
  obtain ⟨t1, h1⟩ := h1
  obtain ⟨ts, hs⟩ := hs
  obtain ⟨t3, h3⟩ := h3
  exact ⟨_, Eval.pair h1 (Eval.comp (Eval.pair hs (Eval.const [b] _)) h3)⟩

theorem eval_notP_true (x : BStr) (hx : x = [true]) :
    ∃ t, Eval notP x [false] t := by
  subst hx
  exact ⟨_, Eval.ite_true (Eval.id [true]) (Eval.const [false] [true])⟩

theorem eval_notP_false (x : BStr) (hx : x ≠ [true]) :
    ∃ t, Eval notP x [true] t :=
  ⟨_, Eval.ite_false (Eval.id x) hx (Eval.const [true] x)⟩

theorem polyTime_initS : PolyTime initS := polyTime_pair polyTime_id (polyTime_const [])

theorem polyTime_ext (b : Bool) : PolyTime (ext b) :=
  polyTime_pair polyTime_fst
    (polyTime_comp (polyTime_pair polyTime_snd (polyTime_const [b])) polyTime_append)

theorem polyTime_notP : PolyTime notP :=
  polyTime_ite polyTime_id (polyTime_const [false]) (polyTime_const [true])

/-- `notP` のコストは入力長の線形関数で抑えられる（具体形）。 -/
theorem notP_cost {x y : BStr} {t : ℕ} (h : Eval notP x y t) : t ≤ 2 * x.length + 4 := by
  rcases h.ite_inv with ⟨tc, tf, hc, hf, rfl⟩ | ⟨r, tc, tg, hc, hne, hg, rfl⟩
  · cases hc; cases hf; simp
  · cases hc; cases hg; simp; omega

end ProgLemmas

/-! ## 探索ループの正当性 -/

section SearchCorrect

variable {R : NPRel} {D : Prog}

/-- ループ本体。 -/
private def body (D : Prog) : Prog :=
  Prog.ite (Prog.comp (ext false) D) (ext false) (ext true)

/-- ループ条件。 -/
private def loopCond (V : Prog) : Prog := Prog.comp V notP

/--
ループ不変量の維持。

`enc x u` で `∃ v, R.rel x (u ++ v)` が成り立ち、かつ `u` 自身が
証拠でない（`V(enc x u) ≠ [true]`）なら、`v ≠ []` なので
`v` の先頭ビット `b` について `∃ v', R.rel x (u ++ [b] ++ v')`。
`D` は `(prefRel R).lang` を判定するので、body はこの `b` を選ぶ。
-/
theorem body_preserves (hD : Decides D (prefRel R).lang) (x u : BStr)
    (hinv : ∃ v, R.rel x (u ++ v)) (hnot : ¬ R.rel x u) :
    ∃ (b : Bool) (t : ℕ), Eval (body D) (enc x u) (enc x (u ++ [b])) t ∧
      ∃ v, R.rel x (u ++ [b] ++ v) := by
  obtain ⟨v, hv⟩ := hinv
  -- v ≠ [] （さもなくば u 自身が証拠）
  have hvne : v ≠ [] := by
    intro h; subst h; simp at hv; exact hnot hv
  obtain ⟨b, v', rfl⟩ : ∃ b v', v = b :: v' := by
    cases v with
    | nil => exact absurd rfl hvne
    | cons b v' => exact ⟨b, v', rfl⟩
  -- u ++ [b] ++ v' が証拠
  have hwit : R.rel x (u ++ [b] ++ v') := by
    rw [List.append_assoc]
    simpa using hv
  -- D(enc x (u ++ [false])) が true になるか否かで分岐
  obtain ⟨tf, hef⟩ := eval_ext false x u
  obtain ⟨yD, tD, heD⟩ := hD.1 (enc x (u ++ [false]))
  by_cases hDtrue : yD = [true]
  · -- false 側が選ばれる。D が true を返すので u ++ [false] は延長可能
    subst hDtrue
    refine ⟨false, _, Eval.ite_true (Eval.comp hef heD) hef, ?_⟩
    have := (hD.2 _ _ _ heD).mp rfl
    rw [prefRel_mem_iff] at this
    obtain ⟨v'', hv''⟩ := this
    exact ⟨v'', by simpa using hv''⟩
  · -- false 側が false を返すので、b は true でなければならない
    obtain ⟨tt, het⟩ := eval_ext true x u
    refine ⟨true, _, Eval.ite_false (Eval.comp hef heD) (by
      intro hc
      exact hDtrue (by
        have := hef.out_unique hef
        simpa using hc)) het, ?_⟩
    -- b = true を示す: b = false なら D は true を返すはず
    have hb : b = true := by
      by_contra hbf
      simp at hbf
      subst hbf
      exact hDtrue ((hD.2 _ _ _ heD).mpr (by
        rw [prefRel_mem_iff]
        exact ⟨v', by simpa using hwit⟩))
    subst hb
    exact ⟨v', hwit⟩

end SearchCorrect

section LoopRun

variable {R : NPRel} {D : Prog}

/-- `V` が `enc x u` 上で `[true]` を返すことと `R.rel x u` は同値。 -/
theorem V_true_iff (R : NPRel) (x u : BStr) {y : BStr} {t : ℕ}
    (h : Eval R.V (enc x u) y t) : y = [true] ↔ R.rel x u :=
  R.V_decides x u y t h

/--
ループの実行。

不変量 `∃ v, R.rel x (u ++ v)` と測度 `R.q |x| - |u|` に関する帰納法で、
ループが停止し、証拠を含む状態 `enc x w`（`R.rel x w`）に到達することを示す。
-/
theorem loop_reaches (hD : Decides D (prefRel R).lang) (x : BStr) :
    ∀ (fuel : ℕ) (u : BStr), R.q x.length ≤ u.length + fuel →
      (∃ v, R.rel x (u ++ v)) →
      ∃ (w : BStr) (t : ℕ),
        Eval (Prog.loop (loopCond R.V) (body D)) (enc x u) (enc x w) t ∧ R.rel x w := by
  intro fuel
  induction fuel with
  | zero =>
      intro u hq hinv
      -- 測度が 0: u はもう伸ばせないので u 自身が証拠でなければならない
      obtain ⟨v, hv⟩ := hinv
      have hvnil : v = [] := by
        by_contra hvne
        have hlen : (u ++ v).length ≤ R.q x.length := R.bound _ _ hv
        simp only [List.length_append] at hlen
        have : 0 < v.length := List.length_pos_iff.mpr hvne
        omega
      subst hvnil
      simp only [List.append_nil] at hv
      -- V(enc x u) = [true] なのでループは即停止
      obtain ⟨yv, tv, hev⟩ := R.V_poly.total (enc x u)
      have hyv : yv = [true] := (V_true_iff R x u hev).mpr hv
      subst hyv
      obtain ⟨tn, hen⟩ := eval_notP_true [true] rfl
      exact ⟨u, _, Eval.loop_stop (Eval.comp hev hen) (by simp), hv⟩
  | succ n ih =>
      intro u hq hinv
      obtain ⟨yv, tv, hev⟩ := R.V_poly.total (enc x u)
      by_cases hyv : yv = [true]
      · -- u 自身が証拠。ループは停止
        subst hyv
        have hrel : R.rel x u := (V_true_iff R x u hev).mp rfl
        obtain ⟨tn, hen⟩ := eval_notP_true [true] rfl
        exact ⟨u, _, Eval.loop_stop (Eval.comp hev hen) (by simp), hrel⟩
      · -- u は証拠でない。body で 1 ビット伸ばす
        have hnot : ¬ R.rel x u := fun hc => hyv ((V_true_iff R x u hev).mpr hc)
        obtain ⟨b, tb, heb, hinv'⟩ := body_preserves hD x u hinv hnot
        obtain ⟨tn, hen⟩ := eval_notP_false yv hyv
        -- 測度が 1 減る
        have hq' : R.q x.length ≤ (u ++ [b]).length + n := by
          simp only [List.length_append, List.length_cons, List.length_nil]
          omega
        obtain ⟨w, tw, hew, hrw⟩ := ih (u ++ [b]) hq' (by
          obtain ⟨v, hv⟩ := hinv'
          exact ⟨v, by simpa using hv⟩)
        exact ⟨w, _, Eval.loop_step (Eval.comp hev hen) heb hew, hrw⟩

end LoopRun

section SearchTCS

variable {R : NPRel} {D : Prog}

/-- 探索プログラムの本体（条件が true の側）。 -/
private def searchBody (D V : Prog) : Prog :=
  Prog.comp initS (Prog.comp (Prog.loop (loopCond V) (body D)) Prog.snd)

theorem prefixSearch_eq (D V : Prog) :
    prefixSearch D V = Prog.ite (Prog.comp initS D) (searchBody D V) (Prog.const []) := rfl

/-- YES インスタンスでは探索が証拠を返す。 -/
theorem prefixSearch_yes (hD : Decides D (prefRel R).lang) {x : BStr} (hx : x ∈ R.lang) :
    ∃ (w : BStr) (t : ℕ), Eval (prefixSearch D R.V) x w t ∧ R.rel x w := by
  obtain ⟨ti, hei⟩ := eval_initS x
  -- D(enc x []) = [true]（x ∈ R.lang なので）
  obtain ⟨yD, tD, heD⟩ := hD.1 (enc x [])
  have hDtrue : yD = [true] := by
    refine (hD.2 _ _ _ heD).mpr ?_
    rw [prefRel_mem_iff]
    obtain ⟨w, hw⟩ := hx
    exact ⟨w, by simpa using hw⟩
  subst hDtrue
  -- ループが証拠に到達する
  obtain ⟨w, tl, hel, hrw⟩ := loop_reaches hD x (R.q x.length) [] (by simp) (by
    obtain ⟨v, hv⟩ := hx
    exact ⟨v, by simpa using hv⟩)
  -- snd (enc x w) = w
  obtain ⟨ts, hes⟩ := eval_snd_enc x w
  exact ⟨w, _, Eval.ite_true (c := Prog.comp initS D) (f := searchBody D R.V)
    (g := Prog.const []) (Eval.comp hei heD)
    (Eval.comp hei (Eval.comp hel hes)), hrw⟩

/-- 探索プログラムは全域。 -/
theorem prefixSearch_total (hD : Decides D (prefRel R).lang) (x : BStr) :
    ∃ y t, Eval (prefixSearch D R.V) x y t := by
  by_cases hx : x ∈ R.lang
  · obtain ⟨w, t, he, -⟩ := prefixSearch_yes hD hx
    exact ⟨w, t, he⟩
  · -- NO インスタンス: D(enc x []) ≠ [true] なので [] を返す
    obtain ⟨ti, hei⟩ := eval_initS x
    obtain ⟨yD, tD, heD⟩ := hD.1 (enc x [])
    have hDfalse : yD ≠ [true] := by
      intro hc
      have := (hD.2 _ _ _ heD).mp hc
      rw [prefRel_mem_iff] at this
      obtain ⟨v, hv⟩ := this
      exact hx ⟨v, by simpa using hv⟩
    exact ⟨[], _, Eval.ite_false (c := Prog.comp initS D) (f := searchBody D R.V)
      (g := Prog.const []) (Eval.comp hei heD) hDfalse (Eval.const [] x)⟩

/-- 探索プログラムの出力は `R.q` 長に収まる。 -/
theorem prefixSearch_short (hD : Decides D (prefRel R).lang) (x y : BStr) (t : ℕ)
    (hev : Eval (prefixSearch D R.V) x y t) : y.length ≤ R.q x.length := by
  by_cases hx : x ∈ R.lang
  · obtain ⟨w, tw, hew, hrw⟩ := prefixSearch_yes hD hx
    rw [hev.out_unique hew]
    exact R.bound _ _ hrw
  · -- NO インスタンスでは [] を返す
    obtain ⟨ti, hei⟩ := eval_initS x
    obtain ⟨yD, tD, heD⟩ := hD.1 (enc x [])
    have hDfalse : yD ≠ [true] := by
      intro hc
      have := (hD.2 _ _ _ heD).mp hc
      rw [prefRel_mem_iff] at this
      obtain ⟨v, hv⟩ := this
      exact hx ⟨v, by simpa using hv⟩
    have hno : ∃ t', Eval (prefixSearch D R.V) x [] t' :=
      ⟨_, Eval.ite_false (c := Prog.comp initS D) (f := searchBody D R.V)
        (g := Prog.const []) (Eval.comp hei heD) hDfalse (Eval.const [] x)⟩
    obtain ⟨t', hno⟩ := hno
    rw [hev.out_unique hno]
    simp

/-- **`prefixSearch` は TCS**。 -/
noncomputable def prefixSearch_tcs (hD : Decides D (prefRel R).lang) : TCS R where
  M := prefixSearch D R.V
  total := prefixSearch_total hD
  correct := by
    intro x y t hev hx
    obtain ⟨w, tw, hew, hrw⟩ := prefixSearch_yes hD hx
    rw [hev.out_unique hew]
    exact hrw
  short := prefixSearch_short hD

end SearchTCS

/-! ## 探索のコスト上界 -/

section CostHelper

/--
多項式時間プログラムの、長さ `L` 以下の入力に対する一様なコスト上界。

`PolyTime P` から `c`・`k` を取り出し、入力長 `≤ L` のとき
コストが `c(L+1)^k` で抑えられることを言う。
-/
theorem polyTime_bound_on_le {P : Prog} (h : PolyTime P) :
    ∃ c k : ℕ, ∀ (L : ℕ) (x : BStr), x.length ≤ L →
      ∃ y t, Eval P x y t ∧ t ≤ c * (L + 1) ^ k := by
  obtain ⟨c, k, hc⟩ := h
  refine ⟨c, k, fun L x hx => ?_⟩
  obtain ⟨y, t, he, ht⟩ := hc x
  exact ⟨y, t, he, le_trans ht (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _))⟩

/-- 決定性より、`Eval` が与えられたときのコストは上界を継承する。 -/
theorem cost_le_of_eval {P : Prog} {x y : BStr} {t : ℕ} (hev : Eval P x y t)
    {c k L : ℕ} (hb : ∃ y' t', Eval P x y' t' ∧ t' ≤ c * (L + 1) ^ k) :
    t ≤ c * (L + 1) ^ k := by
  obtain ⟨y', t', he', ht'⟩ := hb
  rwa [hev.time_unique he']

end CostHelper

section SearchPoly

variable {R : NPRel} {D : Prog}

/-- 状態長の上界。 -/
private def stateLen (R : NPRel) (x : BStr) : ℕ := 2 * x.length + 1 + R.q x.length

theorem enc_len_le {R : NPRel} {x u : BStr} (h : u.length ≤ R.q x.length) :
    (enc x u).length ≤ stateLen R x := by
  rw [enc_length]; unfold stateLen; omega

/--
ループの実行と、そのコストの多項式上界。

反復ごとに `|u|` が 1 増え、`|u| ≤ R.q |x|` が保たれるので、
状態長は `stateLen R x` を超えない。1 反復のコストは
`V`・`notP`・`body` の、長さ `stateLen R x` 以下の入力に対する
コストの和で抑えられ、反復回数は `fuel + 1` 以下。
-/
theorem loop_reaches_cost (hD : Decides D (prefRel R).lang) (hDpoly : PolyTime D) :
    ∃ A B : ℕ, ∀ (x : BStr) (fuel : ℕ) (u : BStr),
      R.q x.length ≤ u.length + fuel → u.length ≤ R.q x.length →
      (∃ v, R.rel x (u ++ v)) →
      ∃ (w : BStr) (t : ℕ),
        Eval (Prog.loop (loopCond R.V) (body D)) (enc x u) (enc x w) t ∧
        R.rel x w ∧ w.length ≤ R.q x.length ∧
        t ≤ (fuel + 1) * (A * (stateLen R x + 1) ^ B) := by
  obtain ⟨cv, kv, hbv⟩ := polyTime_bound_on_le R.V_poly
  obtain ⟨cn, kn, hbn⟩ := polyTime_bound_on_le polyTime_notP
  obtain ⟨cb, kb, hbb⟩ := polyTime_bound_on_le
    (polyTime_ite (polyTime_comp (polyTime_ext false) hDpoly)
      (polyTime_ext false) (polyTime_ext true) : PolyTime (body D))
  set K := max kv (max kn kb) + 1 with hK
  set A := 3 * cv + cn + cb + 8 with hA
  refine ⟨A, K, ?_⟩
  intro x fuel
  -- 各プログラムのコストを共通の A, K で抑える
  have hpow : ∀ (c k : ℕ), k ≤ K → ∀ m : ℕ,
      c * (stateLen R x + 1) ^ k ≤ c * (stateLen R x + 1) ^ K := by
    intro c k hk m
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) hk)
  have hone : (1:ℕ) ≤ (stateLen R x + 1) ^ K := Nat.one_le_pow _ _ (by omega)
  have hst1 : 1 ≤ stateLen R x := by unfold stateLen; omega
  induction fuel with
  | zero =>
      intro u hq hulen hinv
      obtain ⟨v, hv⟩ := hinv
      have hvnil : v = [] := by
        by_contra hvne
        have hlen : (u ++ v).length ≤ R.q x.length := R.bound _ _ hv
        simp only [List.length_append] at hlen
        have : 0 < v.length := List.length_pos_iff.mpr hvne
        omega
      subst hvnil
      simp only [List.append_nil] at hv
      obtain ⟨yv, tv, hev, htv⟩ := hbv (stateLen R x) (enc x u) (enc_len_le hulen)
      have hyv : yv = [true] := (V_true_iff R x u hev).mpr hv
      subst hyv
      obtain ⟨yn, tn, hen, htn⟩ := hbn (stateLen R x) [true] (by simp [hst1])
      have hyn : yn = [false] := hen.out_unique (eval_notP_true [true] rfl).choose_spec
      subst hyn
      refine ⟨u, _, Eval.loop_stop (Eval.comp hev hen) (by simp), hv, hulen, ?_⟩
      have e1 := hpow cv kv (by omega) 0
      have e2 := hpow cn kn (by omega) 0
      have hgoal : tv + tn + 1 + 1 ≤ (3 * cv + cn + cb + 8) * (stateLen R x + 1) ^ K := by
        calc tv + tn + 1 + 1
            ≤ cv * (stateLen R x + 1) ^ K + cn * (stateLen R x + 1) ^ K
              + 1 * (stateLen R x + 1) ^ K + 1 * (stateLen R x + 1) ^ K := by omega
          _ ≤ (3 * cv + cn + cb + 8) * (stateLen R x + 1) ^ K := by ring_nf; omega
      have heq : (0 + 1) * (A * (stateLen R x + 1) ^ K) = A * (stateLen R x + 1) ^ K := by ring
      rw [heq, hA]
      exact hgoal
  | succ n ih =>
      intro u hq hulen hinv
      obtain ⟨yv, tv, hev, htv⟩ := hbv (stateLen R x) (enc x u) (enc_len_le hulen)
      have e1 := hpow cv kv (by omega) 0
      have e2 := hpow cn kn (by omega) 0
      have e3 := hpow cb kb (by omega) 0
      by_cases hyv : yv = [true]
      · subst hyv
        have hrel : R.rel x u := (V_true_iff R x u hev).mp rfl
        obtain ⟨yn, tn, hen, htn⟩ := hbn (stateLen R x) [true] (by simp [hst1])
        have hyn : yn = [false] := hen.out_unique (eval_notP_true [true] rfl).choose_spec
        subst hyn
        refine ⟨u, _, Eval.loop_stop (Eval.comp hev hen) (by simp), hrel, hulen, ?_⟩
        have hgoal : tv + tn + 1 + 1 ≤ (3 * cv + cn + cb + 8) * (stateLen R x + 1) ^ K := by
          calc tv + tn + 1 + 1
              ≤ cv * (stateLen R x + 1) ^ K + cn * (stateLen R x + 1) ^ K
                + 1 * (stateLen R x + 1) ^ K + 1 * (stateLen R x + 1) ^ K := by omega
            _ ≤ (3 * cv + cn + cb + 8) * (stateLen R x + 1) ^ K := by ring_nf; omega
        have hle : (3 * cv + cn + cb + 8) * (stateLen R x + 1) ^ K
            ≤ (n + 1 + 1) * ((3 * cv + cn + cb + 8) * (stateLen R x + 1) ^ K) :=
          Nat.le_mul_of_pos_left _ (by omega)
        rw [hA]
        omega
      · have hnot : ¬ R.rel x u := fun hc => hyv ((V_true_iff R x u hev).mpr hc)
        obtain ⟨b, tb, heb, hinv'⟩ := body_preserves hD x u hinv hnot
        -- yv の長さは stateLen 以下（size_le より）
        obtain ⟨tn, hen⟩ := eval_notP_false yv hyv
        have hyvlen : yv.length ≤ stateLen R x + tv := by
          have hs := hev.size_le
          have hlen := enc_len_le (R := R) hulen
          omega
        have htn : tn ≤ 2 * (stateLen R x + tv) + 4 :=
          le_trans (notP_cost hen) (by omega)
        -- stateLen ≤ (stateLen+1)^K, tv ≤ cv*(...)^K なので tn は A*(...)^K に収まる
        have hstK : stateLen R x + 1 ≤ (stateLen R x + 1) ^ K := by
          have h2 : (stateLen R x + 1) ^ 1 ≤ (stateLen R x + 1) ^ K :=
            Nat.pow_le_pow_right (by omega) (by omega)
          simpa using h2
        -- body のコスト
        have htb : tb ≤ cb * (stateLen R x + 1) ^ kb :=
          cost_le_of_eval heb (hbb (stateLen R x) (enc x u) (enc_len_le hulen))
        have hulen' : (u ++ [b]).length ≤ R.q x.length := by
          obtain ⟨v, hv⟩ := hinv'
          have := R.bound _ _ hv
          simp only [List.length_append] at this ⊢
          simp only [List.length_cons, List.length_nil] at this ⊢
          omega
        have hq' : R.q x.length ≤ (u ++ [b]).length + n := by
          simp only [List.length_append, List.length_cons, List.length_nil]
          omega
        obtain ⟨w, tw, hew, hrw, hwlen, htw⟩ := ih (u ++ [b]) hq' hulen' (by
          obtain ⟨v, hv⟩ := hinv'
          exact ⟨v, by simpa using hv⟩)
        refine ⟨w, _, Eval.loop_step (Eval.comp hev hen) heb hew, hrw, hwlen, ?_⟩
        simp only [hA] at htw ⊢
        nlinarith

end SearchPoly

/-- `stateLen` は `|x|` の多項式。 -/
theorem stateLen_poly (R : NPRel) : PolyBound (fun n => 2 * n + 1 + R.q n) :=
  PolyBound.add (PolyBound.add (PolyBound.mul (PolyBound.const 2) PolyBound.id)
    (PolyBound.const 1)) R.q_poly

/-- `PolyTime` の十分条件: コストが何らかの `PolyBound` 関数で抑えられる。 -/
theorem polyTime_of_bound {P : Prog} {T : ℕ → ℕ} (hT : PolyBound T)
    (h : ∀ x, ∃ y t, Eval P x y t ∧ t ≤ T x.length) : PolyTime P := by
  obtain ⟨c, k, hc⟩ := hT
  refine ⟨c, k, fun x => ?_⟩
  obtain ⟨y, t, he, ht⟩ := h x
  exact ⟨y, t, he, le_trans ht (hc _)⟩

/--
**`prefixSearch` は多項式時間**。

反復回数は `R.q |x| + 1` 以下、1 反復のコストは状態長
`stateLen R x = 2|x| + 1 + R.q |x|` の多項式。どちらも `|x|` の多項式
なので、積も `|x|` の多項式。
-/
theorem prefixSearch_polyTime (hDpoly : PolyTime D) (hD : Decides D (prefRel R).lang) :
    PolyTime (prefixSearch D R.V) := by
  obtain ⟨A, B, hloop⟩ := loop_reaches_cost hD hDpoly
  obtain ⟨ci, ki, hbi⟩ := polyTime_bound_on_le polyTime_initS
  obtain ⟨cd, kd, hbd⟩ := polyTime_bound_on_le hDpoly
  obtain ⟨cs, ks, hbs⟩ := polyTime_bound_on_le polyTime_snd
  -- コストを抑える多項式 T を定義する
  set SL : ℕ → ℕ := fun n => 2 * n + 1 + R.q n with hSL
  set T : ℕ → ℕ := fun n =>
    2 * ci * (n + 1) ^ ki + cd * (SL n + 1) ^ kd + cs * (SL n + 1) ^ ks
      + (R.q n + 1) * (A * (SL n + 1) ^ B) + 4 with hT
  have hTpoly : PolyBound T := by
    have hSLpoly : PolyBound SL := stateLen_poly R
    have hSL1 : PolyBound (fun n => SL n + 1) := PolyBound.add hSLpoly (PolyBound.const 1)
    have hpow : ∀ e : ℕ, PolyBound (fun n => (SL n + 1) ^ e) := by
      intro e
      have hid : PolyBound (fun m => m ^ e) := ⟨1, e, fun m => by
        simp only [one_mul]
        exact Nat.pow_le_pow_left (by omega) _⟩
      exact PolyBound.comp hid hSL1
    refine PolyBound.add (PolyBound.add (PolyBound.add (PolyBound.add ?_ ?_) ?_) ?_)
      (PolyBound.const 4)
    · exact ⟨2 * ci, ki, fun n => le_refl _⟩
    · exact PolyBound.mul (PolyBound.const cd) (hpow kd)
    · exact PolyBound.mul (PolyBound.const cs) (hpow ks)
    · exact PolyBound.mul (PolyBound.add R.q_poly (PolyBound.const 1))
        (PolyBound.mul (PolyBound.const A) (hpow B))
  refine polyTime_of_bound hTpoly (fun x => ?_)
  -- initS のコスト
  obtain ⟨yi, ti, hei, hti⟩ := hbi x.length x (le_refl _)
  have hyi : yi = enc x [] := hei.out_unique (eval_initS x).choose_spec
  subst hyi
  -- D(enc x []) のコスト
  have hle0 : (enc x []).length ≤ SL x.length := by
    rw [enc_length, hSL]; simp
  obtain ⟨yD, tD, heD, htD⟩ := hbd (SL x.length) (enc x []) hle0
  by_cases hDtrue : yD = [true]
  · subst hDtrue
    -- ループの実行
    have hx : x ∈ R.lang := by
      have := (hD.2 _ _ _ heD).mp rfl
      rw [prefRel_mem_iff] at this
      obtain ⟨v, hv⟩ := this
      exact ⟨v, by simpa using hv⟩
    obtain ⟨w, tl, hel, hrw, hwlen, htl⟩ :=
      hloop x (R.q x.length) [] (by simp) (by simp) (by
        obtain ⟨v, hv⟩ := hx
        exact ⟨v, by simpa using hv⟩)
    -- snd のコスト
    have hlew : (enc x w).length ≤ SL x.length := by
      rw [enc_length, hSL]; simp; omega
    obtain ⟨ys, ts, hes, hts⟩ := hbs (SL x.length) (enc x w) hlew
    have hys : ys = w := hes.out_unique (eval_snd_enc x w).choose_spec
    rw [hys] at hes
    refine ⟨w, _, Eval.ite_true (c := Prog.comp initS D) (f := searchBody D R.V)
      (g := Prog.const []) (Eval.comp hei heD)
      (Eval.comp hei (Eval.comp hel hes)), ?_⟩
    -- コスト = (ti+tD+1) + (ti + (tl+ts+1) + 1) + 1
    rw [hT]
    have h3 : stateLen R x = SL x.length := by rw [hSL]; rfl
    rw [h3] at htl
    show _ ≤ 2 * ci * (x.length + 1) ^ ki + cd * (SL x.length + 1) ^ kd
      + cs * (SL x.length + 1) ^ ks + (R.q x.length + 1) * (A * (SL x.length + 1) ^ B) + 4
    have h2 : 2 * ci * (x.length + 1) ^ ki = 2 * (ci * (x.length + 1) ^ ki) := by ring
    omega
  · -- NO 側: const [] を返す
    refine ⟨[], _, Eval.ite_false (c := Prog.comp initS D) (f := searchBody D R.V)
      (g := Prog.const []) (Eval.comp hei heD) hDtrue (Eval.const [] x), ?_⟩
    rw [hT]
    show _ ≤ 2 * ci * (x.length + 1) ^ ki + cd * (SL x.length + 1) ^ kd
      + cs * (SL x.length + 1) ^ ks + (R.q x.length + 1) * (A * (SL x.length + 1) ^ B) + 4
    have h2 : 2 * ci * (x.length + 1) ^ ki = 2 * (ci * (x.length + 1) ^ ki) := by ring
    simp only [List.length_nil]
    omega
