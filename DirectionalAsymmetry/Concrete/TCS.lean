/-
# Total Candidate Solver と方向非対称性

v3 指示書 §5。

**原則 (P1)**: `TCS` は時間フィールドを持たない。
時間は `Eval` の決定性から一意に定まる値として取り出す。
**原則 (P2)**: プロファイルは長さ n の全入力にわたる最大値（一様）。
-/
import DirectionalAsymmetry.Concrete.Classes
import Mathlib.Data.Nat.Log
import Mathlib.Order.Interval.Finset.Nat

open Encoding Prog

/--
Definition 2: Total Candidate Solver。

常に停止し、YES インスタンスでは valid な証拠を出力する。
出力は `R.q` 長に収まる。**時間フィールドは持たない**（P1）。
-/
structure TCS (R : NPRel) where
  M       : Prog
  total   : ∀ x, ∃ y t, Eval M x y t
  correct : ∀ x y t, Eval M x y t → x ∈ R.lang → R.rel x y
  short   : ∀ x y t, Eval M x y t → y.length ≤ R.q x.length

namespace TCS

variable {R : NPRel}

/-- `M` の `x` 上の出力（決定性より一意）。 -/
noncomputable def out (M : TCS R) (x : BStr) : BStr := (M.total x).choose

/-- `M` の `x` 上の時間（決定性より一意）。 -/
noncomputable def time (M : TCS R) (x : BStr) : ℕ :=
  (M.total x).choose_spec.choose

theorem eval_out_time (M : TCS R) (x : BStr) : Eval M.M x (M.out x) (M.time x) :=
  (M.total x).choose_spec.choose_spec

/-- `out` / `time` は `Eval` から一意に決まる。 -/
theorem out_eq {M : TCS R} {x y : BStr} {t : ℕ} (h : Eval M.M x y t) : M.out x = y :=
  (M.eval_out_time x).out_unique h

theorem time_eq {M : TCS R} {x y : BStr} {t : ℕ} (h : Eval M.M x y t) : M.time x = t :=
  (M.eval_out_time x).time_unique h

theorem time_pos (M : TCS R) (x : BStr) : 1 ≤ M.time x := (M.eval_out_time x).cost_pos

theorem out_short (M : TCS R) (x : BStr) : (M.out x).length ≤ R.q x.length :=
  M.short x _ _ (M.eval_out_time x)

theorem out_correct (M : TCS R) {x : BStr} (hx : x ∈ R.lang) : R.rel x (M.out x) :=
  M.correct x _ _ (M.eval_out_time x) hx

end TCS

/-- `R.V` が `enc x w` 上で費やす時間。 -/
noncomputable def vtime (R : NPRel) (x w : BStr) : ℕ :=
  (R.V_poly.total (enc x w)).choose_spec.choose

theorem eval_vtime (R : NPRel) (x w : BStr) :
    Eval R.V (enc x w) ((R.V_poly.total (enc x w)).choose) (vtime R x w) :=
  (R.V_poly.total (enc x w)).choose_spec.choose_spec

theorem vtime_eq {R : NPRel} {x w y : BStr} {t : ℕ} (h : Eval R.V (enc x w) y t) :
    vtime R x w = t := (eval_vtime R x w).time_unique h

theorem vtime_pos (R : NPRel) (x w : BStr) : 1 ≤ vtime R x w :=
  (eval_vtime R x w).cost_pos

/--
Definition 3: 計算的方向非対称性。

`A_M(x) = log₂ T_M(x) − log₂ T_V(x, M(x))`
-/
noncomputable def asym {R : NPRel} (M : TCS R) (x : BStr) : ℤ :=
  (Nat.log 2 (M.time x) : ℤ) - (Nat.log 2 (vtime R x (M.out x)) : ℤ)

/-- 長さ `n` の二進列全体（有限集合）。 -/
def inputsOfSize (n : ℕ) : Finset BStr :=
  (Finset.univ : Finset (Fin n → Bool)).image (fun f => List.ofFn f)

theorem mem_inputsOfSize {n : ℕ} {x : BStr} : x ∈ inputsOfSize n ↔ x.length = n := by
  constructor
  · intro hx
    obtain ⟨f, -, rfl⟩ := Finset.mem_image.mp hx
    exact List.length_ofFn
  · intro hx
    subst hx
    exact Finset.mem_image.mpr ⟨fun i => x.get i, Finset.mem_univ _, List.ofFn_get x⟩

theorem inputsOfSize_nonempty (n : ℕ) : (inputsOfSize n).Nonempty :=
  ⟨List.replicate n true, mem_inputsOfSize.mpr (List.length_replicate)⟩

/--
Definition 3': プロファイル `g_M(n)`。

長さ `n` の全入力にわたる `asym M x` の最大値（一様な最悪ケース、P2）。
-/
noncomputable def profile {R : NPRel} (M : TCS R) (n : ℕ) : ℤ :=
  (inputsOfSize n).sup' (inputsOfSize_nonempty n) (fun x => asym M x)

theorem le_profile {R : NPRel} (M : TCS R) {x : BStr} {n : ℕ} (hx : x.length = n) :
    asym M x ≤ profile M n :=
  Finset.le_sup' _ (mem_inputsOfSize.mpr hx)

theorem profile_le {R : NPRel} (M : TCS R) {n : ℕ} {b : ℤ}
    (h : ∀ x, x.length = n → asym M x ≤ b) : profile M n ≤ b :=
  Finset.sup'_le _ _ (fun x hx => h x (mem_inputsOfSize.mp hx))

/-- `O(log n)` で上から押さえられる。 -/
def LogBounded (f : ℕ → ℤ) : Prop := ∃ C : ℕ, ∀ n, f n ≤ C * (Nat.log 2 n + 1)

/-! ## log に関する補助補題 -/

section LogAux

/-- `Nat.log 2 a ≤ b → a < 2 ^ (b+1)`。 -/
theorem lt_two_pow_succ_of_log_le {a b : ℕ} (h : Nat.log 2 a ≤ b) : a < 2 ^ (b + 1) :=
  lt_of_lt_of_le (Nat.lt_pow_succ_log_self (by norm_num) a)
    (Nat.pow_le_pow_right (by norm_num) (by omega))

/-- `2 ^ Nat.log 2 n ≤ n`（n ≠ 0）。 -/
theorem two_pow_log_le {n : ℕ} (hn : n ≠ 0) : 2 ^ Nat.log 2 n ≤ n :=
  Nat.pow_log_le_self 2 hn

/-- 多項式なら log は `C(log n + 1)` で押さえられる。 -/
theorem log_poly_le {T : ℕ → ℕ} (hT : PolyBound T) :
    ∃ C : ℕ, ∀ n, Nat.log 2 (T n) ≤ C * (Nat.log 2 n + 1) := by
  obtain ⟨c, k, hc⟩ := hT
  -- log (c*(n+1)^k) ≤ log c + k * log (n+1) ≤ log c + k*(log n + 1)
  refine ⟨Nat.log 2 c + 2 * k + 1, fun n => ?_⟩
  have h1 : Nat.log 2 (T n) ≤ Nat.log 2 (c * (n + 1) ^ k) := Nat.log_mono_right (hc n)
  refine le_trans h1 ?_
  -- log (c * m) ≤ log c + log m + 1 を使う
  have hlog_mul : ∀ a b : ℕ, Nat.log 2 (a * b) ≤ Nat.log 2 a + Nat.log 2 b + 1 := by
    intro a b
    rcases Nat.eq_zero_or_pos a with rfl | ha
    · simp
    rcases Nat.eq_zero_or_pos b with rfl | hb
    · simp
    by_contra hcon
    push Not at hcon
    have h2 : 2 ^ (Nat.log 2 (a * b)) ≤ a * b :=
      Nat.pow_log_le_self 2 (by positivity)
    have h3 : a * b < 2 ^ (Nat.log 2 a + 1) * 2 ^ (Nat.log 2 b + 1) :=
      Nat.mul_lt_mul_of_lt_of_lt (Nat.lt_pow_succ_log_self (by norm_num) a)
        (Nat.lt_pow_succ_log_self (by norm_num) b)
    rw [← pow_add] at h3
    have h4 : 2 ^ (Nat.log 2 a + Nat.log 2 b + 2) ≤ 2 ^ (Nat.log 2 (a * b)) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    have : (2:ℕ) ^ (Nat.log 2 a + 1 + (Nat.log 2 b + 1))
        = 2 ^ (Nat.log 2 a + Nat.log 2 b + 2) := by ring_nf
    omega
  have hlog_pow : ∀ m e : ℕ, Nat.log 2 (m ^ e) ≤ e * (Nat.log 2 m + 1) := by
    intro m e
    induction e with
    | zero => simp
    | succ e ih =>
        rcases Nat.eq_zero_or_pos m with rfl | hm
        · rcases Nat.eq_zero_or_pos e with rfl | he
          · simp
          · have : (0:ℕ) ^ (e + 1) = 0 := by simp
            rw [this]
            simp
        calc Nat.log 2 (m ^ (e + 1)) = Nat.log 2 (m ^ e * m) := by rw [pow_succ]
          _ ≤ Nat.log 2 (m ^ e) + Nat.log 2 m + 1 := hlog_mul _ _
          _ ≤ e * (Nat.log 2 m + 1) + Nat.log 2 m + 1 := by omega
          _ = (e + 1) * (Nat.log 2 m + 1) := by ring
  have hlogn1 : Nat.log 2 (n + 1) ≤ Nat.log 2 n + 1 := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · -- n ≥ 1 のとき n+1 ≤ 2n なので 2^(log n + 2) > n+1、よって log(n+1) ≤ log n + 1
      by_contra hcon
      push Not at hcon
      have h1 : 2 ^ (Nat.log 2 n + 2) ≤ n + 1 :=
        le_trans (Nat.pow_le_pow_right (by norm_num) (by omega))
          (Nat.pow_log_le_self 2 (by omega))
      have h2 : n < 2 ^ (Nat.log 2 n + 1) := Nat.lt_pow_succ_log_self (by norm_num) n
      have h3 : (2:ℕ) ^ (Nat.log 2 n + 2) = 2 * 2 ^ (Nat.log 2 n + 1) := by ring
      omega
  calc Nat.log 2 (c * (n + 1) ^ k) ≤ Nat.log 2 c + Nat.log 2 ((n + 1) ^ k) + 1 :=
        hlog_mul _ _
    _ ≤ Nat.log 2 c + k * (Nat.log 2 (n + 1) + 1) + 1 := by
        have := hlog_pow (n + 1) k; omega
    _ ≤ Nat.log 2 c + k * (Nat.log 2 n + 2) + 1 := by
        have : Nat.log 2 (n + 1) + 1 ≤ Nat.log 2 n + 2 := by omega
        have := Nat.mul_le_mul_left k this
        omega
    _ ≤ (Nat.log 2 c + 2 * k + 1) * (Nat.log 2 n + 1) := by
        set L := Nat.log 2 n
        have hk : k * (L + 2) ≤ 2 * k * (L + 1) := by nlinarith
        have hcc : Nat.log 2 c ≤ Nat.log 2 c * (L + 1) := Nat.le_mul_of_pos_right _ (by omega)
        have hone : 1 ≤ 1 * (L + 1) := by omega
        calc Nat.log 2 c + k * (L + 2) + 1
            ≤ Nat.log 2 c * (L + 1) + 2 * k * (L + 1) + 1 * (L + 1) := by omega
          _ = (Nat.log 2 c + 2 * k + 1) * (L + 1) := by ring

end LogAux

/-! ## §5 の必須補題 -/

section MainLemmas

variable {R : NPRel}

/--
**普遍下界**（論文 §3.2）。

`asym M x = log T_M − log T_V` で、`T_V` は入力 `enc x (M x)` 上の
`R.V` のコスト。`M` の出力は `R.q |x|` 長に収まるので `T_V` は
`|x|` の多項式で抑えられ、その log は `O(log n)`。
`T_M ≥ 1` より `log T_M ≥ 0` なので、`asym` は `-O(log n)` 以上。
-/
theorem asym_lower (R : NPRel) (M : TCS R) :
    ∃ C : ℕ, ∀ n, -(C * (Nat.log 2 n + 1) : ℤ) ≤ profile M n := by
  -- T_V(x, M x) は |x| の多項式で抑えられる
  obtain ⟨cv, kv, hcv⟩ := R.V_poly
  obtain ⟨cq, kq, hcq⟩ := R.q_poly
  -- |enc x (M x)| = 2|x| + 1 + |M x| ≤ 2n + 1 + q(n)
  set TV : ℕ → ℕ := fun n => cv * (2 * n + 1 + cq * (n + 1) ^ kq + 1) ^ kv with hTV
  have hTVpoly : PolyBound TV := by
    refine PolyBound.mul (PolyBound.const cv) ?_
    -- (2n + 1 + cq(n+1)^kq + 1) ≤ (4 + cq)(n+1)^kq なので、kv 乗して多項式
    refine ⟨(4 + cq) ^ kv, (kq + 1) * kv, fun n => ?_⟩
    have hge : n + 1 ≤ (n + 1) ^ (kq + 1) := by
      have : (n + 1) ^ 1 ≤ (n + 1) ^ (kq + 1) :=
        Nat.pow_le_pow_right (by omega) (by omega)
      simpa using this
    have hkq : (n + 1) ^ kq ≤ (n + 1) ^ (kq + 1) :=
      Nat.pow_le_pow_right (by omega) (by omega)
    have hbase : 2 * n + 1 + cq * (n + 1) ^ kq + 1 ≤ (4 + cq) * (n + 1) ^ (kq + 1) := by
      have h2 : cq * (n + 1) ^ kq ≤ cq * (n + 1) ^ (kq + 1) := Nat.mul_le_mul_left _ hkq
      nlinarith
    calc (2 * n + 1 + cq * (n + 1) ^ kq + 1) ^ kv
        ≤ ((4 + cq) * (n + 1) ^ (kq + 1)) ^ kv := Nat.pow_le_pow_left hbase _
      _ = (4 + cq) ^ kv * (n + 1) ^ ((kq + 1) * kv) := by rw [Nat.mul_pow, ← pow_mul]
  obtain ⟨C, hC⟩ := log_poly_le hTVpoly
  refine ⟨C, fun n => ?_⟩
  obtain ⟨x, hx⟩ := inputsOfSize_nonempty n
  have hxn : x.length = n := mem_inputsOfSize.mp hx
  refine le_trans ?_ (le_profile M hxn)
  -- asym M x ≥ -log (vtime) ≥ -C(log n + 1)
  have hvle : vtime R x (M.out x) ≤ TV n := by
    obtain ⟨y, t, he, ht⟩ := hcv (enc x (M.out x))
    rw [vtime_eq he]
    refine le_trans ht ?_
    rw [hTV]
    refine Nat.mul_le_mul_left _ (Nat.pow_le_pow_left ?_ _)
    have h1 := M.out_short x
    have h2 := hcq x.length
    rw [hxn] at h1 h2
    rw [enc_length, hxn]
    omega
  have hlog : Nat.log 2 (vtime R x (M.out x)) ≤ C * (Nat.log 2 n + 1) :=
    le_trans (Nat.log_mono_right hvle) (hC n)
  unfold asym
  have hz : (0:ℤ) ≤ (Nat.log 2 (M.time x) : ℤ) := Int.natCast_nonneg _
  have hlogZ : (Nat.log 2 (vtime R x (M.out x)) : ℤ) ≤ (C : ℤ) * ((Nat.log 2 n : ℤ) + 1) := by
    exact_mod_cast hlog
  omega

/-- 多項式時間 TCS のプロファイルは `O(log n)`。 -/
theorem logBounded_of_polyTime {M : TCS R} (h : PolyTime M.M) : LogBounded (profile M) := by
  obtain ⟨c, k, hc⟩ := h
  -- T_M(x) ≤ c(n+1)^k なので log T_M ≤ C(log n + 1)
  obtain ⟨C, hC⟩ := log_poly_le (⟨c, k, fun n => le_refl _⟩ : PolyBound (fun n => c * (n+1)^k))
  refine ⟨C, fun n => ?_⟩
  refine profile_le M (fun x hxn => ?_)
  obtain ⟨y, t, he, ht⟩ := hc x
  unfold asym
  have htm : M.time x ≤ c * (n + 1) ^ k := by rw [TCS.time_eq he, ← hxn]; exact ht
  have h1 : Nat.log 2 (M.time x) ≤ C * (Nat.log 2 n + 1) :=
    le_trans (Nat.log_mono_right htm) (hC n)
  have h2 : (0:ℤ) ≤ (Nat.log 2 (vtime R x (M.out x)) : ℤ) := Int.natCast_nonneg _
  have h1Z : (Nat.log 2 (M.time x) : ℤ) ≤ (C : ℤ) * ((Nat.log 2 n : ℤ) + 1) := by
    exact_mod_cast h1
  omega

end MainLemmas

/--
**(c)⇒(a) の核**: プロファイルが `O(log n)` なら `M` は多項式時間。

方針（指示書 §5 のヒント）:
`asym M x ≤ C(log n + 1)` より `log T_M ≤ log T_V + C(log n + 1)`。
`lt_two_pow_succ_of_log_le` で `T_M < 2^(log T_V + C(log n+1) + 1)`
`= 2 · 2^(log T_V) · (2^(log n + 1))^C ≤ 2 · T_V · (2(n+1))^C`。
`T_V` は `short` と `V_poly` から多項式で抑えられるので `T_M` も多項式。
-/
theorem polyTime_of_logBounded {R : NPRel} {M : TCS R}
    (h : LogBounded (profile M)) : PolyTime M.M := by
  obtain ⟨C, hC⟩ := h
  -- T_V(x, M x) の多項式上界（asym_lower と同じ構成）
  obtain ⟨cv, kv, hcv⟩ := R.V_poly
  obtain ⟨cq, kq, hcq⟩ := R.q_poly
  set TV : ℕ → ℕ := fun n => cv * (2 * n + 1 + cq * (n + 1) ^ kq + 1) ^ kv with hTV
  have hTVpoly : PolyBound TV := by
    refine PolyBound.mul (PolyBound.const cv) ?_
    refine ⟨(4 + cq) ^ kv, (kq + 1) * kv, fun n => ?_⟩
    have hge : n + 1 ≤ (n + 1) ^ (kq + 1) := by
      have : (n + 1) ^ 1 ≤ (n + 1) ^ (kq + 1) :=
        Nat.pow_le_pow_right (by omega) (by omega)
      simpa using this
    have hkq : (n + 1) ^ kq ≤ (n + 1) ^ (kq + 1) :=
      Nat.pow_le_pow_right (by omega) (by omega)
    have hbase : 2 * n + 1 + cq * (n + 1) ^ kq + 1 ≤ (4 + cq) * (n + 1) ^ (kq + 1) := by
      have h2 : cq * (n + 1) ^ kq ≤ cq * (n + 1) ^ (kq + 1) := Nat.mul_le_mul_left _ hkq
      nlinarith
    calc (2 * n + 1 + cq * (n + 1) ^ kq + 1) ^ kv
        ≤ ((4 + cq) * (n + 1) ^ (kq + 1)) ^ kv := Nat.pow_le_pow_left hbase _
      _ = (4 + cq) ^ kv * (n + 1) ^ ((kq + 1) * kv) := by rw [Nat.mul_pow, ← pow_mul]
  -- 各 x について T_V(x, M x) ≤ TV |x|
  have hvle : ∀ x : BStr, vtime R x (M.out x) ≤ TV x.length := by
    intro x
    obtain ⟨y, t, he, ht⟩ := hcv (enc x (M.out x))
    rw [vtime_eq he]
    refine le_trans ht ?_
    rw [hTV]
    refine Nat.mul_le_mul_left _ (Nat.pow_le_pow_left ?_ _)
    have h1 := M.out_short x
    have h2 := hcq x.length
    rw [enc_length]
    omega
  -- 目標の多項式上界を構成する
  obtain ⟨cT, kT, hcT⟩ := hTVpoly
  refine ⟨2 * cT * 2 ^ C, kT + C, fun x => ?_⟩
  refine ⟨M.out x, M.time x, M.eval_out_time x, ?_⟩
  set n := x.length with hn
  -- asym M x ≤ profile M n ≤ C(log n + 1)
  have hasym : asym M x ≤ (C : ℤ) * ((Nat.log 2 n : ℤ) + 1) := by
    have h1 : asym M x ≤ profile M n := le_profile M hn.symm
    have h2 := hC n
    have : ((C * (Nat.log 2 n + 1) : ℕ) : ℤ) = (C : ℤ) * ((Nat.log 2 n : ℤ) + 1) := by
      push_cast; ring
    omega
  -- log T_M ≤ log T_V + C(log n + 1)
  have hlogM : Nat.log 2 (M.time x) ≤ Nat.log 2 (vtime R x (M.out x)) + C * (Nat.log 2 n + 1) := by
    unfold asym at hasym
    have : ((C * (Nat.log 2 n + 1) : ℕ) : ℤ) = (C : ℤ) * ((Nat.log 2 n : ℤ) + 1) := by
      push_cast; ring
    omega
  -- T_M < 2^(log T_V + C(log n+1) + 1)
  have hTM : M.time x < 2 ^ (Nat.log 2 (vtime R x (M.out x)) + C * (Nat.log 2 n + 1) + 1) :=
    lt_two_pow_succ_of_log_le hlogM
  -- 2^(log T_V) ≤ T_V、2^(log n) ≤ n（n ≠ 0 のとき）
  have hV : 2 ^ Nat.log 2 (vtime R x (M.out x)) ≤ vtime R x (M.out x) :=
    two_pow_log_le (by have := vtime_pos R x (M.out x); omega)
  have hnlog : 2 ^ Nat.log 2 n ≤ n + 1 := by
    rcases Nat.eq_zero_or_pos n with h | h
    · simp [h]
    · exact le_trans (two_pow_log_le (by omega)) (by omega)
  -- 2^(C(log n + 1)) = (2^(log n) * 2)^C ≤ (2(n+1))^C
  have hpowC : 2 ^ (C * (Nat.log 2 n + 1)) ≤ 2 ^ C * (n + 1) ^ C := by
    calc 2 ^ (C * (Nat.log 2 n + 1)) = (2 ^ (Nat.log 2 n + 1)) ^ C := by
          rw [← pow_mul]; ring_nf
      _ = (2 ^ Nat.log 2 n * 2) ^ C := by rw [pow_succ]
      _ ≤ ((n + 1) * 2) ^ C := Nat.pow_le_pow_left (by omega) _
      _ = 2 ^ C * (n + 1) ^ C := by rw [Nat.mul_pow]; ring
  -- 合成
  have hsplit : (2:ℕ) ^ (Nat.log 2 (vtime R x (M.out x)) + C * (Nat.log 2 n + 1) + 1)
      = 2 ^ Nat.log 2 (vtime R x (M.out x)) * 2 ^ (C * (Nat.log 2 n + 1)) * 2 := by
    rw [pow_add, pow_add]; ring
  have hfin : M.time x ≤ 2 * vtime R x (M.out x) * (2 ^ C * (n + 1) ^ C) := by
    rw [hsplit] at hTM
    calc M.time x ≤ 2 ^ Nat.log 2 (vtime R x (M.out x)) * 2 ^ (C * (Nat.log 2 n + 1)) * 2 := by
          omega
      _ ≤ vtime R x (M.out x) * (2 ^ C * (n + 1) ^ C) * 2 :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul hV hpowC)
      _ = 2 * vtime R x (M.out x) * (2 ^ C * (n + 1) ^ C) := by ring
  -- T_V ≤ TV n ≤ cT (n+1)^kT
  have hTVn : vtime R x (M.out x) ≤ cT * (n + 1) ^ kT := le_trans (hvle x) (hcT n)
  calc M.time x ≤ 2 * vtime R x (M.out x) * (2 ^ C * (n + 1) ^ C) := hfin
    _ ≤ 2 * (cT * (n + 1) ^ kT) * (2 ^ C * (n + 1) ^ C) := by
        refine Nat.mul_le_mul_right _ ?_
        exact Nat.mul_le_mul_left _ hTVn
    _ = 2 * cT * 2 ^ C * ((n + 1) ^ kT * (n + 1) ^ C) := by ring
    _ = 2 * cT * 2 ^ C * (n + 1) ^ (kT + C) := by rw [← pow_add]

/--
多項式時間 TCS があれば言語は P に属する。

判定器は `comp (pair id M.M) R.V`: `x ↦ enc x (M x) ↦ R.V`。
`M` が YES インスタンスで証拠を出すので、これは `R.lang` を判定する。
-/
theorem lang_inP_of_polyTime_tcs {R : NPRel} {M : TCS R} (h : PolyTime M.M) :
    R.lang ∈ ClassP := by
  refine ⟨Prog.comp (Prog.pair Prog.id M.M) R.V,
    polyTime_comp (polyTime_pair polyTime_id h) R.V_poly, ?_, ?_⟩
  · intro x
    obtain ⟨y, t, he⟩ := (polyTime_comp (polyTime_pair polyTime_id h) R.V_poly).total x
    exact ⟨y, t, he⟩
  · intro x y t hev
    obtain ⟨m, tp, tv, hp, hv, -⟩ := hev.comp_inv
    -- m = enc x (M x)
    obtain ⟨y₁, y₂, t₁, t₂, he₁, he₂, hm, -⟩ := hp.pair_inv
    rw [he₁.id_inv] at hm
    rw [← TCS.out_eq he₂] at hm
    subst hm
    rw [R.V_decides x (M.out x) y tv hv]
    constructor
    · intro hrel; exact ⟨_, hrel⟩
    · intro hx; exact M.out_correct hx
