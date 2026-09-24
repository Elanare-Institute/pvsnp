/-
# Haken の仮定と系3

v4 指示書 §8。

**原則 (P2)**: 独自 `axiom` をゼロにする。
Haken (1985) の下界は `def HakenLB : Prop` として定義し、
系3の**仮定**として明示する。Haken の証明自体は形式化しない。
-/
import DirectionalAsymmetry.Restricted.Bridge
import DirectionalAsymmetry.Restricted.Pigeonhole

open Encoding RestrictedEncoding

/-! ## 線形は指数より真に小さい（系3の最後の比較で使う） -/

/-- `b(m+1) < 2^m`（`m ≥ 4b+4`）。 -/
theorem lin_lt_exp (b : ℕ) : ∀ m, 4*b+4 ≤ m → b * (m+1) < 2 ^ m := by
  intro m
  induction m with
  | zero => intro h; omega
  | succ p ih =>
      intro hm
      rcases Nat.lt_or_ge (4*b+4) (p+1) with hp | hp
      · -- p ≥ 4b+4 なので帰納法が使える
        have hrec := ih (by omega)
        have he : (2:ℕ)^(p+1) = 2 * 2^p := by ring
        have hstep : b*((p+1)+1) ≤ 2*(b*(p+1)) := by nlinarith
        calc b * ((p+1)+1) ≤ 2*(b*(p+1)) := hstep
          _ < 2 * 2^p := by omega
          _ = 2^(p+1) := he.symm
      · -- p+1 = 4b+4 ちょうど
        have hpe : p + 1 = 4*b+4 := by omega
        rw [hpe]
        -- b*(4b+5) < 2^(4b+4) を示す
        have hge : ∀ c:ℕ, (c+1)*(c+1) ≤ 2^(2*c) := by
          intro c
          induction c with
          | zero => norm_num
          | succ d ihd =>
              have he2 : (2:ℕ)^(2*(d+1)) = 4 * 2^(2*d) := by ring
              nlinarith
        have h1 := hge (2*b+1)
        have he3 : (2:ℕ)^(2*(2*b+1)) = 2^(4*b+2) := by ring_nf
        have he4 : (2:ℕ)^(4*b+4) = 4 * 2^(4*b+2) := by ring
        nlinarith

/--
**`n/k` は `c(log₂ n + 1)` をいずれ追い越す**。

`m := log₂ n` とすると `2^m ≤ n`。`lin_lt_exp` から
`c*k*(m+1) < 2^m ≤ n` なので `c(m+1) < n/k`。
-/
theorem log_lt_div (c k : ℕ) (hk : 0 < k) :
    ∃ N, ∀ n ≥ N, c * (Nat.log 2 n + 1) < n / k := by
  set b := c * k + k with hb
  refine ⟨2 ^ (4 * b + 4), fun n hn => ?_⟩
  have hn0 : n ≠ 0 := by
    have : 0 < 2 ^ (4 * b + 4) := Nat.two_pow_pos _
    omega
  set m := Nat.log 2 n with hm
  -- 2^(4b+4) ≤ n なので 4b+4 ≤ m
  have hmge : 4 * b + 4 ≤ m := by
    rw [hm]
    rw [Nat.le_log_iff_pow_le (by norm_num) (by omega)]
    exact hn
  -- 2^m ≤ n
  have hpow : 2 ^ m ≤ n := Nat.pow_log_le_self 2 hn0
  -- b(m+1) < 2^m ≤ n
  have hlin := lin_lt_exp b m hmge
  -- c(m+1) < n/k
  -- b = ck + k なので b(m+1) = c(m+1)k + k(m+1) ≥ c(m+1)k + k
  have hkey : c * (m + 1) * k + k < n := by
    calc c * (m + 1) * k + k ≤ b * (m + 1) := by
          rw [hb]; nlinarith
      _ < 2 ^ m := hlin
      _ ≤ n := hpow
  -- c(m+1)*k < n から c(m+1) < n/k
  -- n ≥ c(m+1)k + k なので n/k ≥ c(m+1) + 1 > c(m+1)
  have hle : (c * (m + 1) + 1) * k ≤ n := by
    have : (c * (m + 1) + 1) * k = c * (m + 1) * k + k := by ring
    omega
  have := Nat.le_div_iff_mul_le hk |>.mpr hle
  omega

/--
Haken (1985) の下界。

鳩の巣原理の式の一般 resolution 反証は指数サイズ。
論文では文献の定理として引用する。v4 では**仮定**として置く
（`axiom` にはしない）。
-/
def HakenLB : Prop :=
  ∃ k N : ℕ, 0 < k ∧ ∀ n ≥ N, ∀ π : GenRefutation (php n), 2 ^ (n / k) ≤ π.size

/--
木状 resolution でも同じ下界が出る。

木状反証は一般反証に変換でき（`tree_to_gen`）、サイズは増えないので、
一般の下界がそのまま木状の下界になる。
-/
theorem hakenLB_tree (h : HakenLB) :
    ∃ k N : ℕ, 0 < k ∧ ∀ n ≥ N, ∀ τ : TreeRefutation (php n), 2 ^ (n / k) ≤ τ.size := by
  obtain ⟨k, N, hk, hlb⟩ := h
  refine ⟨k, N, hk, fun n hn τ => ?_⟩
  obtain ⟨π, hπ⟩ := tree_to_gen τ
  exact le_trans (hlb n hn π) hπ

/-- どの証明体系でも Haken の下界が成り立つ。 -/
theorem hakenLB_minSize (h : HakenLB) (S : ProofKind) :
    ∃ k N : ℕ, 0 < k ∧ ∀ n ≥ N, ∀ π : Refutation S (php n), 2 ^ (n / k) ≤ π.size := by
  cases S with
  | treeLike => exact hakenLB_tree h
  | general => exact h

/--
Haken の下界から、最小反証サイズの下界が出る。

ただし「反証が存在する」ことが要る（`minSize` は `sInf ∅ = 0` なので）。
`php n` は充足不能なので、`ResSolver` の `extract` から反証が得られる。
-/
theorem structAsym_php_ge (h : HakenLB) (S : ProofKind) :
    ∃ k N : ℕ, 0 < k ∧ ∀ n ≥ N, (∃ _ : Refutation S (php n), True) →
      n / k ≤ structAsym S (php n) := by
  obtain ⟨k, N, hk, hlb⟩ := hakenLB_minSize h S
  refine ⟨k, N, hk, fun n hn hex => ?_⟩
  obtain ⟨π, -⟩ := hex
  -- minSize は達成される（ℕ の整列性）
  unfold structAsym
  have hne : { m | ∃ ρ : Refutation S (php n), ρ.size = m }.Nonempty :=
    ⟨π.size, π, rfl⟩
  have hmem := Nat.sInf_mem hne
  obtain ⟨ρ, hρ⟩ := hmem
  have hmin : minSize S (php n) = sInf { m | ∃ ρ : Refutation S (php n), ρ.size = m } := by
    cases S with
    | treeLike => rfl
    | general => rfl
  -- 2^(n/k) ≤ minSize なので n/k ≤ log(minSize)
  have hge : 2 ^ (n / k) ≤ minSize S (php n) := by
    rw [hmin, ← hρ]
    exact hlb n hn ρ
  calc n / k = Nat.log 2 (2 ^ (n / k)) := by rw [Nat.log_pow (by norm_num)]
    _ ≤ Nat.log 2 (minSize S (php n)) := Nat.log_mono_right hge

/--
**系3**: DPLL 型・節学習型のソルバーは、多項式時間の全候補ソルバーになれない。

Haken の下界を仮定として置く。

証明:
1. `x_n := encodeCNF (php n)` は充足不能（`php_unsat` と `decodeCNF_encodeCNF`）。
2. 定理3と Haken から `asym M x_n ≥ n/k − C(log|x_n| + 1)`。
3. `|x_n|` は `n` の多項式なので `log|x_n| = O(log n)`。
4. `profile` は長さ `|x_n|` の入力にわたる最大値なので `profile ≥ asym M x_n`。
5. `LogBounded` なら `profile ≤ C''(log|x_n| + 1) = O(log n)` だが、
   2・3 から `profile ≥ n/k − O(log n)`。`n` が大きいと矛盾。
-/
theorem no_polytime_res_solver (h : HakenLB) (S : ProofKind) (R : NPRel)
    (hR : ImplementsSAT R) (M : ResSolver S R) :
    ¬ LogBounded (profile M.tcs) := by
  rintro ⟨Cp, hCp⟩
  -- 定理3の定数
  obtain ⟨Cb, hCb⟩ := bridge_resolution S R hR M
  -- Haken の定数
  obtain ⟨k, N, hk, hlb⟩ := structAsym_php_ge h S
  -- 符号化長の多項式上界
  obtain ⟨cL, kL, hcL⟩ := php_encode_polyBound
  -- log|x_n| ≤ CL(log n + 1)
  obtain ⟨CL, hCL⟩ := log_poly_le (⟨cL, kL, hcL⟩ : PolyBound _)
  -- 全体の定数: profile ≤ Cp(log|x_n|+1) ≤ Cp(CL(log n+1)+1) ≤ 2 Cp CL (log n + 1)
  -- asym ≥ n/k − Cb(log|x_n|+1) ≥ n/k − Cb CL(log n+1) − Cb
  -- よって n/k ≤ (2 Cp CL + 2 Cb CL + 2 Cb + 2)(log n + 1) となる n が全て
  set Ctot := 2 * Cp * CL + 2 * Cb * CL + 2 * Cb + 2 * Cp + 2 with hCtot
  obtain ⟨N2, hN2⟩ := log_lt_div Ctot k hk
  -- 十分大きな n で矛盾
  set n := max N (max N2 1) with hn
  have hnN : N ≤ n := le_max_left _ _
  have hnN2 : N2 ≤ n := le_trans (le_max_left _ _) (le_max_right _ _)
  have hn1 : 1 ≤ n := le_trans (le_max_right _ _) (le_max_right _ _)
  set x := encodeCNF (php n) with hx
  -- x は充足不能
  have hunsat : ¬ Satisfiable (decodeCNF x) := by
    rw [hx, decodeCNF_encodeCNF]
    exact php_unsat n
  -- 反証が存在する（extract から）
  obtain ⟨π, -⟩ := M.extract x hunsat
  have hex : ∃ _ : Refutation S (php n), True := by
    rw [hx, decodeCNF_encodeCNF] at π
    exact ⟨π, trivial⟩
  -- structAsym ≥ n/k
  have hstruct : n / k ≤ structAsym S (php n) := hlb n hnN hex
  -- 定理3
  have hbr := hCb x hunsat
  rw [hx, decodeCNF_encodeCNF] at hbr
  -- profile ≥ asym
  have hprof : asym M.tcs x ≤ profile M.tcs x.length := le_profile M.tcs rfl
  -- profile ≤ Cp(log|x|+1)
  have hple := hCp x.length
  -- log|x| ≤ CL(log n + 1)
  have hlogx : Nat.log 2 x.length ≤ CL * (Nat.log 2 n + 1) := hCL n
  -- 整数に持ち上げる
  have hstructZ : (n / k : ℤ) ≤ (structAsym S (php n) : ℤ) := by exact_mod_cast hstruct
  have hlogxZ : (Nat.log 2 x.length : ℤ) ≤ (CL : ℤ) * ((Nat.log 2 n : ℤ) + 1) := by
    exact_mod_cast hlogx
  have hnn : (0:ℤ) ≤ (Nat.log 2 n : ℤ) := Int.natCast_nonneg _
  have hnnx : (0:ℤ) ≤ (Nat.log 2 x.length : ℤ) := Int.natCast_nonneg _
  -- n/k < Ctot(log n + 1)
  have hcontra : (n / k : ℤ) < (Ctot : ℤ) * ((Nat.log 2 n : ℤ) + 1) := by
    calc (n / k : ℤ) ≤ (structAsym S (php n) : ℤ) := hstructZ
      _ ≤ asym M.tcs x + (Cb : ℤ) * ((Nat.log 2 x.length : ℤ) + 1) := by linarith
      _ ≤ profile M.tcs x.length + (Cb : ℤ) * ((Nat.log 2 x.length : ℤ) + 1) := by
          linarith
      _ ≤ (Cp : ℤ) * ((Nat.log 2 x.length : ℤ) + 1)
            + (Cb : ℤ) * ((Nat.log 2 x.length : ℤ) + 1) := by
          have : (profile M.tcs x.length) ≤ (Cp * (Nat.log 2 x.length + 1) : ℕ) := hple
          push_cast at this ⊢
          linarith
      _ < (Ctot : ℤ) * ((Nat.log 2 n : ℤ) + 1) := by
          rw [hCtot]
          push_cast
          nlinarith [Int.natCast_nonneg Cp, Int.natCast_nonneg Cb, Int.natCast_nonneg CL]
  -- しかし log_lt_div から Ctot(log n + 1) < n/k
  have := hN2 n hnN2
  have hZ : (Ctot : ℤ) * ((Nat.log 2 n : ℤ) + 1) < (n / k : ℤ) := by
    have : (Ctot * (Nat.log 2 n + 1) : ℕ) < (n / k : ℕ) := this
    exact_mod_cast this
  omega

/-! ## ボーナス: 予想との接続（指示書 §9.3） -/

/--
予想A′の「制限された設定」版。

v3 の `ConjA` は `residualAsym`（`opaque`、中身なし）を使うが、
制限された設定では `structAsym`（中身のある定義）に置き換えられる。
-/
def ConjA_restricted (S : ProofKind) : Prop :=
  ∀ (R : NPRel), ImplementsSAT R → ∀ (M : ResSolver S R),
    ∃ C : ℕ, ∀ x, ¬ Satisfiable (decodeCNF x) →
      (structAsym S (decodeCNF x) : ℤ) - C * (Nat.log 2 x.length + 1) ≤ asym M.tcs x

/--
**制限された設定では予想A′は定理**（論文 §6.5 の主旨）。

一般の設定では予想のままの主張が、ソルバーの型を限定すると
機械検証可能な定理になる。これが「橋が定理になる場所」の
形式的な内容である。
-/
theorem conjA_restricted_holds (S : ProofKind) : ConjA_restricted S :=
  fun R hR M => bridge_resolution S R hR M
