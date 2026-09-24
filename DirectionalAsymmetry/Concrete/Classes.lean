/-
# 計算量クラス: PolyTime, ClassP, NPRel, ClassNP, PeqNP, Reduces, IsNPComplete

v3 指示書 §4。

`V_poly` は「長い証拠も含めたすべての入力」で時間を縛る。
これにより v2 の反例（短い証拠についてしか縛っていなかった）が
構造的に起きなくなる。
-/
import DirectionalAsymmetry.Concrete.Poly
import DirectionalAsymmetry.Concrete.Interp

open Encoding Prog

/-- プログラムが全域かつ多項式時間。 -/
def PolyTime (P : Prog) : Prop :=
  ∃ c k : ℕ, ∀ x, ∃ y t, Eval P x y t ∧ t ≤ c * (x.length + 1) ^ k

/-- `PolyTime` なら全域。 -/
theorem PolyTime.total {P : Prog} (h : PolyTime P) (x : BStr) : ∃ y t, Eval P x y t := by
  obtain ⟨c, k, hc⟩ := h
  obtain ⟨y, t, he, -⟩ := hc x
  exact ⟨y, t, he⟩

/-- プログラム `D` が言語 `L` を判定する。 -/
def Decides (D : Prog) (L : Set BStr) : Prop :=
  (∀ x, ∃ y t, Eval D x y t) ∧ ∀ x y t, Eval D x y t → (y = [true] ↔ x ∈ L)

/-- クラス P。 -/
def ClassP : Set (Set BStr) := {L | ∃ D, PolyTime D ∧ Decides D L}

/-- Definition 1: NP relation。 -/
structure NPRel where
  rel       : BStr → BStr → Prop
  V         : Prog
  V_poly    : PolyTime V
  V_decides : ∀ x w y t, Eval V (enc x w) y t → (y = [true] ↔ rel x w)
  q         : ℕ → ℕ
  q_poly    : PolyBound q
  bound     : ∀ x w, rel x w → w.length ≤ q x.length

/-- NP relation が定める言語。 -/
def NPRel.lang (R : NPRel) : Set BStr := {x | ∃ w, R.rel x w}

@[simp] theorem NPRel.mem_lang {R : NPRel} {x : BStr} :
    x ∈ R.lang ↔ ∃ w, R.rel x w := Iff.rfl

/-- クラス NP。 -/
def ClassNP : Set (Set BStr) := {L | ∃ R : NPRel, R.lang = L}

/-- P = NP（NP ⊆ P と同値。P ⊆ NP は定理）。 -/
def PeqNP : Prop := ClassNP ⊆ ClassP

/-- 多項式時間多対一帰着。 -/
def Reduces (L₁ L₂ : Set BStr) : Prop :=
  ∃ f, PolyTime f ∧ ∀ x y t, Eval f x y t → (x ∈ L₁ ↔ y ∈ L₂)

/-- NP 完全性。 -/
def IsNPComplete (L : Set BStr) : Prop := L ∈ ClassNP ∧ ∀ L' ∈ ClassNP, Reduces L' L

section Closure

/-- 合成の多項式時間性。サイズ–コスト不変量で中間出力長を抑える。 -/
theorem polyTime_comp {f g : Prog} (hf : PolyTime f) (hg : PolyTime g) :
    PolyTime (Prog.comp f g) := by
  obtain ⟨cf, kf, hcf⟩ := hf
  obtain ⟨cg, kg, hcg⟩ := hg
  -- 中間出力 y の長さは |x| + tf ≤ |x| + cf*(|x|+1)^kf ≤ (1+cf)*(|x|+1)^(kf+1)
  refine ⟨cf + cg * (1 + cf) ^ kg + 1, (kf + 1) + (kf + 1) * kg, fun x => ?_⟩
  obtain ⟨y, tf, hef, htf⟩ := hcf x
  obtain ⟨z, tg, heg, htg⟩ := hcg y
  refine ⟨z, tf + tg + 1, Eval.comp hef heg, ?_⟩
  set n := x.length with hn
  -- |y| + 1 ≤ (1 + cf) * (n+1)^(kf+1)
  have hylen : y.length + 1 ≤ (1 + cf) * (n + 1) ^ (kf + 1) := by
    have h1 := hef.size_le
    have hp : (n + 1) ^ kf * (n + 1) = (n + 1) ^ (kf + 1) := by ring
    have hge : n + 1 ≤ (n + 1) ^ (kf + 1) := by
      have : (n + 1) ^ 1 ≤ (n + 1) ^ (kf + 1) :=
        Nat.pow_le_pow_right (by omega) (by omega)
      simpa using this
    have hkf : cf * (n + 1) ^ kf ≤ cf * (n + 1) ^ (kf + 1) :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) (by omega))
    calc y.length + 1 ≤ n + tf + 1 := by omega
      _ ≤ n + cf * (n + 1) ^ kf + 1 := by omega
      _ ≤ (n + 1) ^ (kf + 1) + cf * (n + 1) ^ (kf + 1) := by omega
      _ = (1 + cf) * (n + 1) ^ (kf + 1) := by ring
  have htg' : tg ≤ cg * (1 + cf) ^ kg * (n + 1) ^ ((kf + 1) * kg) := by
    calc tg ≤ cg * (y.length + 1) ^ kg := htg
      _ ≤ cg * ((1 + cf) * (n + 1) ^ (kf + 1)) ^ kg :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hylen _)
      _ = cg * (1 + cf) ^ kg * (n + 1) ^ ((kf + 1) * kg) := by
          rw [Nat.mul_pow, ← pow_mul]; ring
  set K := (kf + 1) + (kf + 1) * kg with hK
  have hone : (1 : ℕ) ≤ (n + 1) ^ K := Nat.one_le_pow _ _ (by omega)
  have hf1 : (n + 1) ^ kf ≤ (n + 1) ^ K :=
    Nat.pow_le_pow_right (by omega) (by omega)
  have hf2 : (n + 1) ^ ((kf + 1) * kg) ≤ (n + 1) ^ K :=
    Nat.pow_le_pow_right (by omega) (by omega)
  have e1 : tf ≤ cf * (n + 1) ^ K := le_trans htf (Nat.mul_le_mul_left _ hf1)
  have e2 : tg ≤ cg * (1 + cf) ^ kg * (n + 1) ^ K :=
    le_trans htg' (Nat.mul_le_mul_left _ hf2)
  calc tf + tg + 1
      ≤ cf * (n + 1) ^ K + cg * (1 + cf) ^ kg * (n + 1) ^ K + 1 * (n + 1) ^ K := by
        omega
    _ = (cf + cg * (1 + cf) ^ kg + 1) * (n + 1) ^ K := by ring

/-- 対の多項式時間性。 -/
theorem polyTime_pair {f g : Prog} (hf : PolyTime f) (hg : PolyTime g) :
    PolyTime (Prog.pair f g) := by
  obtain ⟨cf, kf, hcf⟩ := hf
  obtain ⟨cg, kg, hcg⟩ := hg
  -- コストは tf + tg + 1 + |enc y z|、|enc y z| = 2|y|+1+|z|
  refine ⟨3 * cf + 3 * cg + 4, max kf kg + 1, fun x => ?_⟩
  obtain ⟨y, tf, hef, htf⟩ := hcf x
  obtain ⟨z, tg, heg, htg⟩ := hcg x
  refine ⟨enc y z, tf + tg + 1 + (enc y z).length, Eval.pair hef heg, ?_⟩
  have hy := hef.size_le
  have hz := heg.size_le
  rw [enc_length]
  set n := x.length with hn
  set K := max kf kg + 1 with hK
  have hfK : (n + 1) ^ kf ≤ (n + 1) ^ K :=
    Nat.pow_le_pow_right (by omega) (by omega)
  have hgK : (n + 1) ^ kg ≤ (n + 1) ^ K :=
    Nat.pow_le_pow_right (by omega) (by omega)
  have hnK : n + 1 ≤ (n + 1) ^ K := by
    have : (n + 1) ^ 1 ≤ (n + 1) ^ K := Nat.pow_le_pow_right (by omega) (by omega)
    simpa using this
  have htf' : tf ≤ cf * (n + 1) ^ K := le_trans htf (Nat.mul_le_mul_left _ hfK)
  have htg' : tg ≤ cg * (n + 1) ^ K := le_trans htg (Nat.mul_le_mul_left _ hgK)
  -- 2|y|+1+|z| ≤ 2(n+tf)+1+(n+tg) = 3n+2tf+tg+1
  calc tf + tg + 1 + (2 * y.length + 1 + z.length)
      ≤ 3 * tf + 3 * tg + 3 * (n + 1) := by omega
    _ ≤ 3 * (cf * (n + 1) ^ K) + 3 * (cg * (n + 1) ^ K) + 3 * (n + 1) ^ K := by
        omega
    _ ≤ (3 * cf + 3 * cg + 4) * (n + 1) ^ K := by ring_nf; omega

/-- 条件分岐の多項式時間性。 -/
theorem polyTime_ite {c f g : Prog} (hc : PolyTime c) (hf : PolyTime f) (hg : PolyTime g) :
    PolyTime (Prog.ite c f g) := by
  obtain ⟨cc, kc, hcc⟩ := hc
  obtain ⟨cf, kf, hcf⟩ := hf
  obtain ⟨cg, kg, hcg⟩ := hg
  refine ⟨cc + cf + cg + 1, max kc (max kf kg), fun x => ?_⟩
  obtain ⟨r, tc, hec, htc⟩ := hcc x
  set n := x.length
  set K := max kc (max kf kg)
  have hcK : (n + 1) ^ kc ≤ (n + 1) ^ K := Nat.pow_le_pow_right (by omega) (le_max_left _ _)
  have hfK : (n + 1) ^ kf ≤ (n + 1) ^ K :=
    Nat.pow_le_pow_right (by omega) (le_trans (le_max_left _ _) (le_max_right _ _))
  have hgK : (n + 1) ^ kg ≤ (n + 1) ^ K :=
    Nat.pow_le_pow_right (by omega) (le_trans (le_max_right _ _) (le_max_right _ _))
  have hone : (1 : ℕ) ≤ (n + 1) ^ K := Nat.one_le_pow _ _ (by omega)
  by_cases hr : r = [true]
  · subst hr
    obtain ⟨y, tf, hef, htf⟩ := hcf x
    refine ⟨y, tc + tf + 1, Eval.ite_true hec hef, ?_⟩
    have h1 : tc ≤ cc * (n + 1) ^ K := le_trans htc (Nat.mul_le_mul_left _ hcK)
    have h2 : tf ≤ cf * (n + 1) ^ K := le_trans htf (Nat.mul_le_mul_left _ hfK)
    nlinarith
  · obtain ⟨y, tg, heg, htg⟩ := hcg x
    refine ⟨y, tc + tg + 1, Eval.ite_false hec hr heg, ?_⟩
    have h1 : tc ≤ cc * (n + 1) ^ K := le_trans htc (Nat.mul_le_mul_left _ hcK)
    have h2 : tg ≤ cg * (n + 1) ^ K := le_trans htg (Nat.mul_le_mul_left _ hgK)
    nlinarith

theorem polyTime_id : PolyTime Prog.id := ⟨2, 1, fun x => ⟨x, _, Eval.id x, by simp; nlinarith⟩⟩

theorem polyTime_const (w : BStr) : PolyTime (Prog.const w) :=
  ⟨1 + w.length, 0, fun x => ⟨w, _, Eval.const w x, by simp⟩⟩

theorem polyTime_fst : PolyTime Prog.fst :=
  ⟨3, 1, fun x => ⟨_, _, Eval.fst x, by
    have := dec_fst_length_le x; simp; nlinarith⟩⟩

theorem polyTime_snd : PolyTime Prog.snd :=
  ⟨3, 1, fun x => ⟨_, _, Eval.snd x, by
    have := dec_snd_length_le x; simp; nlinarith⟩⟩

theorem polyTime_append : PolyTime Prog.append :=
  ⟨4, 1, fun x => ⟨_, _, Eval.append x, by
    have h1 := dec_fst_length_le x
    have h2 := dec_snd_length_le x
    simp; nlinarith⟩⟩

theorem polyTime_eqConst (w : BStr) : PolyTime (Prog.eqConst w) :=
  ⟨2 + w.length, 1, fun x => ⟨_, _, Eval.eqConst w x, by simp; nlinarith⟩⟩

end Closure

section Basic

/-- 空の証拠しか持たない relation の verifier: `enc x [] ↦ D x`。 -/
private def pVerifier (D : Prog) : Prog :=
  Prog.ite (Prog.comp Prog.snd (Prog.eqConst []))
    (Prog.comp Prog.fst D) (Prog.const [false])

/-- **P ⊆ NP**。 -/
theorem p_sub_np : ClassP ⊆ ClassNP := by
  rintro L ⟨D, hDpoly, hDtotal, hDdec⟩
  refine ⟨{ rel := fun x w => x ∈ L ∧ w = []
            V := pVerifier D
            V_poly := polyTime_ite (polyTime_comp polyTime_snd (polyTime_eqConst []))
                        (polyTime_comp polyTime_fst hDpoly) (polyTime_const [false])
            V_decides := ?_
            q := fun _ => 0
            q_poly := PolyBound.const 0
            bound := ?_ }, ?_⟩
  · -- V_decides
    intro x w y t hev
    rcases hev.ite_inv with ⟨tc, tf, hc, hf, -⟩ | ⟨r, tc, tg, hc, hne, hg, -⟩
    · -- 条件が true: snd (enc x w) = [] すなわち w = []
      obtain ⟨m, tp, tq, hp, hq, -⟩ := hc.comp_inv
      rw [hp.snd_inv, dec_enc] at hq
      have hw : w = [] := by
        have := hq.eqConst_inv
        simp at this
        by_contra hc2
        simp [hc2] at this
      subst hw
      -- 本体: fst (enc x []) = x を D に渡す
      obtain ⟨m2, tp2, tq2, hp2, hq2, -⟩ := hf.comp_inv
      rw [hp2.fst_inv, dec_enc] at hq2
      rw [hDdec _ _ _ hq2]
      simp
    · -- 条件が false: w ≠ []、出力は [false]
      obtain ⟨m, tp, tq, hp, hq, -⟩ := hc.comp_inv
      rw [hp.snd_inv, dec_enc] at hq
      rw [hg.const_inv]
      have hw : w ≠ [] := by
        intro hw
        subst hw
        rw [hq.eqConst_inv] at hne
        simp at hne
      simp [hw]
  · intro x w hw; simp [hw.2]
  · ext x
    simp only [NPRel.mem_lang]
    constructor
    · rintro ⟨w, hx, -⟩; exact hx
    · intro hx; exact ⟨[], hx, rfl⟩

/-- 帰着による P への所属の移送。 -/
theorem inP_of_reduces {L₁ L₂ : Set BStr} (hred : Reduces L₁ L₂) (h₂ : L₂ ∈ ClassP) :
    L₁ ∈ ClassP := by
  obtain ⟨f, hfpoly, hfred⟩ := hred
  obtain ⟨D, hDpoly, hDtotal, hDdec⟩ := h₂
  refine ⟨Prog.comp f D, polyTime_comp hfpoly hDpoly, ?_, ?_⟩
  · intro x
    obtain ⟨y, tf, hef⟩ := hfpoly.total x
    obtain ⟨z, td, hed⟩ := hDpoly.total y
    exact ⟨z, tf + td + 1, Eval.comp hef hed⟩
  · intro x y t hev
    cases hev with
    | comp hef hed =>
        rename_i y1 tf td
        rw [hDdec _ _ _ hed]
        exact (hfred _ _ _ hef).symm

/-- 自明な NP relation（証拠を持つ入力が存在しない）。 -/
def trivialRel : NPRel where
  rel _ _ := False
  V := Prog.const [false]
  V_poly := polyTime_const [false]
  V_decides := by
    intro x w y t hev
    cases hev
    simp
  q := fun _ => 0
  q_poly := PolyBound.const 0
  bound := fun _ _ h => h.elim

@[simp] theorem trivialRel_lang : trivialRel.lang = (∅ : Set BStr) := by
  ext x; simp [NPRel.lang, trivialRel]

instance : Nonempty NPRel := ⟨trivialRel⟩

end Basic
