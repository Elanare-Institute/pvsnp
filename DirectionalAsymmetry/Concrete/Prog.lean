/-
# プログラム言語（深い埋め込み）とコスト意味論

v3 指示書 §3.2–3.4。

**原則 (P1)**: 時間は実行から導出する。構造体に時間フィールドを持たせない。
**要件 (R1)**: 任意の Lean 関数を受け取る構成子は禁止（計算がタダにならないため）。
**要件 (R2)**: 各プリミティブのコストは「1 + 読む入力長 + 出力長」以上。
これによりサイズ–コスト不変量 `Eval.size_le` が成り立ち、
n ステップで長さ 2^n のデータを作ることができなくなる。
-/
import DirectionalAsymmetry.Concrete.Encoding

open Encoding

/-- プログラムの構文。固定の単純な操作のみを構成子とする（R1）。 -/
inductive Prog where
  /-- x ↦ x -/
  | id : Prog
  /-- x ↦ w -/
  | const (w : BStr) : Prog
  /-- x ↦ x.take 1 -/
  | head : Prog
  /-- x ↦ x.drop 1 -/
  | tail : Prog
  /-- y ↦ (dec y).1 -/
  | fst : Prog
  /-- y ↦ (dec y).2 -/
  | snd : Prog
  /-- y ↦ (dec y).1 ++ (dec y).2 -/
  | append : Prog
  /-- x ↦ [decide (x = w)] -/
  | eqConst (w : BStr) : Prog
  /-- x ↦ g (f x) -/
  | comp (f g : Prog) : Prog
  /-- x ↦ enc (f x) (g x) -/
  | pair (f g : Prog) : Prog
  /-- c x = [true] なら f x、それ以外なら g x -/
  | ite (c f g : Prog) : Prog
  /-- c s = [true] の間 s := b s。止まったら s を返す -/
  | loop (c b : Prog) : Prog
  deriving DecidableEq, Repr

namespace Prog

/--
大ステップのコスト意味論。`Eval P x y t` は
「P は入力 x で出力 y を返し、t ステップで停止する」。

発散する実行には導出が存在しない（部分関数）。
-/
inductive Eval : Prog → BStr → BStr → ℕ → Prop where
  | id (x : BStr) : Eval Prog.id x x (1 + 2 * x.length)
  | const (w x : BStr) : Eval (Prog.const w) x w (1 + w.length)
  | head (x : BStr) : Eval Prog.head x (x.take 1) (1 + x.length + (x.take 1).length)
  | tail (x : BStr) : Eval Prog.tail x (x.drop 1) (1 + x.length + (x.drop 1).length)
  | fst (x : BStr) : Eval Prog.fst x (dec x).1 (1 + x.length + (dec x).1.length)
  | snd (x : BStr) : Eval Prog.snd x (dec x).2 (1 + x.length + (dec x).2.length)
  | append (x : BStr) :
      Eval Prog.append x ((dec x).1 ++ (dec x).2)
        (1 + x.length + ((dec x).1 ++ (dec x).2).length)
  | eqConst (w x : BStr) :
      Eval (Prog.eqConst w) x [decide (x = w)] (2 + x.length + w.length)
  | comp {f g : Prog} {x y z : BStr} {tf tg : ℕ} :
      Eval f x y tf → Eval g y z tg → Eval (Prog.comp f g) x z (tf + tg + 1)
  | pair {f g : Prog} {x y z : BStr} {tf tg : ℕ} :
      Eval f x y tf → Eval g x z tg →
      Eval (Prog.pair f g) x (enc y z) (tf + tg + 1 + (enc y z).length)
  | ite_true {c f g : Prog} {x y : BStr} {tc tf : ℕ} :
      Eval c x [true] tc → Eval f x y tf → Eval (Prog.ite c f g) x y (tc + tf + 1)
  | ite_false {c f g : Prog} {x r y : BStr} {tc tg : ℕ} :
      Eval c x r tc → r ≠ [true] → Eval g x y tg →
      Eval (Prog.ite c f g) x y (tc + tg + 1)
  | loop_stop {c b : Prog} {s r : BStr} {tc : ℕ} :
      Eval c s r tc → r ≠ [true] → Eval (Prog.loop c b) s s (tc + 1)
  | loop_step {c b : Prog} {s s' y : BStr} {tc tb t : ℕ} :
      Eval c s [true] tc → Eval b s s' tb → Eval (Prog.loop c b) s' y t →
      Eval (Prog.loop c b) s y (tc + tb + t + 1)

/-- 意味論は決定的: 出力と時間がともに一意。 -/
theorem Eval.deterministic {P : Prog} {x y y' : BStr} {t t' : ℕ}
    (h : Eval P x y t) (h' : Eval P x y' t') : y = y' ∧ t = t' := by
  induction h generalizing y' t' with
  | id x => cases h'; exact ⟨rfl, rfl⟩
  | const w x => cases h'; exact ⟨rfl, rfl⟩
  | head x => cases h'; exact ⟨rfl, rfl⟩
  | tail x => cases h'; exact ⟨rfl, rfl⟩
  | fst x => cases h'; exact ⟨rfl, rfl⟩
  | snd x => cases h'; exact ⟨rfl, rfl⟩
  | append x => cases h'; exact ⟨rfl, rfl⟩
  | eqConst w x => cases h'; exact ⟨rfl, rfl⟩
  | comp hf hg ihf ihg =>
      cases h' with
      | comp hf' hg' =>
          obtain ⟨rfl, rfl⟩ := ihf hf'
          obtain ⟨rfl, rfl⟩ := ihg hg'
          exact ⟨rfl, rfl⟩
  | pair hf hg ihf ihg =>
      cases h' with
      | pair hf' hg' =>
          obtain ⟨rfl, rfl⟩ := ihf hf'
          obtain ⟨rfl, rfl⟩ := ihg hg'
          exact ⟨rfl, rfl⟩
  | ite_true hc hf ihc ihf =>
      cases h' with
      | ite_true hc' hf' =>
          obtain ⟨-, rfl⟩ := ihc hc'
          obtain ⟨rfl, rfl⟩ := ihf hf'
          exact ⟨rfl, rfl⟩
      | ite_false hc' hne hg' =>
          obtain ⟨rfl, -⟩ := ihc hc'
          exact absurd rfl hne
  | ite_false hc hne hg ihc ihg =>
      cases h' with
      | ite_true hc' hf' =>
          obtain ⟨rfl, -⟩ := ihc hc'
          exact absurd rfl hne
      | ite_false hc' hne' hg' =>
          obtain ⟨rfl, rfl⟩ := ihc hc'
          obtain ⟨rfl, rfl⟩ := ihg hg'
          exact ⟨rfl, rfl⟩
  | loop_stop hc hne ihc =>
      cases h' with
      | loop_stop hc' hne' =>
          obtain ⟨rfl, rfl⟩ := ihc hc'
          exact ⟨rfl, rfl⟩
      | loop_step hc' hb' hl' =>
          obtain ⟨rfl, -⟩ := ihc hc'
          exact absurd rfl hne
  | loop_step hc hb hl ihc ihb ihl =>
      cases h' with
      | loop_stop hc' hne' =>
          obtain ⟨rfl, -⟩ := ihc hc'
          exact absurd rfl hne'
      | loop_step hc' hb' hl' =>
          obtain ⟨-, rfl⟩ := ihc hc'
          obtain ⟨rfl, rfl⟩ := ihb hb'
          obtain ⟨rfl, rfl⟩ := ihl hl'
          exact ⟨rfl, rfl⟩

/-- 出力は一意。 -/
theorem Eval.out_unique {P : Prog} {x y y' : BStr} {t t' : ℕ}
    (h : Eval P x y t) (h' : Eval P x y' t') : y = y' := (h.deterministic h').1

/-- 時間は一意。 -/
theorem Eval.time_unique {P : Prog} {x y y' : BStr} {t t' : ℕ}
    (h : Eval P x y t) (h' : Eval P x y' t') : t = t' := (h.deterministic h').2

/-- コストは正。 -/
theorem Eval.cost_pos {P : Prog} {x y : BStr} {t : ℕ} (h : Eval P x y t) : 1 ≤ t := by
  induction h with
  | id x => omega
  | const w x => omega
  | head x => omega
  | tail x => omega
  | fst x => omega
  | snd x => omega
  | append x => omega
  | eqConst w x => omega
  | comp _ _ ihf ihg => omega
  | pair _ _ ihf ihg => omega
  | ite_true _ _ ihc ihf => omega
  | ite_false _ _ _ ihc ihg => omega
  | loop_stop _ _ ihc => omega
  | loop_step _ _ _ ihc ihb ihl => omega

/--
**サイズ–コスト不変量**（要件 R2 の帰結）。

出力長は入力長 + コストを超えない。これにより
単位コストでのデータ倍化が不可能になり、
「多項式ステップ」が多項式時間の意味を保つ。
-/
theorem Eval.size_le {P : Prog} {x y : BStr} {t : ℕ} (h : Eval P x y t) :
    y.length ≤ x.length + t := by
  induction h with
  | id x => omega
  | const w x => omega
  | head x => have := List.length_take_le 1 x; omega
  | tail x => omega
  | fst x => have := dec_fst_length_le x; omega
  | snd x => have := dec_snd_length_le x; omega
  | append x => omega
  | eqConst w x => simp; omega
  | comp hf hg ihf ihg => omega
  | pair hf hg ihf ihg => omega
  | ite_true _ _ ihc ihf => omega
  | ite_false _ _ _ ihc ihg => omega
  | loop_stop _ _ ihc => omega
  | loop_step _ _ _ ihc ihb ihl => omega

/-! ### 反転補題 -/

theorem Eval.id_inv {x y : BStr} {t : ℕ} (h : Eval Prog.id x y t) : y = x := by
  cases h; rfl

theorem Eval.const_inv {w x y : BStr} {t : ℕ} (h : Eval (Prog.const w) x y t) : y = w := by
  cases h; rfl

theorem Eval.fst_inv {x y : BStr} {t : ℕ} (h : Eval Prog.fst x y t) : y = (dec x).1 := by
  cases h; rfl

theorem Eval.snd_inv {x y : BStr} {t : ℕ} (h : Eval Prog.snd x y t) : y = (dec x).2 := by
  cases h; rfl

theorem Eval.append_inv {x y : BStr} {t : ℕ} (h : Eval Prog.append x y t) :
    y = (dec x).1 ++ (dec x).2 := by
  cases h; rfl

theorem Eval.eqConst_inv {w x y : BStr} {t : ℕ} (h : Eval (Prog.eqConst w) x y t) :
    y = [decide (x = w)] := by
  cases h; rfl

theorem Eval.comp_inv {f g : Prog} {x z : BStr} {t : ℕ} (h : Eval (Prog.comp f g) x z t) :
    ∃ y tf tg, Eval f x y tf ∧ Eval g y z tg ∧ t = tf + tg + 1 := by
  cases h with
  | comp hf hg => exact ⟨_, _, _, hf, hg, rfl⟩

theorem Eval.pair_inv {f g : Prog} {x z : BStr} {t : ℕ} (h : Eval (Prog.pair f g) x z t) :
    ∃ y₁ y₂ tf tg, Eval f x y₁ tf ∧ Eval g x y₂ tg ∧ z = enc y₁ y₂ ∧
      t = tf + tg + 1 + (enc y₁ y₂).length := by
  cases h with
  | pair hf hg => exact ⟨_, _, _, _, hf, hg, rfl, rfl⟩

theorem Eval.ite_inv {c f g : Prog} {x y : BStr} {t : ℕ} (h : Eval (Prog.ite c f g) x y t) :
    (∃ tc tf, Eval c x [true] tc ∧ Eval f x y tf ∧ t = tc + tf + 1) ∨
    (∃ r tc tg, Eval c x r tc ∧ r ≠ [true] ∧ Eval g x y tg ∧ t = tc + tg + 1) := by
  cases h with
  | ite_true hc hf => exact Or.inl ⟨_, _, hc, hf, rfl⟩
  | ite_false hc hne hg => exact Or.inr ⟨_, _, _, hc, hne, hg, rfl⟩

theorem Eval.loop_inv {c b : Prog} {s y : BStr} {t : ℕ} (h : Eval (Prog.loop c b) s y t) :
    (∃ r tc, Eval c s r tc ∧ r ≠ [true] ∧ y = s ∧ t = tc + 1) ∨
    (∃ s' tc tb t', Eval c s [true] tc ∧ Eval b s s' tb ∧
      Eval (Prog.loop c b) s' y t' ∧ t = tc + tb + t' + 1) := by
  cases h with
  | loop_stop hc hne => exact Or.inl ⟨_, _, hc, hne, rfl, rfl⟩
  | loop_step hc hb hl => exact Or.inr ⟨_, _, _, _, hc, hb, hl, rfl⟩

end Prog
