/-
# 燃料付き実行可能インタプリタと健全性

v3 指示書 §3.6。

`native_decide` は `Lean.ofReduceBool` 公理が混入するので使わない。
`decide` / `rfl` で実行テストできるようにする。
-/
import DirectionalAsymmetry.Concrete.Prog

open Encoding

namespace Prog

/-- 燃料付きインタプリタ。燃料が尽きたら `none`。 -/
def run : ℕ → Prog → BStr → Option (BStr × ℕ)
  | 0, _, _ => none
  | _ + 1, Prog.id, x => some (x, 1 + 2 * x.length)
  | _ + 1, Prog.const w, _ => some (w, 1 + w.length)
  | _ + 1, Prog.head, x => some (x.take 1, 1 + x.length + (x.take 1).length)
  | _ + 1, Prog.tail, x => some (x.drop 1, 1 + x.length + (x.drop 1).length)
  | _ + 1, Prog.fst, x => some ((dec x).1, 1 + x.length + (dec x).1.length)
  | _ + 1, Prog.snd, x => some ((dec x).2, 1 + x.length + (dec x).2.length)
  | _ + 1, Prog.append, x =>
      some ((dec x).1 ++ (dec x).2, 1 + x.length + ((dec x).1 ++ (dec x).2).length)
  | _ + 1, Prog.eqConst w, x => some ([decide (x = w)], 2 + x.length + w.length)
  | n + 1, Prog.comp f g, x =>
      match run n f x with
      | none => none
      | some (y, tf) =>
        match run n g y with
        | none => none
        | some (z, tg) => some (z, tf + tg + 1)
  | n + 1, Prog.pair f g, x =>
      match run n f x with
      | none => none
      | some (y, tf) =>
        match run n g x with
        | none => none
        | some (z, tg) => some (enc y z, tf + tg + 1 + (enc y z).length)
  | n + 1, Prog.ite c f g, x =>
      match run n c x with
      | none => none
      | some (r, tc) =>
        if r = [true] then
          match run n f x with
          | none => none
          | some (y, tf) => some (y, tc + tf + 1)
        else
          match run n g x with
          | none => none
          | some (y, tg) => some (y, tc + tg + 1)
  | n + 1, Prog.loop c b, s =>
      match run n c s with
      | none => none
      | some (r, tc) =>
        if r = [true] then
          match run n b s with
          | none => none
          | some (s', tb) =>
            match run n (Prog.loop c b) s' with
            | none => none
            | some (y, t) => some (y, tc + tb + t + 1)
        else
          some (s, tc + 1)

/-- **健全性**: インタプリタが答えを返せば、それは意味論に従う。 -/
theorem run_sound : ∀ (fuel : ℕ) (P : Prog) (x y : BStr) (t : ℕ),
    run fuel P x = some (y, t) → Eval P x y t := by
  intro fuel
  induction fuel with
  | zero => intro P x y t h; simp [run] at h
  | succ n ih =>
      intro P x y t h
      cases P with
      | id =>
          rw [run, Option.some.injEq, Prod.ext_iff] at h
          obtain ⟨rfl, rfl⟩ := h; exact Eval.id x
      | const w =>
          rw [run, Option.some.injEq, Prod.ext_iff] at h
          obtain ⟨rfl, rfl⟩ := h; exact Eval.const w x
      | head =>
          rw [run, Option.some.injEq, Prod.ext_iff] at h
          obtain ⟨rfl, rfl⟩ := h; exact Eval.head x
      | tail =>
          rw [run, Option.some.injEq, Prod.ext_iff] at h
          obtain ⟨rfl, rfl⟩ := h; exact Eval.tail x
      | fst =>
          rw [run, Option.some.injEq, Prod.ext_iff] at h
          obtain ⟨rfl, rfl⟩ := h; exact Eval.fst x
      | snd =>
          rw [run, Option.some.injEq, Prod.ext_iff] at h
          obtain ⟨rfl, rfl⟩ := h; exact Eval.snd x
      | append =>
          rw [run, Option.some.injEq, Prod.ext_iff] at h
          obtain ⟨rfl, rfl⟩ := h; exact Eval.append x
      | eqConst w =>
          rw [run, Option.some.injEq, Prod.ext_iff] at h
          obtain ⟨rfl, rfl⟩ := h; exact Eval.eqConst w x
      | comp f g =>
          rw [run] at h
          split at h; · simp at h
          rename_i y1 tf hf
          split at h; · simp at h
          rename_i y2 tg hg
          rw [Option.some.injEq, Prod.ext_iff] at h
          obtain ⟨rfl, rfl⟩ := h
          exact Eval.comp (ih f x y1 tf hf) (ih g y1 y2 tg hg)
      | pair f g =>
          rw [run] at h
          split at h; · simp at h
          rename_i y1 tf hf
          split at h; · simp at h
          rename_i y2 tg hg
          rw [Option.some.injEq, Prod.ext_iff] at h
          obtain ⟨rfl, rfl⟩ := h
          exact Eval.pair (ih f x y1 tf hf) (ih g x y2 tg hg)
      | ite c f g =>
          rw [run] at h
          split at h; · simp at h
          rename_i r tc hc
          by_cases hr : r = [true]
          · subst hr
            rw [if_pos rfl] at h
            split at h; · simp at h
            rename_i y1 tf hf
            rw [Option.some.injEq, Prod.ext_iff] at h
            obtain ⟨rfl, rfl⟩ := h
            exact Eval.ite_true (ih c x [true] tc hc) (ih f x y1 tf hf)
          · rw [if_neg hr] at h
            split at h; · simp at h
            rename_i y1 tg hg
            rw [Option.some.injEq, Prod.ext_iff] at h
            obtain ⟨rfl, rfl⟩ := h
            exact Eval.ite_false (ih c x r tc hc) hr (ih g x y1 tg hg)
      | loop c b =>
          rw [run] at h
          split at h; · simp at h
          rename_i r tc hc
          by_cases hr : r = [true]
          · subst hr
            rw [if_pos rfl] at h
            split at h; · simp at h
            rename_i s' tb hb
            split at h; · simp at h
            rename_i y1 t1 hl
            rw [Option.some.injEq, Prod.ext_iff] at h
            obtain ⟨rfl, rfl⟩ := h
            exact Eval.loop_step (ih c x [true] tc hc) (ih b x s' tb hb)
              (ih (Prog.loop c b) s' y1 t1 hl)
          · rw [if_neg hr] at h
            rw [Option.some.injEq, Prod.ext_iff] at h
            obtain ⟨rfl, rfl⟩ := h
            exact Eval.loop_stop (ih c x r tc hc) hr

-- 燃料の単調性 `run_mono` は、健全性 `run_sound` があれば
-- 実行テスト（Test/Exec.lean）には不要なので省略する。

end Prog
