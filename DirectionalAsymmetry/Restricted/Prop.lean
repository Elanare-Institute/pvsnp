/-
# 命題論理の基礎

v4 指示書 §2。変数・リテラル・節・CNF・割り当て・充足。

変数は ℕ で番号づける。`Satisfiable` の判定可能性は不要
（すべて命題として扱う）。
-/
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Tactic

/-- 命題変数（ℕ で番号づける）。 -/
abbrev Var := ℕ

/-- リテラル（変数かその否定）。 -/
inductive Lit where
  | pos (v : Var)
  | neg (v : Var)
  deriving DecidableEq, Repr

namespace Lit

/-- リテラルの変数。 -/
def var : Lit → Var
  | .pos v => v
  | .neg v => v

/-- リテラルの補。 -/
def compl : Lit → Lit
  | .pos v => .neg v
  | .neg v => .pos v

@[simp] theorem compl_compl (l : Lit) : l.compl.compl = l := by
  cases l <;> rfl

@[simp] theorem var_compl (l : Lit) : l.compl.var = l.var := by
  cases l <;> rfl

@[simp] theorem compl_pos (v : Var) : (Lit.pos v).compl = Lit.neg v := rfl
@[simp] theorem compl_neg (v : Var) : (Lit.neg v).compl = Lit.pos v := rfl

theorem compl_ne (l : Lit) : l.compl ≠ l := by
  cases l <;> simp [compl]

end Lit

/-- 節（リテラルの有限集合。選言と解釈する）。 -/
abbrev Clause := Finset Lit

/-- CNF（節のリスト。連言と解釈する。重複・順序は問わない）。 -/
abbrev CNF := List Clause

/-- 真理値割り当て。 -/
abbrev Assignment := Var → Bool

namespace Lit

/-- リテラルの評価。 -/
def eval (a : Assignment) : Lit → Bool
  | .pos v => a v
  | .neg v => !(a v)

@[simp] theorem eval_pos (a : Assignment) (v : Var) : (Lit.pos v).eval a = a v := rfl
@[simp] theorem eval_neg (a : Assignment) (v : Var) : (Lit.neg v).eval a = !(a v) := rfl

/-- リテラルとその補は、ちょうど一方が真。 -/
theorem eval_compl (a : Assignment) (l : Lit) : l.compl.eval a = !(l.eval a) := by
  cases l <;> simp [eval, compl]

/-- リテラルとその補が同時に真にはならない。 -/
theorem not_both (a : Assignment) (l : Lit) :
    ¬ (l.eval a = true ∧ l.compl.eval a = true) := by
  rintro ⟨h1, h2⟩
  rw [eval_compl, h1] at h2
  simp at h2

end Lit

/-- 節の充足（少なくとも一つのリテラルが真）。 -/
def Clause.eval (a : Assignment) (C : Clause) : Prop := ∃ l ∈ C, l.eval a = true

/-- CNF の充足（すべての節が真）。 -/
def CNF.eval (a : Assignment) (F : CNF) : Prop := ∀ C ∈ F, C.eval a

/-- 充足可能性。 -/
def Satisfiable (F : CNF) : Prop := ∃ a, F.eval a

/-- 空節はどの割り当てでも偽。 -/
@[simp] theorem Clause.eval_empty (a : Assignment) : ¬ (∅ : Clause).eval a := by
  rintro ⟨l, hl, -⟩
  simp at hl

/-- 空節を含む CNF は充足不能。 -/
theorem not_satisfiable_of_empty_mem {F : CNF} (h : (∅ : Clause) ∈ F) :
    ¬ Satisfiable F := by
  rintro ⟨a, ha⟩
  exact Clause.eval_empty a (ha ∅ h)

/-- `F` に現れる変数の有限集合。 -/
def CNF.vars (F : CNF) : Finset Var :=
  (F.foldr (fun C acc => C ∪ acc) ∅).image Lit.var
