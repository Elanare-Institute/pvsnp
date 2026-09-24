/-
# 基礎定義: 多項式・言語・サイズ n の入力集合

v2 指示書 §2 の土台。計算モデルには依存しない抽象層。

v1 の `Algorithm` / `Verifier` は `NPRelation` / `TotalCandidateSolver`
（`TotalCandidateSolver.lean`）に置き換えられたため、ここからは削除した。
-/
import Mathlib.Data.Set.Basic
import Mathlib.Data.List.OfFn
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.BooleanAlgebra
import Mathlib.Data.Finset.Prod

universe u

variable {α : Type u}

/--
判定問題を言語として表現する。

`def` ではなく `abbrev`: `def` にすると `Set` の `Membership`
インスタンスが透けず `x ∈ L` が elaborate しない（v1 で確認済み）。
-/
abbrev Language (α : Type u) : Type u := Set (List α)

/-- 多項式有界性（v2 §2.1 で `IsPolynomial` として参照される）。 -/
def IsPolynomial (f : ℕ → ℕ) : Prop :=
  ∃ c k : ℕ, ∀ n, f n ≤ c * n ^ k + c

/--
サイズ `n` の入力全体の有限集合。

Mathlib では `Vector` が `List.Vector` に改名され root の `Vector` は
core の配列型なので、改名の影響を受けない `List.ofFn` 経由で構成する。
-/
def inputsOfSize (α : Type u) [Fintype α] [DecidableEq α] (n : ℕ) : Finset (List α) :=
  (Finset.univ : Finset (Fin n → α)).image List.ofFn

/-- `inputsOfSize` は（`α` が非空なら）非空。定義が依存するので `sorry` 不可。 -/
theorem inputsOfSize_nonempty (α : Type u) [Fintype α] [DecidableEq α] [Nonempty α]
    (n : ℕ) : (inputsOfSize α n).Nonempty :=
  Finset.univ_nonempty.image _

/-- `inputsOfSize α n` の要素とは、ちょうど長さ `n` のリスト。 -/
theorem mem_inputsOfSize [Fintype α] [DecidableEq α] {n : ℕ} {x : List α} :
    x ∈ inputsOfSize α n ↔ x.length = n := by
  constructor
  · rintro hx
    obtain ⟨f, -, rfl⟩ := Finset.mem_image.mp hx
    exact List.length_ofFn
  · intro hx
    subst hx
    exact Finset.mem_image.mpr ⟨fun i => x.get i, Finset.mem_univ _, List.ofFn_get x⟩

/--
サイズ `n` の入力と、長さ `m` 以下の証拠の対全体。

v2 §2.1 の `NPRelation.verifyTimePoly` が
`inputsOfSizePairs` 上の `sup'` を要求するため導入する。
証拠側は「長さちょうど `m`」ではなく **`m` 以下**を取る:
`witnessShort` が与えるのは上界なので、上界以下の証拠すべてを
走査しないと worst-case 検証時間の意味にならない。
-/
def witnessesUpTo (α : Type u) [Fintype α] [DecidableEq α] (m : ℕ) : Finset (List α) :=
  (Finset.range (m + 1)).biUnion (fun k => inputsOfSize α k)

/-- `witnessesUpTo` の要素とは、長さが `m` 以下のリスト。 -/
theorem mem_witnessesUpTo [Fintype α] [DecidableEq α] {m : ℕ} {w : List α} :
    w ∈ witnessesUpTo α m ↔ w.length ≤ m := by
  simp [witnessesUpTo, mem_inputsOfSize, Nat.lt_succ_iff]

/-- `witnessesUpTo` は非空（空リストを含む）。 -/
theorem witnessesUpTo_nonempty (α : Type u) [Fintype α] [DecidableEq α] (m : ℕ) :
    (witnessesUpTo α m).Nonempty :=
  ⟨[], mem_witnessesUpTo.mpr (Nat.zero_le _)⟩

/-- サイズ `n` の入力と長さ `m` 以下の証拠の対。 -/
def inputsOfSizePairs (α : Type u) [Fintype α] [DecidableEq α] (n m : ℕ) :
    Finset (List α × List α) :=
  (inputsOfSize α n) ×ˢ (witnessesUpTo α m)

/-- `inputsOfSizePairs` は非空。 -/
theorem inputsOfSizePairs_nonempty (α : Type u) [Fintype α] [DecidableEq α] [Nonempty α]
    (n m : ℕ) : (inputsOfSizePairs α n m).Nonempty :=
  Finset.nonempty_product.mpr ⟨inputsOfSize_nonempty α n, witnessesUpTo_nonempty α m⟩
