/-
# P と NP の定義

v2 指示書 §2.5 に対応。

**仕様からの逸脱（利用者承認済み）**:
v2 §2.5 の `ClassP` は「多項式時間 TCS が存在する」とだけ述べるが、
TCS は YES インスタンスで証拠を出すだけで **判定はしない**
（`correct` は YES 方向のみ）。このままでは Thm 1 の ⟸ 方向
`log_bounded_implies_in_p` が非対称性の仮定を一切使わず
定義展開だけで自明に成立してしまい、定理の内容が空疎になる。

そこで「M を走らせた後 `R.rel x (M.solve x)` を検査すれば判定できる」
という**判定手続きを明示化**した `ClassP` を採用する。
論文 §3.3 の iff に忠実な定式化である。
-/
import DirectionalAsymmetry.TotalCandidateSolver
import DirectionalAsymmetry.Asymmetry

universe u

variable {α : Type u} [Fintype α] [DecidableEq α] [Nonempty α]

/-- サイズ `n` における worst-case 実行時間。 -/
def worstCaseTime (t : List α → ℕ) (n : ℕ) : ℕ :=
  (inputsOfSize α n).sup t

/--
TCS `M` に基づく判定手続き。

`M` を走らせて候補証拠を得たあと、それが本当に証拠かを検査する。
`R.rel` は決定可能（`NPRelation.decRel`）なのでこれは well-defined。
-/
def TotalCandidateSolver.decide {R : NPRelation α} (M : TotalCandidateSolver α R)
    (x : List α) : Prop :=
  R.rel x (M.solve x)

/--
`M` が `R.language` を正しく判定すること。

TCS の `correct` は YES 方向（`x ∈ L → R.rel x (M.solve x)`）のみだが、
逆向き（`R.rel x (M.solve x) → x ∈ L`）は `language` の定義から
自動的に従う。したがってこれは実は常に成り立つ。
-/
theorem TotalCandidateSolver.decide_iff {R : NPRelation α}
    (M : TotalCandidateSolver α R) (x : List α) :
    M.decide x ↔ x ∈ R.language := by
  constructor
  · intro h; exact ⟨M.solve x, h⟩
  · intro h; exact M.correct x h

/--
Language class P。

「多項式時間 TCS が存在し、その判定手続きが `L` を判定する」。
`decide_iff` により判定条件は自動的に満たされるが、
**定義に明示しておくことで Thm 1 の ⟸ 方向が意味を持つ**。
-/
def ClassP (α : Type u) [Fintype α] [DecidableEq α] [Nonempty α] : Set (Language α) :=
  { L | ∃ (R : NPRelation α) (M : TotalCandidateSolver α R),
      R.language = L ∧
      (∀ x, M.decide x ↔ x ∈ L) ∧
      IsPolynomial (worstCaseTime M.solveTime) }

/--
Language class NP。

NP の定義は NPRelation の存在そのもの
（検証の多項式時間性と証拠長の多項式有界性は `NPRelation` に内蔵）。
-/
def ClassNP (α : Type u) [Fintype α] [DecidableEq α] [Nonempty α] : Set (Language α) :=
  { L | ∃ R : NPRelation α, R.language = L }

@[simp] theorem mem_ClassNP {L : Language α} :
    L ∈ ClassNP α ↔ ∃ R : NPRelation α, R.language = L := Iff.rfl

theorem mem_ClassP {L : Language α} :
    L ∈ ClassP α ↔ ∃ (R : NPRelation α) (M : TotalCandidateSolver α R),
      R.language = L ∧ (∀ x, M.decide x ↔ x ∈ L) ∧
      IsPolynomial (worstCaseTime M.solveTime) := Iff.rfl
