/-
# スペクトル（論文 §4.3 の定義4'・4''、命題1）

v3 指示書 §7。

「O(log n) 差を同一視する同値類」でスペクトルを定義し、
命題1（P = NP ⇔ Σ = {[0]}）を厳密に成立させる。

⊥ には `WithBot` ではなく `Option` の `none` を使う。
論文の ⊥ は「未定義」であって「[0] より小さい」ではないため、
順序構造を持ち込まない（指示書 §7、落とし穴 7）。
-/
import DirectionalAsymmetry.Concrete.Characterization
import Mathlib.Order.Antisymmetrization

open Encoding Prog

/--
プロファイルの型。

`def` にして `ℕ → ℤ` の Pi 順序（各点順序）と衝突させない。
ここで入れる順序は「O(log n) 差を無視する」前順序。
-/
def Profile := ℕ → ℤ

/-- `ℕ → ℤ` から `Profile` への変換（定義上は恒等）。 -/
def toProfile (f : ℕ → ℤ) : Profile := f

/-- `Profile` の値を取り出す。 -/
def Profile.at (f : Profile) (n : ℕ) : ℤ := f n

@[simp] theorem toProfile_at (f : ℕ → ℤ) (n : ℕ) : (toProfile f).at n = f n := rfl

namespace Profile

/-- `f ≤ g` ⟺ `f` は `g` より高々 `O(log n)` だけ大きい。 -/
instance : Preorder Profile where
  le f g := ∃ C : ℕ, ∀ n, f.at n ≤ g.at n + C * (Nat.log 2 n + 1)
  le_refl f := ⟨0, fun n => by simp⟩
  le_trans f g h := by
    rintro ⟨C₁, h₁⟩ ⟨C₂, h₂⟩
    refine ⟨C₁ + C₂, fun n => ?_⟩
    have e1 := h₁ n
    have e2 := h₂ n
    have hnn : (0:ℤ) ≤ (Nat.log 2 n : ℤ) := Int.natCast_nonneg _
    push_cast at e1 e2 ⊢
    nlinarith

theorem le_def {f g : Profile} :
    f ≤ g ↔ ∃ C : ℕ, ∀ n, f.at n ≤ g.at n + C * (Nat.log 2 n + 1) := Iff.rfl

end Profile

/-- 非対称性クラス（O(log n) 差の同値類）。 -/
abbrev AsymClass := Antisymmetrization Profile (· ≤ ·)

/-- プロファイルの属する類。 -/
def cls (f : Profile) : AsymClass := toAntisymmetrization (· ≤ ·) f

/-- 零類 `[0]`。 -/
def zeroClass : AsymClass := cls (toProfile (fun _ => 0))

/-- `R` に対して達成可能な非対称性クラスの集合。 -/
def achievable (R : NPRel) : Set AsymClass :=
  {c | ∃ M : TCS R, cls (toProfile (profile M)) = c}

/--
`R` の非対称性クラス。

最小元が存在しないとき `none`（論文の ⊥）。
`WithBot` ではなく `Option` を使うので順序は入らない。
-/
noncomputable def classOf (R : NPRel) : Option AsymClass :=
  open Classical in
  if h : ∃ c, IsLeast (achievable R) c then some h.choose else none

/-- スペクトル Σ。 -/
def asymSpectrum : Set (Option AsymClass) := Set.range classOf

section Lemmas

/-- `cls` の順序は `Profile` の順序と一致。 -/
theorem cls_le_cls {f g : Profile} : cls f ≤ cls g ↔ f ≤ g :=
  toAntisymmetrization_le_toAntisymmetrization_iff

/-- 零類は任意のプロファイル類以下（普遍下界 `asym_lower` から）。 -/
theorem zeroClass_le {R : NPRel} (M : TCS R) :
    zeroClass ≤ cls (toProfile (profile M)) := by
  rw [zeroClass]
  rw [cls_le_cls]
  rw [Profile.le_def]
  obtain ⟨C, hC⟩ := asym_lower R M
  refine ⟨C, fun n => ?_⟩
  have h := hC n
  simp only [toProfile_at]
  omega

/-- プロファイル類が零類以下 ⟺ `LogBounded`。 -/
theorem cls_le_zero_iff {R : NPRel} (M : TCS R) :
    cls (toProfile (profile M)) ≤ zeroClass ↔ LogBounded (profile M) := by
  rw [zeroClass]
  rw [cls_le_cls]
  rw [Profile.le_def]
  constructor
  · rintro ⟨C, hC⟩
    refine ⟨C, fun n => ?_⟩
    have h := hC n
    simp only [toProfile_at] at h
    omega
  · rintro ⟨C, hC⟩
    refine ⟨C, fun n => ?_⟩
    have h := hC n
    simp only [toProfile_at]
    omega

/-- `LogBounded` なプロファイルの類は零類。 -/
theorem cls_eq_zero_iff {R : NPRel} (M : TCS R) :
    cls (toProfile (profile M)) = zeroClass ↔ LogBounded (profile M) := by
  constructor
  · intro h; exact (cls_le_zero_iff M).mp (le_of_eq h)
  · intro h
    exact le_antisymm ((cls_le_zero_iff M).mpr h) (zeroClass_le M)

end Lemmas

section Prop1

/-- `classOf R = some zeroClass` ⟺ `LogBounded` な TCS が存在する。 -/
theorem classOf_eq_some_zero_iff (R : NPRel) :
    classOf R = some zeroClass ↔ ∃ M : TCS R, LogBounded (profile M) := by
  classical
  constructor
  · intro h
    rw [classOf] at h
    split at h
    · rename_i hex
      -- h : some hex.choose = some zeroClass
      have hzero : hex.choose = zeroClass := by
        exact Option.some.inj h
      have hleast := hex.choose_spec
      rw [hzero] at hleast
      -- zeroClass ∈ achievable R
      obtain ⟨M, hM⟩ := hleast.1
      exact ⟨M, (cls_eq_zero_iff M).mp hM⟩
    · exact absurd h (by simp)
  · rintro ⟨M, hM⟩
    -- zeroClass は achievable R の最小元
    have hleast : IsLeast (achievable R) zeroClass := by
      constructor
      · exact ⟨M, (cls_eq_zero_iff M).mpr hM⟩
      · rintro c ⟨M', rfl⟩
        exact zeroClass_le M'
    have hex : ∃ c, IsLeast (achievable R) c := ⟨zeroClass, hleast⟩
    rw [classOf, dif_pos hex]
    congr 1
    exact IsLeast.unique hex.choose_spec hleast

/--
**命題1**: P = NP ⟺ スペクトルが `{[0]}`。

→ 方向では `Set.range` の非空性のために `Nonempty NPRel` を使う。
-/
theorem prop1 : PeqNP ↔ asymSpectrum = {some zeroClass} := by
  constructor
  · intro h
    ext c
    simp only [asymSpectrum, Set.mem_range, Set.mem_singleton_iff]
    constructor
    · rintro ⟨R, rfl⟩
      rw [classOf_eq_some_zero_iff]
      obtain ⟨M, -, hlog⟩ := thm1_a_to_b h R
      exact ⟨M, hlog⟩
    · rintro rfl
      -- Nonempty NPRel から witness を取る
      obtain ⟨R⟩ := (inferInstance : Nonempty NPRel)
      refine ⟨R, ?_⟩
      rw [classOf_eq_some_zero_iff]
      obtain ⟨M, -, hlog⟩ := thm1_a_to_b h R
      exact ⟨M, hlog⟩
  · intro h
    -- 全ての R について classOf R = some zeroClass
    refine thm1_b_to_a (fun R => ?_)
    have : classOf R ∈ asymSpectrum := ⟨R, rfl⟩
    rw [h] at this
    simp only [Set.mem_singleton_iff] at this
    exact (classOf_eq_some_zero_iff R).mp this

end Prop1
