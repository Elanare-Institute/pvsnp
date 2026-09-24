/-
# 多項式上界と閉包性

v3 指示書 §4 の前半。

単調な形 `c * (n+1)^k` を採用する。`n+1` にすることで
`n = 0` でも下界 `c` が残り、単調性が自明になる。
-/
import DirectionalAsymmetry.Concrete.Prog

/-- 単調な形の多項式上界。 -/
def PolyBound (T : ℕ → ℕ) : Prop := ∃ c k : ℕ, ∀ n, T n ≤ c * (n + 1) ^ k

namespace PolyBound

theorem const (c : ℕ) : PolyBound (fun _ => c) := ⟨c, 0, fun n => by simp⟩

theorem id : PolyBound (fun n => n) := ⟨1, 1, fun n => by simp⟩

/-- 和で閉じる。 -/
theorem add {S T : ℕ → ℕ} (hS : PolyBound S) (hT : PolyBound T) :
    PolyBound (fun n => S n + T n) := by
  obtain ⟨c₁, k₁, h₁⟩ := hS
  obtain ⟨c₂, k₂, h₂⟩ := hT
  refine ⟨c₁ + c₂, max k₁ k₂, fun n => ?_⟩
  have e₁ : (n + 1) ^ k₁ ≤ (n + 1) ^ (max k₁ k₂) :=
    Nat.pow_le_pow_right (by omega) (le_max_left _ _)
  have e₂ : (n + 1) ^ k₂ ≤ (n + 1) ^ (max k₁ k₂) :=
    Nat.pow_le_pow_right (by omega) (le_max_right _ _)
  calc S n + T n ≤ c₁ * (n + 1) ^ k₁ + c₂ * (n + 1) ^ k₂ := Nat.add_le_add (h₁ n) (h₂ n)
    _ ≤ c₁ * (n + 1) ^ (max k₁ k₂) + c₂ * (n + 1) ^ (max k₁ k₂) :=
        Nat.add_le_add (Nat.mul_le_mul_left _ e₁) (Nat.mul_le_mul_left _ e₂)
    _ = (c₁ + c₂) * (n + 1) ^ (max k₁ k₂) := by ring

/-- 積で閉じる。 -/
theorem mul {S T : ℕ → ℕ} (hS : PolyBound S) (hT : PolyBound T) :
    PolyBound (fun n => S n * T n) := by
  obtain ⟨c₁, k₁, h₁⟩ := hS
  obtain ⟨c₂, k₂, h₂⟩ := hT
  refine ⟨c₁ * c₂, k₁ + k₂, fun n => ?_⟩
  calc S n * T n ≤ (c₁ * (n + 1) ^ k₁) * (c₂ * (n + 1) ^ k₂) :=
        Nat.mul_le_mul (h₁ n) (h₂ n)
    _ = (c₁ * c₂) * (n + 1) ^ (k₁ + k₂) := by rw [pow_add]; ring

/-- 上から押さえられる関数も多項式有界。 -/
theorem of_le {S T : ℕ → ℕ} (hT : PolyBound T) (h : ∀ n, S n ≤ T n) : PolyBound S := by
  obtain ⟨c, k, hc⟩ := hT
  exact ⟨c, k, fun n => le_trans (h n) (hc n)⟩

/-- 単調化: `PolyBound T` なら `c*(n+1)^k` は単調。 -/
theorem mono_witness {T : ℕ → ℕ} (hT : PolyBound T) :
    ∃ c k : ℕ, (∀ n, T n ≤ c * (n + 1) ^ k) ∧
      ∀ m n, m ≤ n → c * (m + 1) ^ k ≤ c * (n + 1) ^ k := by
  obtain ⟨c, k, hc⟩ := hT
  exact ⟨c, k, hc, fun m n hmn => Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)⟩

/-- 合成で閉じる（外側は単調な形を使う）。 -/
theorem comp {S T : ℕ → ℕ} (hS : PolyBound S) (hT : PolyBound T) :
    PolyBound (fun n => S (T n)) := by
  obtain ⟨c₁, k₁, h₁⟩ := hS
  obtain ⟨c₂, k₂, h₂⟩ := hT
  refine ⟨c₁ * (c₂ + 1) ^ k₁, k₂ * k₁, fun n => ?_⟩
  calc S (T n) ≤ c₁ * (T n + 1) ^ k₁ := h₁ _
    _ ≤ c₁ * (c₂ * (n + 1) ^ k₂ + 1) ^ k₁ := by
        refine Nat.mul_le_mul_left _ (Nat.pow_le_pow_left ?_ _)
        have := h₂ n
        omega
    _ ≤ c₁ * ((c₂ + 1) * (n + 1) ^ k₂) ^ k₁ := by
        refine Nat.mul_le_mul_left _ (Nat.pow_le_pow_left ?_ _)
        have : 1 ≤ (n + 1) ^ k₂ := Nat.one_le_pow _ _ (by omega)
        nlinarith
    _ = c₁ * (c₂ + 1) ^ k₁ * (n + 1) ^ (k₂ * k₁) := by
        rw [Nat.mul_pow, ← pow_mul]; ring

end PolyBound
