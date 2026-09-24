/-
# 定理1・系1・系2

v3 指示書 §6.3。論文 §3.3 の定理1に対応。

(a) P = NP
(b) 任意の NP relation に O(log n) 非対称性の TCS が存在
(c) NP 完全 relation に O(log n) 非対称性の TCS が存在

`thm1_a_to_b` の証明は `prefixSearch` を経由し、
v2 の `transportSolver` のような移送を**使わない**。
-/
import DirectionalAsymmetry.Concrete.Prefix

open Encoding Prog

/--
**定理1 (a)⇒(b)**。

P = NP から `(prefRel R).lang ∈ ClassP` を得て decider `D` を取り出し、
`prefixSearch D R.V` を TCS として使う。移送は使わない。
-/
theorem thm1_a_to_b (h : PeqNP) (R : NPRel) :
    ∃ M : TCS R, PolyTime M.M ∧ LogBounded (profile M) := by
  -- (prefRel R).lang ∈ ClassNP なので、PeqNP より ClassP
  have hmem : (prefRel R).lang ∈ ClassP := h ⟨prefRel R, rfl⟩
  obtain ⟨D, hDpoly, hDdec⟩ := hmem
  -- prefixSearch D R.V が求める TCS
  refine ⟨prefixSearch_tcs hDdec, ?_, ?_⟩
  · exact prefixSearch_polyTime hDpoly hDdec
  · exact logBounded_of_polyTime (prefixSearch_polyTime hDpoly hDdec)

/--
**定理1 (b)⇒(a)**。

任意の NP relation に `LogBounded` な TCS があれば、
`polyTime_of_logBounded` で多項式時間になり、
`lang_inP_of_polyTime_tcs` で言語が P に入る。
-/
theorem thm1_b_to_a (h : ∀ R : NPRel, ∃ M : TCS R, LogBounded (profile M)) : PeqNP := by
  rintro L ⟨R, rfl⟩
  obtain ⟨M, hM⟩ := h R
  exact lang_inP_of_polyTime_tcs (polyTime_of_logBounded hM)

/--
**定理1 (c)⇒(a)**。

NP 完全な `R` について `LogBounded` な TCS があれば、
`R.lang ∈ ClassP` となり、NP 完全性の帰着で NP ⊆ P。
-/
theorem thm1_c_to_a (R : NPRel) (hNPC : IsNPComplete R.lang)
    (h : ∃ M : TCS R, LogBounded (profile M)) : PeqNP := by
  obtain ⟨M, hM⟩ := h
  have hRP : R.lang ∈ ClassP := lang_inP_of_polyTime_tcs (polyTime_of_logBounded hM)
  rintro L hL
  exact inP_of_reduces (hNPC.2 L hL) hRP

/-- **定理1 (a)⇔(b)**。 -/
theorem thm1_a_iff_b : PeqNP ↔ ∀ R : NPRel, ∃ M : TCS R, LogBounded (profile M) := by
  constructor
  · intro h R
    obtain ⟨M, -, hlog⟩ := thm1_a_to_b h R
    exact ⟨M, hlog⟩
  · exact thm1_b_to_a

/-- **定理1 (a)⇔(c)**（NP 完全 relation について）。 -/
theorem thm1_a_iff_c (R : NPRel) (hNPC : IsNPComplete R.lang) :
    PeqNP ↔ ∃ M : TCS R, LogBounded (profile M) := by
  constructor
  · intro h
    obtain ⟨M, -, hlog⟩ := thm1_a_to_b h R
    exact ⟨M, hlog⟩
  · exact thm1_c_to_a R hNPC

/-- **系1**: P ≠ NP ⟺ ある NP relation の全 TCS が超対数的。 -/
theorem cor1 : ¬ PeqNP ↔ ∃ R : NPRel, ∀ M : TCS R, ¬ LogBounded (profile M) := by
  rw [thm1_a_iff_b]
  push Not
  rfl

/-- **系1'**: P ≠ NP なら NP 完全 relation の全 TCS が超対数的。 -/
theorem cor1' (h : ¬ PeqNP) (R : NPRel) (hNPC : IsNPComplete R.lang)
    (M : TCS R) : ¬ LogBounded (profile M) := by
  intro hlog
  exact h (thm1_c_to_a R hNPC ⟨M, hlog⟩)

/-- **系2**: NP 完全 relation について、P 所属と O(log n) 非対称性は同値。 -/
theorem cor2 (R : NPRel) (hNPC : IsNPComplete R.lang) :
    R.lang ∈ ClassP ↔ ∃ M : TCS R, LogBounded (profile M) := by
  constructor
  · intro hRP
    -- R.lang ∈ ClassP なら PeqNP（NP 完全性より）、よって (a)⇒(c)
    have hPeq : PeqNP := by
      rintro L hL
      exact inP_of_reduces (hNPC.2 L hL) hRP
    obtain ⟨M, -, hlog⟩ := thm1_a_to_b hPeq R
    exact ⟨M, hlog⟩
  · rintro ⟨M, hlog⟩
    exact lang_inP_of_polyTime_tcs (polyTime_of_logBounded hlog)
