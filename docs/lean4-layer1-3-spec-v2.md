# Lean 4 形式検証指示書 v2: Layer 1–3
## Directional Asymmetry Reformulation of P vs NP

### 改訂の経緯

v1 指示書で Claude Code が実行した結果、型チェック不整合が9件見つかった。
主な原因:
- Algorithm と Verifier が別構造体で、time の型が合わない
- maxAsymmetry_eq_worstcase_diff が数学的に偽（sup(f-g) ≠ sup f - sup g）
- avgAsymmetry が def なのに sorry
- Mathlib API 名が古い

本指示書は論文の formal skeleton（ChatGPT統合版）に基づき、
定義を Total Candidate Solver 中心に再設計する。

---

## 0. 前回実行からの引き継ぎ

前回の Layer 1 で **証明済みの定理** は以下:
- `p_sub_np_via_asymmetry` (P ⊆ NP)
- `log_polynomial_is_O_log`
- `log_diff_polynomials_is_O_log`
- `log_exponential_is_linear`

これらのうち、新しい定義体系でも成立するものは移植・再利用してよい。
特に `log_polynomial_is_O_log` と `log_diff_polynomials_is_O_log` は
定義非依存の純粋数学なのでそのまま使える。

前回のプロジェクト構造・lakefile.lean・Mathlib 依存設定はそのまま使ってよい。
Mathlib バージョンは前回と同じ v4.33.1 で問題ない。

---

## 1. プロジェクト構成

```
DirectionalAsymmetry/
├── lakefile.lean
├── lean-toolchain
├── DirectionalAsymmetry/
│   ├── Basic.lean              -- 多項式・漸近記法・Language
│   ├── TotalCandidateSolver.lean -- Def 1-2: NP relation, TCS
│   ├── Asymmetry.lean          -- Def 3-3': A_M(x), A*(x)
│   ├── Complexity.lean         -- P, NP の定義
│   ├── Characterization.lean   -- Thm 1: P=NP ⟺ sup A_M = O(log n)
│   ├── Distribution.lean       -- Def 4: D_n(A), spectrum (Layer 1–2境界)
│   ├── SearchSpace.lean        -- Def 5-6: solvable region, local asymmetry (Layer 2)
│   ├── Accumulation.lean       -- Prop 2: accumulation identity (Layer 2)
│   ├── MeaningTransformation.lean -- Def 7: asymmetry-reducing transformation (Layer 2)
│   ├── Separation.lean         -- Conj A, Conj B, Thm 2 (Layer 3)
│   ├── Auxiliary.lean          -- 補助補題（対数、多項式）
│   └── Main.lean               -- 全体のインポートと #check
├── Test/
│   └── NoSorryInDefs.lean      -- 定義層の sorry 不在テスト（前回から引き継ぎ）
└── README.md
```

---

## 2. Layer 1: 基礎定義と P=NP 特性化

### 2.1 NP Relation（TotalCandidateSolver.lean）

```lean
/-- Definition 1: NP relation -/
structure NPRelation (α : Type) where
  /-- The relation R(x, w) -/
  rel : List α → List α → Prop
  /-- R is decidable -/
  decRel : DecidablePred (fun p : List α × List α => rel p.1 p.2)
  /-- Verification is polynomial-time -/
  verifyTime : List α → List α → ℕ
  verifyTimePoly : IsPolynomial (fun n => 
    Finset.sup' (inputsOfSizePairs n) (inputsOfSizePairsNonempty n) 
      (fun p => verifyTime p.1 p.2))
  /-- Witness length is polynomially bounded -/
  witnessBound : ℕ → ℕ
  witnessBoundPoly : IsPolynomial witnessBound
  witnessShort : ∀ x w, rel x w → w.length ≤ witnessBound x.length

/-- Language defined by an NP relation -/
def NPRelation.language (R : NPRelation α) : Language α :=
  { x | ∃ w, R.rel x w }
```

### 2.2 Total Candidate Solver（TotalCandidateSolver.lean）

```lean
/-- Definition 2: Total Candidate Solver
    Always halts. For YES instances, outputs a valid witness.
    For NO instances, outputs arbitrary candidate. -/
structure TotalCandidateSolver (α : Type) (R : NPRelation α) where
  /-- The solver function: input → candidate witness -/
  solve : List α → List α
  /-- Running time -/
  solveTime : List α → ℕ
  /-- Correctness on YES instances -/
  correct : ∀ x, x ∈ R.language → R.rel x (solve x)
```

**注意点:**
- `solve` は全域関数（常に停止）
- YES instance では valid witness を出力する保証
- NO instance では何を出力してもよい（`R.rel x (solve x)` は偽になるだけ）
- `solveTime` は実行時間を別フィールドで持つ（抽象モデル）
- correctness は YES 方向のみ要求

### 2.3 方向非対称性（Asymmetry.lean）

```lean
/-- Definition 3: Computational Directional Asymmetry
    A_M(x) = log₂ T_M(x) - log₂ T_V(x, M(x)) -/
noncomputable def directionalAsymmetry 
    {α : Type} {R : NPRelation α}
    (M : TotalCandidateSolver α R)
    (x : List α) : ℤ :=
  Int.log 2 (M.solveTime x) - Int.log 2 (R.verifyTime x (M.solve x))

/-- Worst-case asymmetry at size n -/
noncomputable def maxAsymmetry [Fintype α] [DecidableEq α]
    {R : NPRelation α}
    (M : TotalCandidateSolver α R)
    (n : ℕ)
    (hn : (inputsOfSize α n).Nonempty) : ℤ :=
  (inputsOfSize α n).sup' hn (fun x => directionalAsymmetry M x)
```

**v1 からの変更点:**
- `solveCost` と `verifyCost` が別引数だったのを、`M : TotalCandidateSolver` に統合
- witness は `M.solve x` で決定 → `verifyCost` の witness 曖昧性が解消
- `verifyTime x (M.solve x)`: verifier は M の出力を検査する。accept する必要はない

**前回の不備の修正:**
- `maxAsymmetry_eq_worstcase_diff` は**削除**。sup(f-g) = sup f - sup g は偽。

### 2.4 Optimal Asymmetry（Asymmetry.lean）

```lean
/-- Definition 3': Optimal asymmetry (infimum over all TCS)
    A*(x) = inf_M A_M(x)
    Note: by Blum's speed-up theorem, the infimum may not be attained. -/
noncomputable def optimalAsymmetry 
    {α : Type} (R : NPRelation α) 
    (x : List α) : ℤ :=
  iInf (fun (M : TotalCandidateSolver α R) => directionalAsymmetry M x)

-- 注: iInf は ℤ の ConditionallyCompleteLattice を使う。
-- 空でない場合のみ well-defined。TCS が少なくとも1つ存在することは
-- NP relation の定義から保証（brute-force search が常に存在）。
```

### 2.5 P と NP の定義（Complexity.lean）

```lean
/-- Language class P -/
def ClassP (α : Type) : Set (Language α) :=
  { L | ∃ (R : NPRelation α) (M : TotalCandidateSolver α R),
    R.language = L ∧
    IsPolynomial (fun n => worstCaseTime M.solveTime n) }

/-- Language class NP -/
def ClassNP (α : Type) : Set (Language α) :=
  { L | ∃ (R : NPRelation α), R.language = L }
  -- NP の定義は NPRelation の存在そのもの
  -- （verifyTime の多項式性と witness bound は NPRelation に内蔵）

/-- Helper: worst-case time at size n -/
noncomputable def worstCaseTime [Fintype α] [DecidableEq α]
    (t : List α → ℕ) (n : ℕ) : ℕ :=
  if h : (inputsOfSize α n).Nonempty then
    (inputsOfSize α n).sup' h t
  else 0
```

### 2.6 Theorem 1: P=NP 特性化（Characterization.lean）

```lean
/-- Theorem 1 (⟹ direction): 
    P = NP implies there exists a poly-time TCS with O(log n) asymmetry -/
theorem p_eq_np_implies_log_bounded
    [Fintype α] [DecidableEq α]
    (h : ClassP α = ClassNP α)
    (R : NPRelation α) (hR : R.language ∈ ClassNP α) :
    ∃ (M : TotalCandidateSolver α R),
      IsPolynomial (fun n => worstCaseTime M.solveTime n) ∧
      IsBigO 
        (fun n => if hn : (inputsOfSize α n).Nonempty 
                  then (maxAsymmetry M n hn).natAbs else 0)
        (fun n => Nat.log 2 n) := by
  sorry -- TODO: Layer 1 proof

/-- Theorem 1 (⟸ direction):
    A poly-time TCS with O(log n) asymmetry implies the language is in P -/
theorem log_bounded_implies_in_p
    [Fintype α] [DecidableEq α]
    (R : NPRelation α) 
    (M : TotalCandidateSolver α R)
    (hPoly : IsPolynomial (fun n => worstCaseTime M.solveTime n)) :
    R.language ∈ ClassP α := by
  sorry -- TODO: Layer 1 proof (simpler direction)

/-- Corollary: P ≠ NP iff for all poly-time TCS, 
    worst-case asymmetry is superlogarithmic -/
theorem p_ne_np_iff_superlog_asymmetry
    [Fintype α] [DecidableEq α] :
    ClassP α ≠ ClassNP α ↔ 
    ∃ (R : NPRelation α), R.language ∈ ClassNP α ∧
      ∀ (M : TotalCandidateSolver α R),
        IsPolynomial (fun n => worstCaseTime M.solveTime n) →
        ¬ IsBigO 
          (fun n => if hn : (inputsOfSize α n).Nonempty 
                    then (maxAsymmetry M n hn).natAbs else 0)
          (fun n => Nat.log 2 n) := by
  sorry -- TODO: follows from the two directions above
```

### 2.7 P ⊆ NP（Characterization.lean）

```lean
/-- P ⊆ NP in the asymmetry framework -/
theorem p_sub_np : ClassP α ⊆ ClassNP α := by
  sorry -- TODO: Layer 1 proof (reuse from v1 if compatible)
```

### 2.8 補助補題（Auxiliary.lean）

前回証明済みのものを再利用:

```lean
lemma log_polynomial_is_O_log 
    (f : ℕ → ℕ) (hf : IsPolynomial f) :
    IsBigO (fun n => Nat.log 2 (f n)) (fun n => Nat.log 2 n) := by
  sorry -- 前回証明済み: 移植

lemma log_diff_polynomials_is_O_log
    (f g : ℕ → ℕ) (hf : IsPolynomial f) (hg : IsPolynomial g) :
    IsBigO 
      (fun n => Int.natAbs (Int.log 2 (f n) - Int.log 2 (g n)))
      (fun n => Nat.log 2 n) := by
  sorry -- 前回証明済み: 移植

lemma log_exponential_is_linear
    (b : ℕ) (hb : 2 ≤ b) :
    ∀ n, n ≤ Nat.log 2 (b ^ n) := by
  sorry -- 前回証明済み: 移植
```

---

## 3. Layer 2: 探索空間構造と累積

### 3.1 Solvable Region（SearchSpace.lean）

```lean
/-- Definition 5: Partial assignment (using Option to represent unassigned) -/
def PartialAssignment (n : ℕ) := Fin n → Option Bool

/-- A partial assignment extends to a total assignment -/
def extends_ {n : ℕ} (p : PartialAssignment n) (x : Fin n → Bool) : Prop :=
  ∀ i, p i = some (x i) ∨ p i = none

/-- Definition 5: Solvable region for a boolean formula -/
def solvableRegion {n : ℕ} (φ : (Fin n → Bool) → Prop) : 
    Set (PartialAssignment n) :=
  { p | ∃ x, extends_ p x ∧ φ x }
```

### 3.2 Local Search Asymmetry（SearchSpace.lean）

```lean
/-- One-step extensions of a partial assignment -/
def extensions {n : ℕ} (p : PartialAssignment n) : 
    Set (PartialAssignment n) :=
  { p' | ∃ i, p i = none ∧ (∃ b, p' = Function.update p i (some b)) ∧
         ∀ j, j ≠ i → p' j = p j }

/-- Definition 6: Local search asymmetry 
    a(p) = log |E(p)| / |G(p)| where G(p) = E(p) ∩ solvableRegion -/
noncomputable def localAsymmetry {n : ℕ} 
    (φ : (Fin n → Bool) → Prop) 
    (p : PartialAssignment n) 
    (hE : (extensions p).Finite)
    (hG : (extensions p ∩ solvableRegion φ).Finite)
    (hGne : (extensions p ∩ solvableRegion φ).Nonempty) : ℝ :=
  Real.log (hE.toFinset.card : ℝ) - Real.log (hG.toFinset.card : ℝ)
```

**注意点:**
- `extensions p` は有限集合（各 unassigned variable × {0,1}）
- `solvableRegion` のメンバーシップは NP-hard — これは意図的。
  定義としては well-defined だが計算可能でない。
- `localAsymmetry` は Real.log を使用（noncomputable）

### 3.3 Accumulation Identity（Accumulation.lean）

```lean
/-- A search path: sequence of partial assignments -/
structure SearchPath (n : ℕ) (d : ℕ) where
  path : Fin (d + 1) → PartialAssignment n
  consecutive : ∀ i : Fin d, path i.castSucc ∈ extensions (path (Fin.succ i))
    ∨ path (Fin.succ i) ∈ extensions (path i.castSucc)
  -- 注: 方向は downward (root → leaf) を想定

/-- Proposition 2: Accumulation Identity
    Total structural asymmetry = sum of local asymmetries along a path -/
theorem accumulation_identity {n d : ℕ} 
    (φ : (Fin n → Bool) → Prop)
    (sp : SearchPath n d)
    /- 適切な有限性・非空性の仮定 -/ :
    structuralAsymmetry φ sp = 
      Finset.sum (Finset.range d) (fun i => 
        localAsymmetry φ (sp.path ⟨i, by omega⟩) /- 仮定 -/) := by
  sorry -- TODO: Layer 2 proof
  -- 証明方針: 対数の加法性。log(∏ aᵢ/bᵢ) = Σ (log aᵢ - log bᵢ)
```

### 3.4 Distribution（Distribution.lean）

```lean
/-- Definition 4: Asymmetry distribution as pushforward measure -/
-- Mathlib の MeasureTheory を使用
-- μ_n を size-n instances 上の測度とし、A_M の pushforward を取る

noncomputable def asymmetryDistribution 
    [MeasurableSpace (List α)]
    {R : NPRelation α}
    (M : TotalCandidateSolver α R)
    (μ : MeasureTheory.Measure (List α)) :
    MeasureTheory.Measure ℤ :=
  μ.map (fun x => directionalAsymmetry M x)

-- 注: MeasurableSpace と Measure の整合性に注意。
-- 有限アルファベットなら ⊤ (discrete) で問題ない。
```

### 3.5 Meaning Transformation（MeaningTransformation.lean）

```lean
/-- Definition 7: Asymmetry-Reducing Transformation
    A transformation τ that, when applied to the search state,
    reduces the effective local asymmetry -/
structure AsymmetryReducingTransform (n : ℕ) where
  /-- The transformation on partial assignments -/
  transform : PartialAssignment n → PartialAssignment n
  /-- Computational cost of the transformation -/
  cost : PartialAssignment n → ℕ
  /-- Cost is polynomial in n -/
  costPoly : IsPolynomial (fun n => cost default)  -- 簡略化

/-- A transformation reduces asymmetry at a given point -/
def reduces_asymmetry {n : ℕ}
    (φ : (Fin n → Bool) → Prop)
    (τ : AsymmetryReducingTransform n)
    (p : PartialAssignment n) : Prop :=
  localAsymmetry φ (τ.transform p) /- ... -/ ≤ localAsymmetry φ p /- ... -/
  -- 注: 有限性・非空性の仮定を適切に補う必要あり
```

---

## 4. Layer 3: 分離プログラム

### 4.1 Conjecture A（Separation.lean）

```lean
/-- Conjecture A: Structural-to-Computational Bridge
    If residual structural asymmetry after all poly-time transformations
    is superlogarithmic, then computational asymmetry is superlogarithmic -/
axiom conjecture_A : 
  ∀ {α : Type} [Fintype α] [DecidableEq α]
    (R : NPRelation α) (M : TotalCandidateSolver α R),
    -- If residual structural asymmetry is ω(log n)...
    (∀ C : ℕ, ∃ᶠ n in Filter.atTop, 
      residualStructuralAsymmetry R M n > C * Nat.log 2 n) →
    -- ...then computational asymmetry is ω(log n)
    (∀ C : ℕ, ∃ᶠ n in Filter.atTop,
      ∃ x, x.length = n ∧ (directionalAsymmetry M x).natAbs > C * Nat.log 2 n)
```

**注意:** 
- `axiom` として宣言する（未証明を明示）
- `residualStructuralAsymmetry` は別途定義が必要:
  M が利用可能な全 poly-time transformation を適用した後の構造的非対称性
- `∃ᶠ n in Filter.atTop` は「十分大きな n で無限に多く」を意味
  （Mathlib の `Filter.Frequently`）

### 4.2 Conjecture B（Separation.lean）

```lean
/-- Conjecture B: Meaning-Dimension Inexhaustibility
    For every poly-time TCS, there exists an NP-encodable family
    with superlogarithmic residual structural asymmetry -/
axiom conjecture_B :
  ∀ {α : Type} [Fintype α] [DecidableEq α]
    (R : NPRelation α) (M : TotalCandidateSolver α R),
    IsPolynomial (fun n => worstCaseTime M.solveTime n) →
    (∀ C : ℕ, ∃ᶠ n in Filter.atTop,
      residualStructuralAsymmetry R M n > C * Nat.log 2 n)
```

### 4.3 Conditional Separation Theorem（Separation.lean）

```lean
/-- Theorem 2: Conjecture A + Conjecture B ⟹ P ≠ NP -/
theorem conditional_p_ne_np
    [Fintype α] [DecidableEq α] :
    ClassP α ≠ ClassNP α := by
  -- Uses conjecture_A and conjecture_B as axioms
  intro h_eq
  -- h_eq : ClassP = ClassNP
  -- From h_eq, obtain poly-time TCS for some NP-complete language
  -- Apply conjecture_B: residual structural asymmetry is ω(log n)
  -- Apply conjecture_A: computational asymmetry is ω(log n)
  -- Contradiction with h_eq via Theorem 1
  sorry -- TODO: Layer 3 proof (should be straightforward given A and B)
```

**証明方針:**
1. `h_eq : ClassP = ClassNP` を仮定
2. NP-complete 言語 $L$ を固定（Cook-Levin が必要 → 別途 axiom or import）
3. `h_eq` より $L \in ClassP$、従って poly-time TCS $M$ が存在
4. Theorem 1 より $\sup A_M = O(\log n)$
5. Conjecture B より $A_{\text{struct}}^M = \omega(\log n)$
6. Conjecture A より $A_M = \omega(\log n)$ on some family
7. 矛盾

---

## 5. 全体の sorry 優先順位

### 即座に証明すべき（Layer 1 コア）

| 優先度 | 対象 | 方針 |
|---|---|---|
| 1 | `p_sub_np` | P ⊆ NP。前回実績あり、新定義に移植 |
| 2 | `log_polynomial_is_O_log` | 純粋数学。前回証明済み、移植 |
| 3 | `log_diff_polynomials_is_O_log` | 2 の系。前回証明済み、移植 |
| 4 | `log_exponential_is_linear` | 純粋数学。前回証明済み、移植 |
| 5 | `log_bounded_implies_in_p` | Thm 1 の簡単な方向 |
| 6 | `p_eq_np_implies_log_bounded` | Thm 1 の本方向。2-3 を利用 |
| 7 | `p_ne_np_iff_superlog_asymmetry` | 5-6 の対偶から |

### Layer 2（定義型チェック優先、証明は次）

| 優先度 | 対象 | 方針 |
|---|---|---|
| 8 | `solvableRegion` 定義 | 型チェックのみ |
| 9 | `localAsymmetry` 定義 | 型チェックのみ |
| 10 | `accumulation_identity` | ステートメント型チェック → 対数加法性で証明 |

### Layer 3（axiom として宣言、証明は将来）

| 優先度 | 対象 | 方針 |
|---|---|---|
| 11 | `conjecture_A` | axiom |
| 12 | `conjecture_B` | axiom |
| 13 | `conditional_p_ne_np` | axiom A+B から導出。sorry → 証明を試みる |

---

## 6. 成功基準

### Layer 1 完了判定

- [ ] `lake build` がエラーなしで通る
- [ ] `NPRelation`, `TotalCandidateSolver` の定義が sorry なし
- [ ] `directionalAsymmetry`, `maxAsymmetry` の定義が sorry なし
- [ ] `ClassP`, `ClassNP` の定義が sorry なし
- [ ] `p_eq_np_implies_log_bounded` のステートメントが型チェックを通る
- [ ] `p_ne_np_iff_superlog_asymmetry` のステートメントが型チェックを通る
- [ ] `p_sub_np` が sorry なしで証明される
- [ ] 前回証明済みの4補題が新定義体系で再証明される

### Layer 2 完了判定

- [ ] `PartialAssignment`, `solvableRegion`, `localAsymmetry` が sorry なし定義
- [ ] `accumulation_identity` のステートメントが型チェックを通る
- [ ] `AsymmetryReducingTransform` の定義が sorry なし
- [ ] `asymmetryDistribution` の定義が型チェックを通る（MeasureTheory依存）

### Layer 3 完了判定

- [ ] `conjecture_A`, `conjecture_B` が axiom として宣言
- [ ] `conditional_p_ne_np` のステートメントが型チェックを通る
- [ ] `conditional_p_ne_np` が axiom A+B を使って sorry なしで証明される
  （A, B が axiom なので sorryAx は伝播するが、
   A+B → P≠NP の導出自体は sorry なし）
- [ ] `#print axioms conditional_p_ne_np` が 
  `[propext, Classical.choice, Quot.sound, conjecture_A, conjecture_B]` のみ

---

## 7. 既知の落とし穴（v1 からの引き継ぎ + 追加）

### v1 から引き継ぎ

1. **Nat.log vs Real.log**: Real.log で定義し Nat.log に降ろす方針を維持
2. **0 の対数**: `T_M(x) ≥ 1` と `T_V(x,w) ≥ 1` を仮定に入れるか、
   NonZero 制約を構造体に含める
3. **sup の存在**: `Finset.sup'` を使う（前回と同様）
4. **アルファベット**: `Bool` が最もシンプル。`α = Bool` で進めてよい

### v2 追加

5. **Total Candidate Solver の存在**: 
   任意の NPRelation に対して brute-force TCS が存在することを
   `instance` または `lemma` で示す必要がある。
   これがないと `optimalAsymmetry` の iInf が空集合上で発散する。

6. **residualStructuralAsymmetry の定義**:
   Layer 3 の Conjecture A/B で使う。正確な定義は:
   「M が poly-time で実行可能な全 AsymmetryReducingTransform を
   適用した後の、各サイズ n における worst-case localAsymmetry の累積」
   → 定義が複雑なので、Layer 2 で型チェックが通る定義を先に作り、
   Layer 3 ではそれを参照する。
   定義が難しすぎる場合は、抽象化して
   `residualStructuralAsymmetry : NPRelation → TCS → ℕ → ℝ`
   として axiom 内で使う形でもよい。

7. **Cook-Levin の扱い**: 
   Layer 3 の `conditional_p_ne_np` で NP-complete 言語が必要。
   Mathlib に Cook-Levin はない。選択肢:
   (a) NP-complete 性を別の axiom として宣言
   (b) 特定の NP-complete 言語の存在を仮定に入れる
   (c) Conjecture B 自体が「任意の NPRelation について」なので不要かも
   → (c) が最も clean。Thm 2 の証明では任意の R について
   Conj B を適用するので、NP-completeness は不要。

8. **Filter.atTop と ∃ᶠ**:
   Mathlib の `Filter.Frequently` を使う。
   `∃ᶠ n in Filter.atTop, P n` は `∀ N, ∃ n ≥ N, P n` と同値。
   `import Mathlib.Order.Filter.Basic` が必要。

---

## 8. 論文との対応

| 論文セクション | Lean ファイル | Layer |
|---|---|---|
| §2 Preliminaries | Basic.lean | 1 |
| §3.1 Total Candidate Solver | TotalCandidateSolver.lean | 1 |
| §3.2–3.3 A_M, Thm 1 | Asymmetry.lean, Characterization.lean | 1 |
| §4 Distribution | Distribution.lean | 1–2 境界 |
| §5 Five Worlds | (形式化対象外 — 解釈的内容) | — |
| §6 Search Space | SearchSpace.lean | 2 |
| §6.4 Accumulation | Accumulation.lean | 2 |
| §7.2 Meaning Transform | MeaningTransformation.lean | 2 |
| §7.3–7.5 Conj A/B, Thm 2 | Separation.lean | 3 |
| §8 Barriers | (形式化対象外 — メタ分析) | — |
