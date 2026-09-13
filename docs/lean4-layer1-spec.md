# Lean 4 形式検証指示書: Layer 1
## Directional Asymmetry Reformulation of P vs NP — 定義と基本含意

### 目的

P vs NP 問題を「方向非対称性」(Directional Asymmetry) の枠組みで再定式化する論文の、
定義層と基本的な含意関係を Lean 4 + Mathlib で形式検証する。

**この Layer で検証するもの:**
- 方向非対称性 A_n(x) の定義
- P, NP の標準定義との対応関係
- 「P=NP ⟹ sup A_n ∈ O(log n)」の方向
- 「sup A_n ∉ O(log n) ⟹ P≠NP」の対偶

**この Layer では扱わないもの:**
- Cook-Levin 定理の形式化（既存研究に依存、Layer 2）
- 位相不変量による消去不可能性の証明（Layer 3）
- 「意味次元」の形式的定義（後続研究）

---

## 1. プロジェクト構成

```
DirectionalAsymmetry/
├── lakefile.lean
├── lean-toolchain
├── DirectionalAsymmetry/
│   ├── Basic.lean           -- 基本定義
│   ├── Asymmetry.lean       -- A_n(x) の定義と性質
│   ├── Complexity.lean      -- P, NP の定義（自前 or 既存利用）
│   ├── Correspondence.lean  -- P/NP と A_n の対応
│   └── Main.lean            -- 主定理のステートメント
└── README.md
```

### ツールチェーン

- Lean 4 最新安定版
- Mathlib4 最新版（`lakefiles.lean` で依存追加）
- Mathlib の `Computability` 以下を可能な限り利用する

---

## 2. 定義の仕様

### 2.1 計算モデル（Basic.lean）

Mathlib の `Turing.TM1` が利用可能ならそれを使う。
使えない場合は、以下の最小限の抽象化で始める:

```lean
-- 判定問題: 入力を受け取り Yes/No を返す
-- Language として定義（標準的）
def Language (α : Type) := Set (List α)

-- 計算量の抽象: アルゴリズムが入力 x を処理するステップ数
-- 具体的な計算モデルに依存しない抽象層
structure Algorithm (α : Type) where
  decides : Language α           -- このアルゴリズムが判定する言語
  time : List α → ℕ              -- 入力に対する計算時間
  correct : ∀ x, /* 正しく判定する */

-- Verifier: 入力 x と証拠 w を受け取り Yes/No
structure Verifier (α : Type) where
  verifies : Language α
  time : List α → List α → ℕ    -- (input, witness) → steps
  correct : ∀ x w, /* 正しく検証する */
```

**注意:** Mathlib に `Turing.TM1` ベースの P/NP 定義がある場合（PR #35366 参照）、
そちらを使い、上記は互換レイヤーとして書く。
2026年9月時点で Mathlib 本体に merge されていない可能性が高いので、
自前定義で進め、後で接続する方針を取る。

### 2.2 多項式時間（Basic.lean）

```lean
-- 多項式の定義
def IsPolynomial (f : ℕ → ℕ) : Prop :=
  ∃ (c k : ℕ), ∀ n, f n ≤ c * n ^ k + c

-- 漸近記法: f ∈ O(g)
def IsBigO (f g : ℕ → ℕ) : Prop :=
  ∃ (c n₀ : ℕ), ∀ n, n₀ ≤ n → f n ≤ c * g n

-- 注: Mathlib の Asymptotics.IsO が使える場合はそちらを利用
```

### 2.3 P と NP の定義（Complexity.lean）

```lean
-- P: 多項式時間で判定可能な言語のクラス
def P (α : Type) : Set (Language α) :=
  { L | ∃ (A : Algorithm α), A.decides = L ∧ IsPolynomial (fun n => 
    Finset.sup' (/* size n inputs */) A.time) }

-- NP: 多項式時間で検証可能な言語のクラス  
def NP (α : Type) : Set (Language α) :=
  { L | ∃ (V : Verifier α), V.verifies = L ∧ 
    IsPolynomial (fun n => /* V の最大検証時間 */) ∧
    /* witness の長さも多項式有界 */ }
```

**設計判断:**
- worst-case を取る箇所は `Finset.sup'` または `iSup` を使う
- 入力サイズは `List.length` で自然に得られる
- witness の多項式有界性も NP の定義に含める

### 2.4 方向非対称性の定義（Asymmetry.lean）

これが本論文のオリジナル定義。

```lean
-- 方向非対称性（対数スケール）
-- 特定のアルゴリズム M とverifier V に対して定義
noncomputable def directionalAsymmetry 
    (solveCost : List α → ℕ)   -- アルゴリズム M の計算量
    (verifyCost : List α → ℕ)  -- verifier V の計算量
    (x : List α) : ℤ :=
  Int.log 2 (solveCost x) - Int.log 2 (verifyCost x)

-- 注: 実数上の log を使う方が数学的に正確だが、
-- Lean での扱いやすさから整数離散対数で近似する。
-- 必要に応じて Real.log に切り替える。

-- サイズ n における最大方向非対称性（worst-case）
noncomputable def maxAsymmetry
    (solveCost verifyCost : List α → ℕ)
    (n : ℕ) : ℤ :=
  sSup { directionalAsymmetry solveCost verifyCost x | 
         x : List α, x.length = n }

-- 比率版（対数を取らない）
noncomputable def asymmetryRatio
    (solveCost verifyCost : List α → ℕ)
    (x : List α) : ℚ :=
  solveCost x / verifyCost x
```

**注意:** 
- `verifyCost x = 0` のケースの処理が必要（0除算回避）
- `sSup` が存在するには有限性条件が必要 → `Finset` で有限サイズの入力集合を使う
- 実用上は `Finset.sup'` で非空有限集合上の sup を取る方がクリーン

### 2.5 洗練版: 有限集合上の定義

```lean
-- サイズ n の入力の有限集合（アルファベットが Fintype なら有限）
def inputsOfSize [Fintype α] [DecidableEq α] (n : ℕ) : 
    Finset (List α) :=
  (Finset.univ : Finset (Vector α n)).image Vector.toList
  -- または直接構成

-- 有限集合上の worst-case 非対称性
def maxAsymmetryFin [Fintype α] [DecidableEq α]
    (solveCost verifyCost : List α → ℕ)
    (n : ℕ) 
    (hn : (inputsOfSize n : Finset (List α)).Nonempty) : ℤ :=
  (inputsOfSize n).sup' hn 
    (fun x => directionalAsymmetry solveCost verifyCost x)
```

---

## 3. 主要な定理ステートメント（Correspondence.lean）

### 3.1 P=NP ⟹ 非対称性が対数有界

```lean
/-- P=NP ならば、任意の NP 言語に対して、
    ある多項式時間アルゴリズムが存在し、
    方向非対称性の worst-case が O(log n) に収まる -/
theorem p_eq_np_implies_log_bounded_asymmetry
    (h : P α = NP α)
    (L : Language α) (hL : L ∈ NP α)
    (V : Verifier α) (hV : V.verifies = L) :
    ∃ (A : Algorithm α), A.decides = L ∧ 
      IsBigO 
        (fun n => maxAsymmetryFin A.time V.time n)
        (fun n => Nat.log 2 n) := by
  sorry -- Layer 1 では statement のみ、証明は後
```

**証明の方針メモ（sorry を埋める際の指針）:**
- `h : P = NP` から `L ∈ P` が得られる
- `L ∈ P` の定義から多項式時間アルゴリズム A が存在
- A.time(x) ≤ c · n^k（多項式有界）
- V.time(x) も多項式有界（NP の定義から）
- 両方が多項式なので、対数の差は O(log n)
- 具体的には log(c₁·n^k₁) - log(c₂·n^k₂) = O(log n)

### 3.2 対偶: 非対称性が超対数的 ⟹ P≠NP

```lean
/-- 方向非対称性の worst-case が O(log n) に収まらない
    NP 言語が存在するならば、P≠NP -/
theorem superlog_asymmetry_implies_p_ne_np
    (L : Language α) (hL : L ∈ NP α)
    (V : Verifier α) (hV : V.verifies = L)
    (h : ∀ (A : Algorithm α), A.decides = L → 
      ¬ IsBigO 
        (fun n => maxAsymmetryFin A.time V.time n)
        (fun n => Nat.log 2 n)) :
    P α ≠ NP α := by
  sorry -- 対偶なので 3.1 から直ちに従う
```

### 3.3 非対称性と既存概念の対応

```lean
/-- worst-case 非対称性は worst-case 計算量の差に対応する -/
theorem maxAsymmetry_eq_worstcase_diff
    (solveCost verifyCost : List α → ℕ) (n : ℕ) :
    maxAsymmetryFin solveCost verifyCost n = 
    /* worst-case solve time の対数 */ - 
    /* worst-case verify time の対数 */ := by
  sorry

/-- 平均非対称性の定義（average-case への接続用） -/
noncomputable def avgAsymmetry 
    (solveCost verifyCost : List α → ℕ)
    (μ : Finset (List α) → ℝ)  -- 入力上の測度
    (n : ℕ) : ℝ :=
  sorry -- 期待値の定義、Mathlib の MeasureTheory を利用

/-- P ⊆ NP は非対称性の言語でも自然に出る -/
theorem p_sub_np_via_asymmetry :
    P α ⊆ NP α := by
  sorry -- 標準的証明: 多項式時間アルゴリズムは自明な verifier を持つ
```

---

## 4. 補助的な補題

### 4.1 多項式の対数は O(log n)

```lean
/-- 多項式関数の対数は O(log n) -/
lemma log_polynomial_is_O_log 
    (f : ℕ → ℕ) (hf : IsPolynomial f) :
    IsBigO (fun n => Nat.log 2 (f n)) (fun n => Nat.log 2 n) := by
  sorry
  -- 証明: f(n) ≤ c·n^k なので log f(n) ≤ log c + k·log n = O(log n)
```

### 4.2 多項式どうしの対数差は O(log n)

```lean
/-- 2つの多項式関数の対数の差は O(log n) -/
lemma log_diff_polynomials_is_O_log
    (f g : ℕ → ℕ) (hf : IsPolynomial f) (hg : IsPolynomial g) :
    IsBigO 
      (fun n => Int.natAbs (Int.log 2 (f n) - Int.log 2 (g n)))
      (fun n => Nat.log 2 n) := by
  sorry
  -- これが 3.1 の核心的補題
```

### 4.3 指数関数の対数は Ω(n)

```lean
/-- 指数関数の対数は少なくとも線形に成長する -/
lemma log_exponential_is_linear
    (b : ℕ) (hb : 2 ≤ b) :
    ∀ n, n ≤ Nat.log 2 (b ^ n) := by
  sorry
  -- これが「非対称性が超対数的になりうる」ことの基盤
```

---

## 5. 実装上の注意点

### 5.1 Mathlib との接続

以下の Mathlib モジュールの利用を検討:

| 必要な概念 | Mathlib モジュール | 備考 |
|---|---|---|
| 漸近記法 O(·) | `Mathlib.Analysis.Asymptotics.Asymptotics` | `IsO`, `IsBigO` |
| 対数 | `Mathlib.Analysis.SpecialFunctions.Log.Basic` | `Real.log` |
| 自然数の対数 | `Mathlib.Data.Nat.Log` | `Nat.log` |
| 有限集合の sup | `Mathlib.Order.Finset` | `Finset.sup'` |
| TM の定義 | `Mathlib.Computability.TuringMachine` | `Turing.TM1` |
| 測度論 | `Mathlib.MeasureTheory` | average-case 用 |

### 5.2 計算モデルの選択について

**推奨:** Mathlib の `Turing.TM1` をベースにする。
ただし step counting が Mathlib 本体にまだ入っていない場合:

1. Issue #35366 のコードを参考に `runN` を自前実装する
2. または計算モデルを抽象化して、`Algorithm` 構造体を
   `time : List α → ℕ` だけ持つ形にする（モデル非依存）

**Layer 1 としては抽象層で十分。** 
計算モデルの具体的な接続は Layer 2 以降で行う。

### 5.3 sorry の扱い

Layer 1 の目的は**定義の整合性確認**と**ステートメントの型チェック**。

- すべての `theorem` / `lemma` は `sorry` で置いてよい
- ただし **`def` と `structure` には sorry を使わない**
  （定義が型チェックを通ることが Layer 1 の最低要件）
- sorry を使った箇所には `-- TODO: Layer N で証明` のコメントを付ける

### 5.4 段階的に sorry を埋める優先順位

1. `p_sub_np_via_asymmetry`（P ⊆ NP、最も標準的）
2. `log_polynomial_is_O_log`（純粋な数学、Mathlib に近い補題がある可能性）
3. `log_diff_polynomials_is_O_log`（上の系）
4. `p_eq_np_implies_log_bounded_asymmetry`（1-3 を組み合わせ）
5. `superlog_asymmetry_implies_p_ne_np`（4 の対偶、ほぼ自動）

---

## 6. 成功基準

Layer 1 が完了したと判断する基準:

- [ ] `lake build` がエラーなしで通る
- [ ] `def` / `structure` / `class` に sorry がない
- [ ] `directionalAsymmetry` の定義が型チェックを通る
- [ ] `maxAsymmetryFin` の定義が型チェックを通る
- [ ] `p_eq_np_implies_log_bounded_asymmetry` のステートメントが型チェックを通る
- [ ] `superlog_asymmetry_implies_p_ne_np` のステートメントが型チェックを通る
- [ ] P ⊆ NP が非対称性の枠組み内でも自然に述べられる

**ボーナス（できれば）:**
- [ ] `p_sub_np_via_asymmetry` の sorry を埋める
- [ ] `log_polynomial_is_O_log` の sorry を埋める
- [ ] Mathlib の `Asymptotics.IsO` を使った版も用意する

---

## 7. 背景: 論文全体の構造（参考）

この Layer 1 は以下の論文構造の Section 2 に対応する:

```
Section 1: Introduction — P vs NP の既存定式化の問題点
Section 2: Definitions — A_n(x), 分布 D_n の形式的定義  ← Layer 1
Section 3: Correspondence — P/NP と非対称性の対応     ← Layer 1
Section 4: Cumulative Asymmetry — 局所非対称性の指数累積 ← Layer 2
Section 5: Expressiveness — Cook-Levin からの帰結       ← Layer 2  
Section 6: Topological Obstruction — 位相的消去不可能性  ← Layer 3
Section 7: Main Theorem — P ≠ NP                        ← Layer 3
Section 8: Discussion — 統一的枠組みとしての意義
```

---

## 8. 既知の落とし穴

1. **Nat.log vs Real.log**: 自然数の対数は floor を取るため、
   差を取ると ±1 のずれが出る。Real.log を使う場合は
   `noncomputable` が必要になるが数学的にはクリーン。
   **推奨: 定義は Real.log で行い、計算が必要な補題で Nat.log に降ろす。**

2. **0 の対数**: `Nat.log 2 0 = 0`, `Real.log 0 = 0` (Mathlib)。
   verifyCost x = 0 のケースは「計算不要」なので定義から除外するか、
   `verifyCost x ≥ 1` の仮定を入れる。

3. **sup の存在**: `sSup` を使う場合は `ConditionallyCompleteLattice` が必要。
   有限集合上の `Finset.sup'` を使う方が安全。

4. **入力の有限性**: アルファベット α が `Fintype` であれば、
   サイズ n の入力は有限集合。`Bool` をアルファベットにすれば最もシンプル。

5. **uniform algorithm の制約**: 
   同一のアルゴリズムが全入力サイズで動くことを、
   単一の `Algorithm` 値として表現する。
   入力ごとに別のアルゴリズムを選ぶ non-uniform（回路）は扱わない。
