# Lean 4 形式検証指示書 v3：具体コストモデル版
## Directional Asymmetry — 論文 rev1 準拠

対象論文: "Computational Directional Asymmetry: A Distributional Reformulation of P vs NP"（rev1、I&C リジェクト後の改訂版）
環境: Lean 4 v4.33.1 / Mathlib v4.33.1（v2 から継続）

---

## 0. この版の目的

### 0.1 論文 rev1 の数学的変更

I&C の査読で、定理1（⟹）の証明が「任意の NP relation で search が decision に帰着する」と暗黙に仮定していると指摘された（実際には一般に成り立たない）。論文 rev1 では次の3点を変更した。

1. 定理1を「言語ごとの主張」から「クラス単位の三同値」に変更した。証明は prefix 言語 Pref_R を経由する。
2. 定義3'を各点最適値 inf_M A_M(x) から、一様な最悪ケース・プロファイル g_M に変更した（各点最適値は退化する）。
3. スペクトルを「O(log n) 差を同一視する同値類」で定義し直し、命題1（P = NP ⇔ Σ = {[0]}）を厳密に成立させた。

### 0.2 v2 形式化の問題（3つ）

1. **時間が抽象フィールド。** `solveTime` が `solve` と無関係な数値なので、relation 間の solver 移送（`transportSolver`）がコストゼロになる。定理1（⟹）の実質である Pref_R 経由の探索アルゴリズムを、一切検証していない。
2. **各点最適値。** `optimalAsymmetry` が各点 `iInf` になっており、論文 rev1 §3.2 が示す通り退化している。入力 x の答えを定数として埋め込んだ solver を使えば、常に O(log n) になる。
3. **【最重要】公理系の矛盾の疑い。** v2 指示書（指示書作成側の誤り）は、Conjecture B を**すべての** NPRelation に量化した `axiom` として指定した。自明な relation（例：rel ≡ False、solver は定数出力）に Conjecture B を適用し、Conjecture A と組み合わせると `False` が導ける可能性が高い。そうであれば `conditional_p_ne_np` は空虚に成立しており、検証として無意味になる。論文の Conjecture B は NP 完全 relation に限定されているので、ずれは Lean 側だけにある。

### 0.3 v3 の三原則

- **(P1) 時間は実行から導出する。** アルゴリズムは深い埋め込みのプログラム（構文）で表し、コストはインタプリタ（意味論）が決める。構造体に時間フィールドを持たせない。
- **(P2) 最適性は一様に扱う。** 単一の solver がすべての入力を扱う形でのみ述べる。
- **(P3) 独自の `axiom` をゼロにする。** 予想は `def … : Prop` として定義し、定理の仮定として明示する。

### 0.4 仕様の誤りを見つけたら

v1・v2 と同様、この指示書にも型の不整合や数学的な誤りが残っている可能性がある。その場合は**論文 rev1 の数学的意図を優先して**修正し、逸脱として報告すること。Mathlib の API 名は指示書を信用せず、`#check` / `exact?` で確認すること。

---

## 1. 構成

```
DirectionalAsymmetry/
├── Concrete/
│   ├── Encoding.lean        -- BStr、対の符号化 enc/dec
│   ├── Prog.lean            -- プログラム言語（深い埋め込み）とコスト意味論 Eval
│   ├── Interp.lean          -- 燃料付き実行可能インタプリタと健全性
│   ├── Poly.lean            -- 多項式上界と閉包性
│   ├── Classes.lean         -- PolyTime, ClassP, NPRel, ClassNP, PeqNP, Reduces, IsNPComplete
│   ├── TCS.lean             -- TCS、asym、profile、LogBounded、普遍下界
│   ├── Prefix.lean          -- prefRel、prefixSearch とその正当性・コスト
│   ├── Characterization.lean -- 定理1、系1、系2
│   ├── Spectrum.lean        -- AsymClass、achievable、classOf、spectrum、命題1
│   └── Degeneracy.lean      -- 各点最適値の退化（推奨ボーナス）
├── Search/                  -- v2 の Layer 2（SearchSpace, Accumulation, MeaningTransformation）を移動・維持
├── Distribution.lean        -- 具体版 asym に合わせて改修
├── Separation.lean          -- 全面改訂（axiom 廃止）
├── Main.lean
Legacy/                      -- v2 抽象層（ビルド対象外。削除でも可）
Test/
├── NoSorryInDefs.lean       -- 継続（対象を v3 の宣言に更新）
├── NoCustomAxioms.lean      -- 新規：主要定理の #print axioms 監査
└── Exec.lean                -- 新規：実行テスト
```

---

## 2. Phase 0：着手前の確認

1. **v2 の矛盾の実証（削除前に行う）。** v2 環境のまま、`conjecture_A`・`conjecture_B` と自明な relation（rel ≡ False、定数出力の solver、`solveTime ≡ 1`）から `example : False` が導けるか試す。導けたかどうかと、その証明を報告すること。論文の説明責任に関わるため、結果が否定的（導けない）でも報告してほしい。
2. v2 の `axiom conjecture_A` / `axiom conjecture_B` を削除する。v2 抽象層は `Legacy/` に移してデフォルトのビルド対象から外す（git 履歴に任せて削除してもよい）。
3. Layer 2 の既存の証明（`accumulation_identity`、`structuralAsymmetry_eq_log_prod` など）は壊さない。

---

## 3. Phase A：計算モデル

### 3.1 データと符号化（Encoding.lean）

```lean
abbrev BStr := List Bool

/-- 対の符号化の一例：a の各ビット c を [true, c] に展開し、区切りの false の後に b をそのまま置く -/
def enc (a b : BStr) : BStr := a.flatMap (fun c => [true, c]) ++ false :: b

/-- 全域の復号（不正な入力でも何かを返す） -/
def dec : BStr → BStr × BStr := ...
```

符号化の具体形は変えてよい。ただし次の4補題が成り立つこと。

- `dec_enc : dec (enc a b) = (a, b)`
- `enc_length : (enc a b).length = 2 * a.length + 1 + b.length`（線形であれば形は問わない）
- `dec_fst_length_le : (dec y).1.length ≤ y.length`
- `dec_snd_length_le : (dec y).2.length ≤ y.length`

### 3.2 プログラム言語（Prog.lean）

推奨の構成子（`comp f g` は「f を先に実行し、その出力に g を適用」）：

```lean
inductive Prog where
  | id                        -- x ↦ x
  | const (w : BStr)          -- x ↦ w
  | head                      -- x ↦ x.take 1
  | tail                      -- x ↦ x.drop 1
  | fst                       -- y ↦ (dec y).1
  | snd                       -- y ↦ (dec y).2
  | append                    -- y ↦ (dec y).1 ++ (dec y).2
  | eqConst (w : BStr)        -- x ↦ [decide (x = w)]
  | comp (f g : Prog)         -- x ↦ g (f x)
  | pair (f g : Prog)         -- x ↦ enc (f x) (g x)
  | ite (c f g : Prog)        -- c x = [true] なら f x、それ以外なら g x
  | loop (c b : Prog)         -- c s = [true] の間 s := b s。止まったら s を返す
```

`head`・`tail` は、モデルを一般的な計算に対して完全（TM と多項式同値）にするために入れている。定理1の証明自体には使わない。

### 3.3 コスト意味論

大ステップの帰納的関係 `Eval : Prog → BStr → BStr → ℕ → Prop`（「P は入力 x で出力 y を返し、t ステップで停止する」）で定義する。

| 構成子 | 出力 | コスト t |
|---|---|---|
| `id` | x | 1 + 2\|x\| |
| `const w` | w | 1 + \|w\| |
| `head` / `tail` / `fst` / `snd` / `append` | 表の通り | 1 + \|x\| + \|y\| |
| `eqConst w` | [x = w] | 2 + \|x\| + \|w\| |
| `comp f g` | g (f x) | t_f + t_g + 1 |
| `pair f g` | enc (f x) (g x) | t_f + t_g + 1 + \|y\| |
| `ite c f g` | 分岐先の出力 | t_c + t_分岐 + 1 |
| `loop c b` | 下記 | 下記 |

`loop` の規則：

```
stop : Eval c s r tc → r ≠ [true] → Eval (loop c b) s s (tc + 1)
step : Eval c s [true] tc → Eval b s s' tb → Eval (loop c b) s' y t
       → Eval (loop c b) s y (tc + tb + t + 1)
```

発散する実行には導出が存在しない（部分関数）。

### 3.4 必須補題

- `Eval.deterministic : Eval P x y t → Eval P x y' t' → y = y' ∧ t = t'`
- `Eval.cost_pos : Eval P x y t → 1 ≤ t`
- `Eval.size_le : Eval P x y t → y.length ≤ x.length + t`（**サイズ–コスト不変量**）
- 各構成子の反転補題（必要に応じて）

### 3.5 設計上の必須要件

- **(R1) 構成子は固定の単純な操作に限る。** 任意の Lean 関数を受け取る構成子（例：`map (f : BStr → BStr)`）は禁止する。これを許すと v2 と同じく「計算がタダ」になる。
- **(R2) 各プリミティブのコストは「1 + 読む入力長 + 出力長」以上とする。** 単位コストでデータを倍化できると、n ステップで長さ 2^n のデータが作れ、「多項式ステップ」が多項式時間の意味を失う。サイズ–コスト不変量がこれを防ぎ、モデルの P/NP が TM 版と多項式同値になるための前提になる。なお、この同値そのものは形式化しない（論文側に仮定として明記する）。
- **(R3) solver・verifier・decider・reduction はすべて `Prog` の値とする。** 時間は `Eval` から一意に決まる値として定義する。決定性補題で一意性を示したうえで `Classical.choose` で値を取り出すのは構わない。存在仮定から `Prog` を取り出すのに選択公理を使うのも構わない（例：P = NP から decider D を得る）。禁止するのは、プログラムの振る舞いや時間を DSL の外の Lean 関数で定めること。

### 3.6 実行可能インタプリタ（Interp.lean）

- 燃料付きの `run : ℕ → Prog → BStr → Option (BStr × ℕ)` を定義する。
- 健全性 `run fuel P x = some (y, t) → Eval P x y t` を証明する。
- 小さなプログラムを `decide` / `rfl` で実行してテストできるようにする。`native_decide` は `Lean.ofReduceBool` 公理が入るので使わない。

---

## 4. Phase B：計算量クラス（Poly.lean, Classes.lean）

```lean
/-- 単調な形の多項式上界 -/
def PolyBound (T : ℕ → ℕ) : Prop := ∃ c k : ℕ, ∀ n, T n ≤ c * (n + 1) ^ k

def PolyTime (P : Prog) : Prop :=
  ∃ c k : ℕ, ∀ x, ∃ y t, Eval P x y t ∧ t ≤ c * (x.length + 1) ^ k

def Decides (D : Prog) (L : Set BStr) : Prop :=
  (∀ x, ∃ y t, Eval D x y t) ∧ ∀ x y t, Eval D x y t → (y = [true] ↔ x ∈ L)

def ClassP : Set (Set BStr) := {L | ∃ D, PolyTime D ∧ Decides D L}

structure NPRel where
  rel       : BStr → BStr → Prop
  V         : Prog
  V_poly    : PolyTime V        -- 入力 enc x w の長さに関して多項式（すべての w について）
  V_decides : ∀ x w y t, Eval V (enc x w) y t → (y = [true] ↔ rel x w)
  q         : ℕ → ℕ
  q_poly    : PolyBound q
  bound     : ∀ x w, rel x w → w.length ≤ q x.length

def NPRel.lang (R : NPRel) : Set BStr := {x | ∃ w, R.rel x w}
def ClassNP : Set (Set BStr) := {L | ∃ R : NPRel, R.lang = L}
def PeqNP : Prop := ClassNP ⊆ ClassP

def Reduces (L₁ L₂ : Set BStr) : Prop :=
  ∃ f, PolyTime f ∧ ∀ x y t, Eval f x y t → (x ∈ L₁ ↔ y ∈ L₂)

def IsNPComplete (L : Set BStr) : Prop := L ∈ ClassNP ∧ ∀ L' ∈ ClassNP, Reduces L' L
```

`V_poly` は長い証拠も含めたすべての入力で、入力長の多項式として時間を縛る。長い証拠を読むにはその分の時間がかかるが、それは入力長の多項式に収まるので問題ない。v2 の反例（短い証拠についてしか縛っていなかった）はこれで構造的に起きなくなる。

必須補題：

- `PolyBound` の和・積・合成に関する閉包
- `polyTime_comp`、`polyTime_pair`、`polyTime_ite`（合成ではサイズ–コスト不変量を使う）
- `p_sub_np : ClassP ⊆ ClassNP`
  - verifier の例：`ite (comp snd (eqConst [])) (comp fst D) (const [false])`
  - rel x w := x ∈ L ∧ w = []、q := 0
- `inP_of_reduces : Reduces L₁ L₂ → L₂ ∈ ClassP → L₁ ∈ ClassP`（判定器は `comp f D`）
- `trivialRel : NPRel`（rel := False、V := const [false]、q := 0）と `Nonempty NPRel`

---

## 5. Phase C：TCS と非対称性（TCS.lean）

```lean
structure TCS (R : NPRel) where
  M       : Prog
  total   : ∀ x, ∃ y t, Eval M x y t
  correct : ∀ x y t, Eval M x y t → x ∈ R.lang → R.rel x y
  short   : ∀ x y t, Eval M x y t → y.length ≤ R.q x.length
  -- 時間フィールドは持たない（P1）
```

定義：

- `out M x`、`time M x`：`total` と決定性から一意に定まる出力と時間
- `vtime R x w`：`R.V` の `enc x w` 上の時間
- `asym M x : ℤ := Nat.log 2 (time M x) - Nat.log 2 (vtime R x (out M x))`（論文の定義3）
- `profile M n : ℤ :=` 長さ n の全入力にわたる `asym M x` の最大値（論文の定義3'。v2 の `inputsOfSize` を再利用してよい）
- `LogBounded (f : ℕ → ℤ) : Prop := ∃ C : ℕ, ∀ n, f n ≤ C * (Nat.log 2 n + 1)`

必須補題：

- `asym_lower : ∀ R (M : TCS R), ∃ C : ℕ, ∀ n, -(C * (Nat.log 2 n + 1) : ℤ) ≤ profile M n`（普遍下界、論文 §3.2）
- `logBounded_of_polyTime : PolyTime M.M → LogBounded (profile M)`
- `polyTime_of_logBounded : LogBounded (profile M) → PolyTime M.M`（(c)⇒(a) の核）
  - ヒント：`Nat.log 2 a ≤ b → a < 2 ^ (b + 1)` と `2 ^ Nat.log 2 n ≤ n` を使い、T_M < 2・(2(n+1))^C・T_V を示す。T_V は `short` と `V_poly` から多項式で抑えられる。
- `lang_inP_of_polyTime_tcs : PolyTime M.M → R.lang ∈ ClassP`（判定器は `comp (pair id M.M) R.V`）

---

## 6. Phase D：定理1（Prefix.lean, Characterization.lean）

### 6.1 prefix relation（論文 §3.3 の Pref_R）

```lean
def prefRel (R : NPRel) : NPRel where
  rel y v := R.rel (dec y).1 ((dec y).2 ++ v)
  -- enc (enc x u) v ↦ enc x (u ++ v) ↦ R.V
  V := comp (pair (comp fst fst) (comp (pair (comp fst snd) snd) append)) R.V
  q := fun n => c * (n + 1) ^ k   -- R.q_poly の多項式（単調）を使う
  ...
```

必須：`prefRel_mem_iff : enc x u ∈ (prefRel R).lang ↔ ∃ v, R.rel x (u ++ v)`

証拠長の上界は |v| ≤ |u ++ v| ≤ R.q |x| ≤ c(|x|+1)^k ≤ c(|enc x u|+1)^k で得られる。

### 6.2 prefix 探索プログラム

```lean
def initS : Prog := pair id (const [])                                        -- x ↦ enc x []
def ext (b : Bool) : Prog := pair fst (comp (pair snd (const [b])) append)   -- enc x u ↦ enc x (u ++ [b])
def notP : Prog := ite id (const [false]) (const [true])

def prefixSearch (D V : Prog) : Prog :=
  ite (comp initS D)
      (comp initS (comp (loop (comp V notP)
                              (ite (comp (ext false) D) (ext false) (ext true)))
                        snd))
      (const [])
```

擬似コード：

```
M(x):
  if D(enc x []) ≠ [true] then return []
  s := enc x []
  while V(s) ≠ [true]:        -- s = enc x u は V の入力形式と一致する
    s := if D(enc x (u ++ [0])) = [true] then enc x (u ++ [0]) else enc x (u ++ [1])
  return snd s                 -- = u
```

必須定理：

- **不変量**：ループ中の各状態 enc x u について ∃ v, R.rel x (u ++ v)。u が証拠でなければ v ≠ [] なので、v の先頭ビットで分岐すれば不変量が保たれる。
- **停止性**：反復回数 ≤ R.q |x|（測度 R.q |x| − |u|）
- `prefixSearch_tcs : Decides D (prefRel R).lang → TCS R`（M := `prefixSearch D R.V`）
- `prefixSearch_polyTime : PolyTime D → Decides D (prefRel R).lang → PolyTime (prefixSearch D R.V)`
  - 1反復のコストは |enc x u| ≤ 2|x| + 1 + q(|x|) の入力に対する V と D のコストで抑えられ、それが高々 q(|x|) + 1 回繰り返される。

### 6.3 定理1と系

```lean
theorem thm1_a_to_b : PeqNP → ∀ R : NPRel, ∃ M : TCS R, PolyTime M.M ∧ LogBounded (profile M)
theorem thm1_b_to_a : (∀ R : NPRel, ∃ M : TCS R, LogBounded (profile M)) → PeqNP
theorem thm1_c_to_a : ∀ R : NPRel, IsNPComplete R.lang →
    (∃ M : TCS R, LogBounded (profile M)) → PeqNP
theorem thm1_a_iff_b : PeqNP ↔ ∀ R : NPRel, ∃ M : TCS R, LogBounded (profile M)
theorem thm1_a_iff_c : ∀ R : NPRel, IsNPComplete R.lang →
    (PeqNP ↔ ∃ M : TCS R, LogBounded (profile M))

theorem cor1  : ¬ PeqNP ↔ ∃ R : NPRel, ∀ M : TCS R, ¬ LogBounded (profile M)
theorem cor1' : ¬ PeqNP → ∀ R : NPRel, IsNPComplete R.lang → ∀ M : TCS R, ¬ LogBounded (profile M)
theorem cor2  : ∀ R : NPRel, IsNPComplete R.lang →
    (R.lang ∈ ClassP ↔ ∃ M : TCS R, LogBounded (profile M))
```

- `thm1_a_to_b`：PeqNP から (prefRel R).lang ∈ ClassP を得て decider D を取り出し、`prefixSearch D R.V` を使う。**`transportSolver` のような移送は使わない。**
- 論文の (b)⇒(c) は Cook–Levin（NP 完全 relation の存在）を使う。Lean では Cook–Levin を形式化せず、(c) を「NP 完全な R について」の形（`thm1_a_iff_c`）で述べることで不要にする。

---

## 7. Phase E：スペクトル（Spectrum.lean）

```lean
def Profile := ℕ → ℤ

instance : Preorder Profile where
  le f g := ∃ C : ℕ, ∀ n, f n ≤ g n + C * (Nat.log 2 n + 1)
  ...

abbrev AsymClass := Antisymmetrization Profile (· ≤ ·)
def cls (f : Profile) : AsymClass := toAntisymmetrization (· ≤ ·) f
def zeroClass : AsymClass := cls (fun _ => 0)

def achievable (R : NPRel) : Set AsymClass := {c | ∃ M : TCS R, cls (profile M) = c}

/-- none は論文の ⊥（最小元が存在しない） -/
noncomputable def classOf (R : NPRel) : Option AsymClass :=
  if h : ∃ c, IsLeast (achievable R) c then some h.choose else none

def spectrum : Set (Option AsymClass) := Set.range classOf

theorem prop1 : PeqNP ↔ spectrum = {some zeroClass}
```

- ⊥ には `WithBot` ではなく `Option` の `none` を使う。論文の ⊥ は「未定義」であって「[0] より小さい」ではないため、順序構造を持ち込まないこと。
- 補助補題：
  - `zeroClass_le : ∀ M, zeroClass ≤ cls (profile M)`（`asym_lower` から）
  - `cls_le_zero_iff : cls (profile M) ≤ zeroClass ↔ LogBounded (profile M)`
- `prop1` の → 方向では `Set.range` の非空性のために `Nonempty NPRel` を使う。

---

## 8. Phase F：各点最適値の退化（Degeneracy.lean）［推奨ボーナス］

```lean
theorem pointwise_degenerate (R : NPRel) (M₀ : TCS R) :
    ∃ C : ℕ, ∀ x, ∃ M : TCS R, asym M x ≤ C * (Nat.log 2 x.length + 1)
```

- 構成：`M := ite (eqConst x) (const w) M₀.M`。w は、x ∈ R.lang なら証拠（`Classical.choose`）、そうでなければ [] とする。
- 定数 w をプログラムに埋め込むことが「インスタンスごとの最適化」の正体であり、P = NP か否かに関係なく成立する。論文 rev1 §3.2 の Uniformity の注を形式的に裏づける。
- C は x に依存しない（R.q の多項式とプリミティブのコストだけで決まる）ことに注意。
- 任意の追加課題：長さごとの版（長さ n の全入力に対する head/tail の決定木で、profile M n ≤ C(log n + 1) とするもの）。

---

## 9. Phase G：分離プログラム（Separation.lean 全面改訂）

```lean
/-- 論文の定義8：ブラックボックス（中身は与えない） -/
opaque residual : (R : NPRel) → TCS R → ℕ → ℤ

def Unbounded (f : ℕ → ℤ) : Prop :=
  ∀ C : ℕ, ∃ᶠ n in Filter.atTop, (C * (Nat.log 2 n + 1) : ℤ) < f n

/-- 論文の予想A -/
def ConjA : Prop :=
  ∀ (R : NPRel) (M : TCS R), PolyTime M.M → Unbounded (residual R M) → Unbounded (profile M)

/-- 論文の予想B（NP 完全 relation に限定） -/
def ConjB : Prop :=
  ∀ (R : NPRel), IsNPComplete R.lang →
    ∀ (M : TCS R), PolyTime M.M → Unbounded (residual R M)

/-- 論文の定理2。予想は仮定として明示し、NP 完全 relation の存在（Cook–Levin）も仮定にする -/
theorem thm2 (hA : ConjA) (hB : ConjB) (hCL : ∃ R : NPRel, IsNPComplete R.lang) : ¬ PeqNP
```

- 証明の方針：PeqNP を仮定し、`thm1_a_to_b` で NP 完全な R に対する多項式時間・`LogBounded` な M を得る。ConjB から residual が Unbounded、ConjA から profile が Unbounded になり、`LogBounded` と矛盾する。
- 補題 `not_unbounded_of_logBounded` を用意する。
- **`axiom` はプロジェクト全体で使わない。** `#print axioms thm2` が `[propext, Classical.choice, Quot.sound]` のみであること。

### 9.1 回帰テスト：v2 型の過剰量化が矛盾することの形式的証明

```lean
/-- v2 型：NP 完全性の仮定のない予想B -/
def ConjB_allRel : Prop :=
  ∀ (R : NPRel) (M : TCS R), PolyTime M.M → Unbounded (residual R M)

theorem v2_style_inconsistent : ConjA → ConjB_allRel → False
```

- `trivialRel` と `M := const []` を使う（profile は定数なので Unbounded にならない）。
- この定理が証明できること自体が、「予想Bの量化を NP 完全 relation に限定しなければならない」ことの形式的証拠になる。

---

## 10. Layer 2 の扱い

- `SearchSpace`・`Accumulation`・`MeaningTransformation` は維持する（時間モデルに依存しないため）。
- 論文 rev1 で定義7が "Structure-Revealing Transformation" に改名されたので、`StructureRevealingTransform` を別名として追加する。
- `Distribution`：具体版の `asym` の押し出し測度として定義し直す。
- **ボーナス（ブリッジ補題）**：論文 §3.3 の「Pref_R は solvable region の一般化」を、SAT 型の関係について示す。

```lean
/-- u を先頭から割り当てた部分割り当て -/
def prefixPA (n : ℕ) (u : List Bool) : PartialAssignment n := ...

theorem prefix_mem_solvable_iff (φ : (Fin n → Bool) → Prop) (u : List Bool) (hu : u.length ≤ n) :
    prefixPA n u ∈ solvableRegion φ ↔
      ∃ v, (u ++ v).length = n ∧ φ (toAssign (u ++ v))
```

---

## 11. 成功基準（チェックリスト）

### Phase A–B
- [ ] `lake build` がエラー・警告なしで通る
- [ ] `Eval.deterministic`、`Eval.cost_pos`、`Eval.size_le` を証明
- [ ] `run` の健全性を証明し、`Test/Exec.lean` で実行テストが通る
- [ ] `p_sub_np`、`inP_of_reduces`、`Nonempty NPRel` を証明

### Phase C–D（定理1）
- [ ] `TCS` に時間フィールドがない（`Concrete/` に `solveTime` という名前が出現しない）
- [ ] `asym_lower`、`logBounded_of_polyTime`、`polyTime_of_logBounded` を証明
- [ ] `prefRel_mem_iff`、`prefixSearch_tcs`、`prefixSearch_polyTime` を証明
- [ ] `thm1_*`、`cor1`、`cor1'`、`cor2` をすべて sorry なしで証明
- [ ] `thm1_a_to_b` の証明が移送（`transportSolver` 相当）を使っていない

### Phase E–G
- [ ] `prop1` を証明
- [ ] （推奨）`pointwise_degenerate` を証明
- [ ] `thm2` と `v2_style_inconsistent` を証明
- [ ] プロジェクト全体で `axiom` 宣言がゼロ
- [ ] `#print axioms` の対象（`thm1_*`、`cor*`、`prop1`、`pointwise_degenerate`、`thm2`、`v2_style_inconsistent`）がすべて `[propext, Classical.choice, Quot.sound]` の部分集合

### 実行テスト（Test/Exec.lean）の最低ライン
- 玩具の relation：rel x w := (w = [true])（どの x にも証拠 [true] がある）
  - `V := comp snd (eqConst [true])`
  - Pref の decider：`D := comp snd (ite (eqConst []) (const [true]) (eqConst [true]))`
- `run` で `prefixSearch D V` を小さな入力に対して実行し、出力が [true] であること、返るステップ数が `Eval` のコストと一致することを `decide` / `rfl` で確認する。

---

## 12. 既知の落とし穴

1. `native_decide` を使わない（`Lean.ofReduceBool` 公理が混入する）。
2. `Nat.log` は床関数。n = 0, 1 で 0 になるので、上界は `C * (Nat.log 2 n + 1)` の形で統一する。
3. ℤ と ℕ のキャスト。`asym` は ℤ、`time` は ℕ。
4. `loop` の停止性とコストは、反復回数に関する帰納法と不変量で示す。`Eval` の導出に関する帰納法を直接使うと扱いにくい場合がある。
5. `Antisymmetrization` / `toAntisymmetrization` の API 名は現行 Mathlib で確認する。
6. `Filter.Frequently`（`∃ᶠ`）の API も確認する。
7. `Option` と `WithBot` を混同しない（第7節）。
8. `decide` による実行テストは燃料と入力を小さく保つ（評価が重くなる）。
9. 多項式の合成では、入力サイズが（サイズ–コスト不変量により）前段のコストだけ増える点を忘れない。

---

## 13. 報告してほしいこと

1. Phase 0 の結果（v2 の公理から `False` が導けたか、その証明）
2. 仕様からの逸脱と理由の一覧（v1・v2 と同様の形式で）
3. 第11節の各項目の `#print axioms` 出力
4. 実行テストの結果
5. ボーナス（`pointwise_degenerate`、長さごとの版、`prefix_mem_solvable_iff`）の達成状況
6. 論文 rev1 の数学的内容に誤りや曖昧さを見つけた場合、その指摘

---

## 14. 論文 rev1 との対応

| 論文 rev1 | Lean（v3） |
|---|---|
| 定義1 NP relation（§2） | `NPRel` |
| 定義2 TCS（§3.1） | `TCS` |
| 定義3 A_M(x)（§3.2） | `asym` |
| 定義3' プロファイル g_M（§3.2） | `profile` |
| 普遍下界（§3.2） | `asym_lower` |
| 一様性の注（§3.2） | `pointwise_degenerate` |
| Pref_R（§3.3） | `prefRel`、`prefixSearch` |
| 定理1（§3.3） | `thm1_a_to_b`、`thm1_b_to_a`、`thm1_c_to_a`、`thm1_a_iff_b`、`thm1_a_iff_c` |
| 系1・系2（§3.3） | `cor1`、`cor1'`、`cor2` |
| 定義4（§4.1） | `Distribution` |
| 定義4'・4''（§4.3） | `AsymClass`、`achievable`、`classOf`、`spectrum` |
| 命題1（§4.3） | `prop1` |
| 定義5・6、命題2（§5） | `solvableRegion`、`localAsymmetry`、`accumulation_identity` |
| 定義7（§5.6） | `StructureRevealingTransform` |
| 定義8（§6.2） | `residual`（opaque） |
| 予想A・B（§6.2–6.3） | `ConjA`、`ConjB`（`Prop`。axiom ではない） |
| 定理2（§6.4） | `thm2` |
| — | `v2_style_inconsistent`（回帰テスト） |

**論文側への反映事項**：v3 の結果が出たら §8.4 を次の趣旨に書き換える。

- 定理1は具体コストモデル上で、Pref_R 経由の探索アルゴリズムごと検証済み。
- 定理2は予想A・Bを仮定とする含意として証明し、独自の公理を使わない。
- 計算モデル（プリミティブのコストが入出力長以上の、二進列上のプログラム言語）が TM と多項式同値であることは形式化していない仮定として明記する。
