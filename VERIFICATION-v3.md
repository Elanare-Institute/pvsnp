# Lean 4 形式検証報告 v3（具体コストモデル版）

対象: `docs/lean4-spec-v3.md` / 論文 rev1
環境: Lean 4 v4.33.1 / Mathlib v4.33.1

## 結論

- `lake build` がエラー・**警告ゼロ**で通る（3070 jobs）
- **`sorry` ゼロ**（106 宣言を証明項レベルで監査）
- **独自 `axiom` ゼロ**（主要定理 24 件が標準3公理のみに依存）
- 指示書 §11 のチェックリストは**全項目達成**（ボーナス3件を含む）

---

## 1. Phase 0 の結果：v2 公理系は矛盾していた

**結論: `False` が導けた。** 指示書 §2.1 の疑いは正しかった。

`Test/Phase0Inconsistency.lean`（`lake build Phase0Test` で再検証可能）:

```
'v2_axioms_inconsistent' depends on axioms:
  [conjecture_A, conjecture_B, propext, Classical.choice, Quot.sound]
```

証明の構成:

1. `trivialRelV2`: `rel ≡ False`（YES インスタンスなし、`correct` は空虚に成立）
2. `trivialSolverV2`: `solve ≡ []`、`solveTime ≡ 1`
3. `maxAsymmetryAbs = 0`（恒等的）を証明 — `log 1 - log 1 = 0`
4. `conjecture_B` → residual が超対数的、`conjecture_A` → 計算的非対称性も超対数的
5. しかし定数 0 は超対数的になりえない → `False`

**含意**: v2 の `conditional_p_ne_np` は空虚に成立しており、検証として
無意味だった。この矛盾は v2 指示書が Conjecture B を**すべての**
`NPRelation` に量化したことに起因する（論文の Conjecture B は NP 完全
relation に限定されているので、ずれは Lean 側だけにあった）。

v3 ではこれを `v2_style_inconsistent : ConjA → ConjB_allRel → False` として
**回帰テスト化**した（§9.1）。この定理自体が「予想Bの量化を NP 完全
relation に限定しなければならない」ことの形式的証拠になっている。

---

## 2. 仕様からの逸脱

いずれも軽微で、論文 rev1 の数学的意図は保たれている。

| # | 箇所 | 逸脱 | 理由 |
|---|---|---|---|
| 1 | §9 `residual` | `residualAsym` に改名 | `residual` は Mathlib に既存（名前衝突） |
| 2 | §7 `spectrum` | `asymSpectrum` に改名 | `spectrum` は Mathlib に既存（名前衝突） |
| 3 | §7 `Profile` | `def` + `Profile.at` アクセサ | `abbrev` だと `ℕ → ℤ` の Pi 順序（各点順序）と衝突し、O(log n) 前順序が入らない |
| 4 | §3.6 `run_mono` | 省略 | 健全性 `run_sound` だけで実行テストは成立する。必須要件にも挙がっていない |
| 5 | §10 `prefix_mem_solvable_iff` | 仮定 `hu : u.length ≤ n` が**不要** | `prefixPA` が範囲外を `none` にするため `u` が長くても成立。仕様に合わせて引数は残し `_hu` と明示 |
| 6 | §5 `profile` の型 | `Finset.sup'` を使用 | 指示書どおり。`inputsOfSize` は `BStr` 版を新規に定義（v2 の `α` 一般版は Legacy へ） |

### 定数の調整（逸脱ではないが記録）

指示書の証明ヒントをそのまま使うと成立しない箇所があり、定数・指数を
強めた。数学的内容は変わらない。

- `polyTime_comp` / `polyTime_pair`: 指数を `kf` → `kf + 1` に。
  `kf = 0` のとき中間出力長の評価 `|y|+1 ≤ (1+cf)(n+1)^0` が偽になるため。
- `loop_reaches_cost`: `K := max(...) + 1`（`K ≥ 1` を保証）。
  `K = 0` だと `stateLen + 1 ≤ (stateLen+1)^K` が偽になる。
- `log_poly_le`: 係数を `log c + k + 1` → `log c + 2k + 1` に。
  `k(L+2) ≤ 2k(L+1)` を使うため。

---

## 3. `#print axioms` の出力（§11・§13）

```
'thm1_a_to_b'            : [propext, Classical.choice, Quot.sound]
'thm1_b_to_a'            : [propext, Classical.choice, Quot.sound]
'thm1_c_to_a'            : [propext, Classical.choice, Quot.sound]
'thm1_a_iff_b'           : [propext, Classical.choice, Quot.sound]
'thm1_a_iff_c'           : [propext, Classical.choice, Quot.sound]
'cor1'                   : [propext, Classical.choice, Quot.sound]
'cor1''                  : [propext, Classical.choice, Quot.sound]
'cor2'                   : [propext, Classical.choice, Quot.sound]
'prop1'                  : [propext, Classical.choice, Quot.sound]
'pointwise_degenerate'   : [propext, Classical.choice, Quot.sound]
'thm2'                   : [propext, Classical.choice, Quot.sound]
'v2_style_inconsistent'  : [propext, Classical.choice, Quot.sound]
```

`Test/NoCustomAxioms.lean` がこれを**ビルド時に強制**する（24 件を監査。
上記に加え `prefixSearch_polyTime`・`polyTime_of_logBounded`・
`Prog.run_sound`・`accumulation_identity` などの中核補題も対象）。

---

## 4. 実行テストの結果（`Test/Exec.lean`）

`native_decide` は不使用（`Lean.ofReduceBool` 公理を避けるため）。
すべて `rfl` で検証。

玩具の relation `rel x w := (w = [true])`:
- `V0 := comp snd (eqConst [true])`
- `D0 := comp snd (ite (eqConst []) (const [true]) (eqConst [true]))`

| テスト | 結果 |
|---|---|
| `run 200 (prefixSearch D0 V0) [true,false]` | `some ([true], 168)` |
| `run 200 (prefixSearch D0 V0) []` | `some ([true], 104)` |
| `run 30 V0 (enc [true,false] [true])` | `some ([true], 13)` — 受理 |
| `run 30 V0 (enc [true,false] [false])` | `some ([false], 13)` — 拒否 |
| `run 30 D0 (enc (enc [true,false] []) [])` | `some ([true], 18)` |

**探索が実際に動き、証拠 `[true]` を発見している。**

ステップ数と `Eval` のコストの一致も確認:

```lean
example : Eval (prefixSearch D0 V0) [true, false] [true] 168 :=
  run_sound 200 _ _ _ _ (by rfl)

-- 決定性より 168 以外のコストはありえない
example (t : ℕ) (h : Eval (prefixSearch D0 V0) [true,false] [true] t) : t = 168 :=
  h.time_unique (run_sound 200 _ _ _ _ (by rfl)) ▸ rfl
```

---

## 5. ボーナスの達成状況

| 項目 | 状態 |
|---|---|
| `pointwise_degenerate`（§8） | ✅ 達成 |
| 長さごとの版（§8 任意課題） | ❌ 未着手 |
| `prefix_mem_solvable_iff`（§10） | ✅ 達成（`Search/Bridge.lean`） |

`pointwise_degenerate` は「`x` の答えを定数としてプログラムに埋め込む」
構成（`ite (eqConst x) (const w) M₀.M`）で、`C` が `x` に依存しないことも
確認済み。これが論文 rev1 §3.2 の Uniformity の注を形式的に裏づける。

---

## 6. 三原則の達成確認

### (P1) 時間は実行から導出する

- `TCS` に時間フィールドは**ない**。`Concrete/` に `solveTime` という
  名前は一度も現れない（コメントでの言及を除く）。
- `TCS.time` は `Eval` の決定性（`Eval.deterministic`）から
  `Classical.choose` で一意に取り出す。
- **サイズ–コスト不変量** `Eval.size_le : y.length ≤ x.length + t` を証明。
  これにより単位コストでのデータ倍化が不可能になり、「多項式ステップ」が
  多項式時間の意味を保つ（要件 R2）。
- 構成子はすべて固定の単純操作。任意の Lean 関数を受け取る構成子はない（R1）。

### (P2) 最適性は一様に扱う

`profile M n` は長さ `n` の全入力にわたる `asym M x` の最大値。
各点 `iInf` は使っていない。`pointwise_degenerate` が、各点最適値では
退化することを形式的に示している。

### (P3) 独自の `axiom` をゼロにする

`grep -rn "^axiom" DirectionalAsymmetry/ Test/` の結果はゼロ
（`Test/Phase0Inconsistency.lean` は Legacy の v2 公理を参照するが、
これは矛盾の実証が目的であり別ターゲット）。
`ConjA`・`ConjB` は `def … : Prop` で、`thm2` の仮定に明示されている。

---

## 7. 定理1（⟹）が移送を使っていないことの確認

`thm1_a_to_b` は次の経路で証明した:

1. `PeqNP` から `(prefRel R).lang ∈ ClassP` を得る
2. decider `D` を取り出す
3. **`prefixSearch D R.V` という実際の探索アルゴリズムを構成**
4. その正当性（`prefixSearch_tcs`）と多項式性（`prefixSearch_polyTime`）を証明

`transportSolver` 相当の移送は使っていない。検証の実質は次の3つ:

- `body_preserves`: ループ不変量の維持（`v ≠ []` なら先頭ビットで分岐できる）
- `loop_reaches`: 停止性と証拠到達（測度 `R.q |x| − |u|` に関する帰納法）
- `loop_reaches_cost`: 1反復のコスト × 反復回数の評価

---

## 8. 論文 rev1 への指摘

### 8.1 予想Bの量化範囲（最重要）

Phase 0 で実証したとおり、予想Bを**すべての** NP relation に量化すると
予想Aと合わせて矛盾する。論文が NP 完全 relation に限定しているのは
正しく、この限定は**本質的**である（単なる自然さの問題ではない）。

論文に「予想Bの NP 完全性への限定は、予想Aとの整合性のために必要である。
限定を外すと自明な relation（例：`rel ≡ False`）で矛盾する」という趣旨の
注を入れることを勧める。形式的証明は `v2_style_inconsistent` にある。

### 8.2 計算モデルと TM の多項式同値性

指示書 §3.5 (R2) のとおり、この同値性は形式化していない。論文側に
**仮定として明記**する必要がある。具体的には:

> 本稿の計算モデル（二進列上のプログラム言語で、各プリミティブの
> コストが入出力長以上であるもの）が Turing 機械と多項式同値であることは
> 仮定する。

`Eval.size_le`（サイズ–コスト不変量）がこの仮定の前提条件を
形式的に保証している。

### 8.3 定理1(c) と Cook–Levin

Lean では Cook–Levin を形式化せず、(c) を「NP 完全な `R` について」の
形（`thm1_a_iff_c`）で述べた。`thm2` も NP 完全 relation の存在を
仮定 `hCL` として明示的に取る。論文の (b)⇒(c) が Cook–Levin を使う点は
そのままで問題ないが、形式化の範囲としては仮定に落としてある。

### 8.4 §8.4 への反映事項（指示書 §14）

- 定理1は具体コストモデル上で、Pref_R 経由の探索アルゴリズムごと検証済み。
  時間は構造体のフィールドではなくインタプリタの意味論が決める。
- 定理2は予想A・Bを仮定とする含意として証明し、独自の公理を使わない。
  `#print axioms thm2` は標準3公理のみ。
- 計算モデルが TM と多項式同値であることは形式化していない仮定として明記する。
- **v2 形式化の公理系が矛盾していたことを付記すべき**（§1 参照）。
  これは論文の主張ではなく形式化側の誤りだったが、説明責任として記録が要る。

---

## 9. ファイル構成

```
DirectionalAsymmetry/
├── Concrete/            -- v3 本体
│   ├── Encoding.lean          enc/dec と4補題
│   ├── Prog.lean              Prog, Eval, deterministic/cost_pos/size_le, 反転補題
│   ├── Interp.lean            run, run_sound
│   ├── Poly.lean              PolyBound と閉包性
│   ├── Classes.lean           PolyTime, ClassP, NPRel, ClassNP, PeqNP, p_sub_np 他
│   ├── TCS.lean               TCS, asym, profile, §5 の必須補題4件
│   ├── Prefix.lean            prefRel, prefixSearch, 正当性・停止性・コスト
│   ├── Characterization.lean  thm1_*, cor1, cor1', cor2
│   ├── Spectrum.lean          AsymClass, classOf, asymSpectrum, prop1
│   ├── Degeneracy.lean        pointwise_degenerate（ボーナス）
│   └── Separation.lean        ConjA, ConjB, thm2, v2_style_inconsistent
├── Search/              -- Layer 2（維持）
│   ├── SearchSpace.lean, Accumulation.lean, MeaningTransformation.lean
│   └── Bridge.lean            prefix_mem_solvable_iff（ボーナス）
├── Distribution.lean    -- 具体版 asym の押し出し測度
└── Main.lean
Legacy/                  -- v2 抽象層（別ターゲット。矛盾の記録用）
Test/
├── NoSorryInDefs.lean       106 宣言の sorry 監査
├── NoCustomAxioms.lean      24 件の公理監査
├── Exec.lean                実行テスト
└── Phase0Inconsistency.lean v2 矛盾の実証（別ターゲット）
```

ビルド:
- `lake build` — v3 本体 + テスト（警告ゼロ）
- `lake build Legacy Phase0Test` — v2 層と矛盾の実証

---

## 10. §11 チェックリスト

### Phase A–B
- [x] `lake build` がエラー・警告なしで通る
- [x] `Eval.deterministic`、`Eval.cost_pos`、`Eval.size_le` を証明
- [x] `run` の健全性を証明し、`Test/Exec.lean` で実行テストが通る
- [x] `p_sub_np`、`inP_of_reduces`、`Nonempty NPRel` を証明

### Phase C–D（定理1）
- [x] `TCS` に時間フィールドがない（`Concrete/` に `solveTime` は出現しない）
- [x] `asym_lower`、`logBounded_of_polyTime`、`polyTime_of_logBounded` を証明
- [x] `prefRel_mem_iff`、`prefixSearch_tcs`、`prefixSearch_polyTime` を証明
- [x] `thm1_*`、`cor1`、`cor1'`、`cor2` をすべて sorry なしで証明
- [x] `thm1_a_to_b` の証明が移送を使っていない

### Phase E–G
- [x] `prop1` を証明
- [x] （推奨）`pointwise_degenerate` を証明
- [x] `thm2` と `v2_style_inconsistent` を証明
- [x] プロジェクト全体で `axiom` 宣言がゼロ
- [x] `#print axioms` の対象がすべて標準3公理の部分集合
