# Lean 4 形式検証指示書 v4：制限された設定での「橋」の定理化

## Directional Asymmetry — 論文 rev1 §6.5 準拠（v3 の上に積む）

環境：Lean 4 v4.33.1 / Mathlib v4.33.1（v3 から継続）

---

## 0. この版の目的

論文 §6.5「Where the Bridge Is a Theorem」を形式化する。一般の設定では予想（Conjecture A′、B）のままの主張が、ソルバーの型を限定した設定（DPLL 型・節学習型）では定理になることを、v3 の具体コストモデルの上で機械検証する。

論文 §6.5 の要素と、v4 での扱いは次のとおり。

| 論文 §6.5 | v4 での扱い |
|---|---|
| 定義9（証明体系に相対的な構造的非対称性） | 定義する |
| 定理3（制限された設定での A′） | 証明する |
| 定理4(i)（鳩の巣原理、Haken 1985） | **仮定**として置く（Hakenの証明は形式化しない） |
| 定理4(ii)（ランダム3-CNF、Chvátal–Szemerédi 1988） | 対象外 |
| 系3（DPLL型・節学習型は多項式時間の全候補ソルバーになれない） | 4(i) の仮定のもとで証明する |
| 表現の軸（Frege では多項式、Buss 1987） | 対象外 |
| 「証明が止まる場所」（Cook–Reckhow） | ボーナス（第9節） |

### 0.1 v4 の原則（v3 の三原則は継続）

- **(P1) 時間は実行から導出する**（v3 のまま。TCS に時間フィールドを持たせない）。
- **(P2) 独自 `axiom` をゼロにする**（v3 のまま）。Haken の下界は `def HakenLB : Prop` として定義し、系3の**仮定**として明示する。
- **(P3) 定義が空虚でないことを確かめる**：resolution の反証について**健全性**（反証があれば充足不能）を必ず証明する。これがないと、「反証」の定義を誤っても Theorem 3 は通ってしまう。

### 0.2 仕様の誤りを見つけたら

v1〜v3 と同様、この指示書にも誤りが残っている可能性がある。その場合は**論文 §6.5 の数学的意図を優先して**修正し、逸脱として報告すること。Mathlib の API 名は `#check` / `exact?` で確認すること。

---

## 1. 構成

```
DirectionalAsymmetry/
├── Concrete/              -- v3（変更しない。必要な補題の追加のみ可）
├── Restricted/
│   ├── Prop.lean          -- 変数・リテラル・節・CNF・割り当て・充足
│   ├── Resolution.lean    -- 導出規則、木状反証、一般反証、サイズ、健全性、木→一般の変換
│   ├── Encoding.lean      -- CNF と割り当ての BStr 符号化、長さの評価
│   ├── SATRel.lean        -- SAT を実装する NPRel の仕様
│   ├── Solvers.lean       -- 制限された設定（DPLL 型・節学習型）のソルバー類
│   ├── Bridge.lean        -- 定義9、定理3
│   ├── Pigeonhole.lean    -- 鳩の巣原理の式、充足不能性、サイズと符号化長
│   └── Corollary.lean     -- HakenLB、系3
└── Test/
    └── RestrictedExec.lean -- 小さな反証の具体例と健全性のテスト
```

---

## 2. Phase A：命題論理の基礎（Restricted/Prop.lean）

```lean
abbrev Var := ℕ

inductive Lit where
  | pos (v : Var)
  | neg (v : Var)
  deriving DecidableEq

def Lit.var : Lit → Var
def Lit.compl : Lit → Lit

abbrev Clause := Finset Lit
abbrev CNF := List Clause          -- 重複・順序は問わない

abbrev Assignment := Var → Bool

def Lit.eval (a : Assignment) : Lit → Bool
def Clause.eval (a : Assignment) (C : Clause) : Prop := ∃ l ∈ C, l.eval a = true
def CNF.eval (a : Assignment) (F : CNF) : Prop := ∀ C ∈ F, C.eval a
def Satisfiable (F : CNF) : Prop := ∃ a, F.eval a
```

- 変数は ℕ で番号づける。有限性が要る箇所では `F` に現れる変数の集合（`Finset Var`）を使う。
- `Satisfiable` の判定可能性は不要（すべて命題として扱う）。

---

## 3. Phase B：resolution（Restricted/Resolution.lean）

### 3.1 導出規則と二種類の反証

```lean
/-- x についての導出：C に pos x、D に neg x があるとき、両方からそれを除いて合わせる -/
def resolvent (x : Var) (C D : Clause) : Clause :=
  (C.erase (.pos x)) ∪ (D.erase (.neg x))

/-- 木状 resolution の導出木。根のラベルが導出された節 -/
inductive TreeDeriv (F : CNF) : Clause → Type where
  | ax  (C : Clause) (h : C ∈ F) : TreeDeriv F C
  | res (x : Var) {C D : Clause}
        (hC : Lit.pos x ∈ C) (hD : Lit.neg x ∈ D)
        (l : TreeDeriv F C) (r : TreeDeriv F D) :
        TreeDeriv F (resolvent x C D)

def TreeDeriv.size : TreeDeriv F C → ℕ        -- ノード数
abbrev TreeRefutation (F : CNF) := TreeDeriv F ∅

/-- 一般 resolution：節の列で、各節は公理か、それより前の二つの節の導出。最後は空節 -/
structure GenRefutation (F : CNF) where
  steps : List Clause
  valid : ...      -- 各 i について「公理」または「j, k < i から x で導出」
  ends  : steps.getLast? = some ∅
def GenRefutation.size (π : GenRefutation F) : ℕ := π.steps.length
```

`GenRefutation.valid` の書き方（添字の持ち方、`Fin` を使うか）は自由。

### 3.2 必須補題

- **健全性（P3）**：
  - `tree_sound : TreeRefutation F → ¬ Satisfiable F`
  - `gen_sound : GenRefutation F → ¬ Satisfiable F`
  - 方針：導出された節は、F を満たす任意の割り当てで真になる（導出に関する帰納法）。空節はどの割り当てでも偽。
- **木→一般の変換**：`tree_to_gen : (τ : TreeRefutation F) → ∃ π : GenRefutation F, π.size ≤ τ.size`
  - 木を後順で並べれば列になる。
- **最小サイズ**：
  ```lean
  noncomputable def minTreeSize (F : CNF) : ℕ := sInf { k | ∃ τ : TreeRefutation F, τ.size = k }
  noncomputable def minGenSize  (F : CNF) : ℕ := sInf { k | ∃ π : GenRefutation F, π.size = k }
  lemma minTreeSize_le (τ : TreeRefutation F) : minTreeSize F ≤ τ.size
  lemma minGenSize_le  (π : GenRefutation F)  : minGenSize F ≤ π.size
  ```
  - 完全性（充足不能ならいつも反証がある）は定理3・系3には不要なので、証明しなくてよい（ボーナス可）。

### 3.3 証明体系の種類をまとめる

```lean
inductive ProofKind where
  | treeLike
  | general

def Refutation : ProofKind → CNF → Type
  | .treeLike, F => TreeRefutation F
  | .general,  F => GenRefutation F

def Refutation.size : {S : ProofKind} → Refutation S F → ℕ
noncomputable def minSize : ProofKind → CNF → ℕ
lemma minSize_le (π : Refutation S F) : minSize S F ≤ π.size
```

---

## 4. Phase C：符号化（Restricted/Encoding.lean）

v3 の `BStr := List Bool` と対の符号化 `enc` / `dec` を使う。

```lean
def encodeCNF : CNF → BStr
def decodeCNF : BStr → CNF            -- 全域。不正な入力には既定値（空の CNF など）
def encodeAssign (vars : Finset Var) : Assignment → BStr
def decodeAssign : BStr → Assignment  -- 全域
```

必須補題：
- `decodeCNF_encodeCNF : decodeCNF (encodeCNF F) = F`
- `encodeCNF_length_le : (encodeCNF F).length ≤ cE * (cnfSize F + 1) ^ kE`
  - `cnfSize F` はリテラルの出現総数と、変数番号の桁数を合わせた量。定義は自由だが、第7節の鳩の巣原理の式で多項式になる必要がある。
- 変数番号は2進で符号化すること（単進だと長さが不必要に大きくなる）。

---

## 5. Phase D：SAT を実装する NP 関係（Restricted/SATRel.lean）

v3 の `NPRel` は検証器 `V : Prog` を要求する。CNF の評価器を DSL で書くのは大仕事なので、v4 では **SAT を実装する NPRel を仮定として受け取る**。

```lean
/-- R が SAT を実装していること -/
structure ImplementsSAT (R : NPRel) : Prop where
  rel_iff : ∀ x w, R.rel x w ↔ (decodeCNF x).eval (decodeAssign w)
```

- 定理3・系3は、「SAT を実装する任意の NPRel R について」という形で述べる。
- そのような R が存在すること（CNF 評価器を DSL の `Prog` として書き、多項式時間を示すこと）は**ボーナス**（第9節）。やらない場合は、報告でそう明記する。
- 注意：`ImplementsSAT R` から、`x` が充足不能なら `x ∉ R.lang` が出る（`rel_iff` から）。

---

## 6. Phase E：制限された設定と定理3（Restricted/Solvers.lean, Bridge.lean）

### 6.1 ソルバー類の定義

```lean
/-- 設定 S のソルバー：充足不能な入力での実行から、実行時間の定数倍以下のサイズの
    S-反証が取り出せる TCS -/
structure ResSolver (S : ProofKind) (R : NPRel) where
  tcs     : TCS R
  c       : ℕ
  extract : ∀ x, ¬ Satisfiable (decodeCNF x) →
              ∃ π : Refutation S (decodeCNF x), π.size ≤ c * time tcs x
```

- `S = treeLike` が DPLL 型、`S = general` が節学習型の設定。
- **この `extract` フィールドが設定の定義そのもの**である。具体的な DPLL・CDCL の実装がこの類に入ること（探索木が木状 resolution の反証になる、節学習が一般 resolution の反証を作る）は、論文では Beame–Kautz–Sabharwal（2004）を引いて述べている事実で、v4 では形式化しない。報告と論文 §8.4 でそう明記する。
- 分岐の選び方などの内部には一切制約を置かない。`tcs.M` は任意の `Prog` でよい。論文の「分岐の選び方には任意の計算を許す」に対応する。

### 6.2 定義9と定理3

```lean
/-- 論文の定義9：証明体系 S に相対的な構造的非対称性 -/
noncomputable def structAsym (S : ProofKind) (F : CNF) : ℕ := Nat.log 2 (minSize S F)

/-- 論文の定理3 -/
theorem bridge_resolution (S : ProofKind) (R : NPRel) (hR : ImplementsSAT R)
    (M : ResSolver S R) :
    ∃ C : ℕ, ∀ x, ¬ Satisfiable (decodeCNF x) →
      (structAsym S (decodeCNF x) : ℤ) - C * (Nat.log 2 x.length + 1) ≤ asym M.tcs x
```

証明の方針：
1. `extract` から π を取り、`minSize_le` と合わせて `minSize S F ≤ c * time M x`。
2. `Nat.log` の単調性と `Nat.log 2 (c * t) ≤ Nat.log 2 c + Nat.log 2 t + 1` で、`structAsym ≤ Nat.log 2 (time M x) + (定数)`。
3. v3 の `short` と `V_poly` から、`Nat.log 2 (vtime R x (out M x)) ≤ C' * (Nat.log 2 x.length + 1)`（v3 で `polyTime_of_logBounded` のために作った評価を再利用できるはず）。
4. `asym = Nat.log 2 time − Nat.log 2 vtime` に代入する。

- 定数 C は `M.c` と `R` の検証器・証拠長の多項式だけに依存し、`x` には依存しないこと。
- `minSize` が 0（空節が F の中にある場合など）のときも式が成り立つよう、`Nat.log` の端の扱いに注意する。

---

## 7. Phase F：鳩の巣原理の式（Restricted/Pigeonhole.lean）

```lean
/-- 変数 p(i, j)：鳩 i（0 ≤ i ≤ n）が穴 j（0 ≤ j < n）に入る -/
def phVar (n i j : ℕ) : Var                    -- 単射な番号づけ。例：i * n + j

def php (n : ℕ) : CNF :=
  -- (1) 各鳩はどこかの穴に入る：各 i について {pos p(i,0), …, pos p(i,n-1)}
  -- (2) 同じ穴に二羽は入らない：各 j と i < i' について {neg p(i,j), neg p(i',j)}
```

必須補題：
- `php_unsat : ¬ Satisfiable (php n)`
  - Mathlib の鳩の巣原理（`Fintype.exists_ne_map_eq_of_card_lt` など、名前は要確認）を使う。割り当てが (1) をすべて満たせば、各鳩に穴を一つ選ぶ関数が作れ、(2) と矛盾する。
- `php_size_le : cnfSize (php n) ≤ cP * (n + 1) ^ kP`
- `php_encode_length_le : (encodeCNF (php n)).length ≤ cL * (n + 1) ^ kL`
- `php_encode_length_ge : n ≤ (encodeCNF (php n)).length`（長さが n とともに無限に大きくなることの確認）

---

## 8. Phase G：Haken の仮定と系3（Restricted/Corollary.lean）

```lean
/-- Haken（1985）の下界：鳩の巣原理の式の一般 resolution 反証は指数サイズ。
    論文では文献の定理として引用。v4 では仮定として置く（axiom にはしない） -/
def HakenLB : Prop :=
  ∃ k N : ℕ, 0 < k ∧ ∀ n ≥ N, ∀ π : GenRefutation (php n), 2 ^ (n / k) ≤ π.size

/-- 木状 resolution でも同じ下界が出る（tree_to_gen から） -/
theorem hakenLB_tree (h : HakenLB) :
    ∃ k N : ℕ, 0 < k ∧ ∀ n ≥ N, ∀ τ : TreeRefutation (php n), 2 ^ (n / k) ≤ τ.size

/-- 論文の系3 -/
theorem no_polytime_res_solver (h : HakenLB) (S : ProofKind) (R : NPRel)
    (hR : ImplementsSAT R) (M : ResSolver S R) :
    ¬ LogBounded (profile M.tcs)
```

系3の証明の方針：
1. `x_n := encodeCNF (php n)`。`php_unsat` と `decodeCNF_encodeCNF` から、`x_n` は充足不能。
2. 定理3と Haken の仮定から、`asym M.tcs x_n ≥ n / k − 1 − C * (Nat.log 2 |x_n| + 1)`。
3. `|x_n| ≤ cL * (n+1)^kL` なので、`Nat.log 2 |x_n| = O(log n)`。
4. v3 の `profile` は長さ `|x_n|` の入力にわたる最大値なので、`profile M.tcs |x_n| ≥ asym M.tcs x_n`。
5. `LogBounded` なら `profile ≤ C'' * (Nat.log 2 |x_n| + 1) = O(log n)` だが、2 と 3 から profile は n / k − O(log n) 以上。n が大きいと矛盾する。

- `#print axioms no_polytime_res_solver` が `[propext, Classical.choice, Quot.sound]` の部分集合であること。Haken の下界は定理の仮定 `h` として現れ、axiom にはならない。

---

## 9. Phase H：ボーナス（任意）

1. **SAT を実装する NPRel の構成**：CNF 評価器を DSL の `Prog` として書き、`V_poly` と `ImplementsSAT` を示す。これができれば、系3の「任意の R について」が空虚でない（そういう R が存在する）ことまで形式化できる。
2. **resolution の完全性**：充足不能な CNF には必ず木状反証がある。`minSize` が意味のある値を取ることの確認になる。
3. **予想との接続**：v3 の `ConjA` を「`ResSolver` に制限し、`residualAsym` を `structAsym` に置き換えた版」として定義し、定理3からその版が成り立つことを示す。論文の「予想そのものにも設定の写像があり、その既知の値は定理だ」の形式的な裏づけになる。
4. **任意の TCS は証明体系を定める**（論文の「証明が止まる場所」の前半）：TCS の実行記録を、実行し直して確かめる検証器を作り、「充足不能な入力について、実行時間以下の長さの証明がある」ことを示す。

---

## 10. 成功基準（チェックリスト）

- [ ] `lake build` がエラー・警告なしで通る（v3 の検証結果を壊さない）
- [ ] `tree_sound`、`gen_sound`（健全性、P3）
- [ ] `tree_to_gen`、`minSize_le`
- [ ] `decodeCNF_encodeCNF`、`encodeCNF_length_le`
- [ ] `bridge_resolution`（定理3）を、木状・一般の両方で証明
- [ ] `php_unsat`、`php_encode_length_le`、`php_encode_length_ge`
- [ ] `hakenLB_tree`、`no_polytime_res_solver`（系3）
- [ ] プロジェクト全体で `axiom` 宣言がゼロ（v3 と同じ）
- [ ] 上記の主要定理の `#print axioms` が標準の3公理の部分集合
- [ ] `Test/RestrictedExec.lean`：`{ {x}, {¬x} }` の木状反証を手で作り、サイズが 3 であること、`tree_sound` から充足不能が出ることを確認する。`php 1` または `php 2` の充足不能性を `php_unsat` で確認する。

---

## 11. 既知の落とし穴

1. `Finset Lit` を使うので、`Lit` に `DecidableEq` が要る（`deriving DecidableEq`）。
2. `resolvent` は `erase` を使うので、C に pos x が複数回入る心配はない（Finset）。ただし `C` に `pos x` と `neg x` が両方ある場合の扱いに注意（定義はそのままでよいが、健全性の証明で場合分けが増える）。
3. `sInf` は空集合で 0 を返す。`minSize_le` は反証 π が存在する場合にしか使わないので問題ないが、`structAsym` を単独で解釈するときに注意。
4. `n / k` は自然数の切り捨て除算。系3の最後の大小比較では、`n / k` が `O(log n)` を上回ることを示す補題（たとえば `Nat.log 2 n` と `n / k` の比較）が要る。
5. v3 の `profile` は長さ n の全入力にわたる最大値。`profile M.tcs m ≥ asym M.tcs x`（`x.length = m`）の補題が v3 になければ追加する。
6. `native_decide` を使わない（v3 と同じ）。

---

## 12. 報告してほしいこと

1. 仕様からの逸脱と理由の一覧
2. 第10節の各項目の `#print axioms` 出力
3. 形式化していないもの（`ResSolver` の定義に入れた BKS の対応、Haken の証明、Chvátal–Szemerédi、Buss）の確認
4. ボーナスの達成状況
5. 論文 §6.5 の数学的内容に誤りや曖昧さを見つけた場合、その指摘

---

## 13. 論文との対応と、論文 §8.4 への反映事項

| 論文 §6.5 | Lean（v4） |
|---|---|
| DPLL 型・節学習型の設定 | `ResSolver treeLike R`、`ResSolver general R` |
| 定義9 | `structAsym` |
| 定理3 | `bridge_resolution` |
| 定理4(i)（Haken） | `HakenLB`（仮定） |
| 系3 | `no_polytime_res_solver`、`hakenLB_tree` |

**v4 の結果が出たら §8.4 に次の趣旨を加える。**

- 定理3と系3は、Haken の下界を仮定として置いたうえで、v3 と同じ具体コストモデルの上で機械検証済みで、独自の公理は使っていない。
- 設定の定義（DPLL・CDCL の実行が resolution の反証を与えること）は、Beame–Kautz–Sabharwal（2004）に基づくもので、形式化はしていない。
