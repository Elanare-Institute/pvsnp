# Lean 4 形式検証報告 v4：制限された設定での「橋」の定理化

対象: `docs/lean4-spec-v4.md` / 論文 rev1 §6.5「Where the Bridge Is a Theorem」
環境: Lean 4 v4.33.1 / Mathlib v4.33.1（v3 から継続）

## 結論

- `lake build` がエラー・**警告ゼロ**で通る（3079 jobs、v3 の結果を壊していない）
- **`sorry` ゼロ**（151 宣言を証明項レベルで監査。v3 の 106 件から +45）
- **独自 `axiom` ゼロ**（主要定理 32 件が標準3公理のみ。v3 の 24 件から +8）
- 指示書 §10 のチェックリストは**全項目達成**
- Haken の下界は**仮定** `HakenLB : Prop` として現れ、`axiom` にはなっていない

論文 §6.5 の主旨——一般の設定では予想のままの主張が、ソルバーの型を
限定した設定では**定理**になる——を、v3 の具体コストモデルの上で機械検証した。

---

## 1. §10 チェックリスト

- [x] `lake build` がエラー・警告なしで通る（v3 の検証結果を壊さない）
- [x] `tree_sound`、`gen_sound`（健全性、P3）
- [x] `tree_to_gen`、`minSize_le`
- [x] `decodeCNF_encodeCNF`、`encodeCNF_length_le`
- [x] `bridge_resolution`（定理3）を、木状・一般の両方で証明
- [x] `php_unsat`、`php_encode_length_le`、`php_encode_length_ge`
- [x] `hakenLB_tree`、`no_polytime_res_solver`（系3）
- [x] プロジェクト全体で `axiom` 宣言がゼロ
- [x] 主要定理の `#print axioms` が標準3公理の部分集合
- [x] `Test/RestrictedExec.lean`：`{{x},{¬x}}` の木状反証（サイズ 3）と `php n` の充足不能性

### 定理3が両方の体系で成り立つことについて

`bridge_resolution` は `ProofKind` に関して**多相**に証明した:

```lean
theorem bridge_resolution (S : ProofKind) (R : NPRel) (_hR : ImplementsSAT R)
    (M : ResSolver S R) : ∃ C : ℕ, ∀ x, ¬ Satisfiable (decodeCNF x) →
      (structAsym S (decodeCNF x) : ℤ) - C * (Nat.log 2 x.length + 1) ≤ asym M.tcs x
```

`S := .treeLike`（DPLL 型）と `S := .general`（節学習型）に具体化すれば
両方の主張が得られる。別々に証明する必要はなかった。

---

## 2. `#print axioms` の出力（§12-2）

```
'tree_sound'                              : [propext, Classical.choice, Quot.sound]
'gen_sound'                               : [propext, Classical.choice, Quot.sound]
'tree_to_gen'                             : [propext, Classical.choice, Quot.sound]
'minSize_le'                              : [propext, Classical.choice, Quot.sound]
'RestrictedEncoding.decodeCNF_encodeCNF'  : [propext, Classical.choice, Quot.sound]
'RestrictedEncoding.encodeCNF_length_le'  : [propext, Classical.choice, Quot.sound]
'bridge_resolution'                       : [propext, Classical.choice, Quot.sound]
'php_unsat'                               : [propext, Classical.choice, Quot.sound]
'php_encode_length_le'                    : [propext, Classical.choice, Quot.sound]
'php_encode_length_ge'                    : [propext, Classical.choice, Quot.sound]
'hakenLB_tree'                            : [propext, Classical.choice, Quot.sound]
'no_polytime_res_solver'                  : [propext, Classical.choice, Quot.sound]
```

v3 の結果も壊れていない（`thm1_a_iff_b`、`prop1`、`thm2` すべて標準3公理のみ）。

`Test/NoCustomAxioms.lean` が 32 件をビルド時に強制する。

---

## 3. 仕様からの逸脱

| # | 箇所 | 逸脱 | 理由 |
|---|---|---|---|
| 1 | §3.1 `resolvent` | `resStep` に改名 | `resolvent` は Mathlib に既存（名前衝突） |
| 2 | §3.1 `GenRefutation.valid` | `Fin` 添字版を維持しつつ、証明は `take` 基準の `GenValidOn` を経由 | 指示書は「書き方は自由」。添字の付け替えが `Fin` 版では極めて扱いにくく、`take i` に属するという同値な条件を使うと簡潔になる。両者の変換は `genValid_of_genValidOn` |
| 3 | §4 `decodeCNF` | 単射性 + 逆像（`Classical.choice`）で定義 | パーサを書く代わりに `encodeCNF_injective` を証明し、`decodeCNF` を逆像で定義。`decodeCNF_encodeCNF` は**本物の単射性から**出ており、空虚ではない |
| 4 | §4 `cnfSize` | 使わず、`encodeCNF_length_le` を節数・節の大きさ・変数番号の上界でパラメータ化 | `cnfSize` の定義は「自由」とされていた。鳩の巣原理で必要なのは `PolyBound` なので、そちらを直接示す方が素直（`php_encode_polyBound`） |
| 5 | §2 `Clause.eval` | `∃ l ∈ C, l.eval a = true`（`Prop`） | 指示書どおり。判定可能性は不要 |
| 6 | §7 `php` の穴 | 鳩 `0..n`（`n+1` 羽）、穴 `0..n-1`（`n` 個） | 指示書どおり。`n = 0` でも充足不能（(1) が空節になる） |

### v3 側への追加（破壊的変更なし）

v4 で必要になった補題を v3 のファイルに追加した。既存の宣言・証明は変更していない。

- `Concrete/Encoding.lean`: `enc_append_inj`（`enc` の self-delimiting 性）
- `Concrete/TCS.lean`: `vtime_log_bound`（検証時間の log 上界）
  - v3 では `asym_lower` と `polyTime_of_logBounded` の中に同じ評価が
    インラインで二度書かれていた。v4 の定理3でも要るので補題に切り出した。

---

## 4. 実行テストの結果（`Test/RestrictedExec.lean`）

`native_decide` は不使用（v3 と同じ）。

| テスト | 結果 |
|---|---|
| `resStep 0 {pos 0} {neg 0} = ∅` | `decide` で確認 |
| `tau0.size = 3` | `decide` で確認（公理2 + 導出1） |
| `F0_unsat : ¬ Satisfiable F0` | `tree_sound refut0` から |
| `tree_to_gen refut0` | 一般反証への変換が通る |
| `php 0`, `php 1`, `php 2` の充足不能性 | `php_unsat` から |
| `(php 1).length = 3` | `decide` で確認 |
| `encNat 5 = [true,false,true]` | 等式補題で展開して確認 |
| `decodeCNF (encodeCNF F0) = F0` | `decodeCNF_encodeCNF` から |

`encNat` は整礎再帰なので `decide` では簡約されない。等式補題
（`rw [encNat, ...]`）で展開した。これは逸脱ではなく、定義の性質。

---

## 5. 形式化していないもの（§12-3）

指示書が明示的に対象外としたもの、および `ResSolver` の定義に
織り込んだ仮定を、改めて列挙する。

1. **DPLL・CDCL の実行が resolution の反証を与えること**（Beame–Kautz–Sabharwal 2004）。
   `ResSolver` の `extract` フィールドが**設定の定義そのもの**であり、
   具体的な DPLL・CDCL の実装がこの類に入ることは形式化していない。
   論文 §8.4 にその旨を明記する必要がある。
2. **Haken (1985) の下界の証明**。`HakenLB : Prop` として定義し、
   系3の仮定として明示した。`axiom` にはしていない。
3. **Chvátal–Szemerédi (1988)**（定理4(ii)、ランダム3-CNF）。指示書で対象外。
4. **Buss (1987)**（Frege では鳩の巣原理が多項式サイズ、表現の軸）。指示書で対象外。
5. **SAT を実装する `NPRel` の存在**。`ImplementsSAT R` を仮定として受け取る
   形にした（指示書 §5 の方針）。したがって定理3・系3は
   「そのような `R` があれば」という条件つきの主張である。
   §9.1 のボーナス（CNF 評価器を `Prog` として書く）は未達成。
6. **resolution の完全性**。指示書が「証明しなくてよい」としたもの。
   DPLL の正当性に相当する作業量で、定理3・系3には不要。

---

## 6. ボーナスの達成状況（§9）

| # | 項目 | 状態 |
|---|---|---|
| 1 | SAT を実装する `NPRel` の構成 | ❌ 未達成 |
| 2 | resolution の完全性 | ❌ 未達成 |
| 3 | 予想との接続 | ✅ 達成 |
| 4 | 任意の TCS は証明体系を定める | ❌ 未達成 |

### ボーナス3（達成）

```lean
def ConjA_restricted (S : ProofKind) : Prop :=
  ∀ (R : NPRel), ImplementsSAT R → ∀ (M : ResSolver S R),
    ∃ C : ℕ, ∀ x, ¬ Satisfiable (decodeCNF x) →
      (structAsym S (decodeCNF x) : ℤ) - C * (Nat.log 2 x.length + 1) ≤ asym M.tcs x

theorem conjA_restricted_holds (S : ProofKind) : ConjA_restricted S :=
  fun R hR M => bridge_resolution S R hR M
```

v3 の `ConjA` は `residualAsym`（`opaque`、中身なし）を使うが、
制限された設定ではそれを `structAsym`（中身のある定義）に置き換えられ、
**予想が定理になる**。論文の「予想そのものにも設定の写像があり、
その既知の値は定理だ」の形式的な裏づけ。

### ボーナス1が未達成であることの含意

`ImplementsSAT R` を満たす `R` を構成していないので、
定理3・系3は「そのような `R` が存在すれば」という条件つきである。
論文の主張としては SAT が NP 関係であることは自明だが、
**形式化としては空虚でないことを確認していない**。
これは報告すべき限界であり、論文 §8.4 に明記すべきである。

なお、`ResSolver` の側は空虚ではない: `extract` は充足不能な入力に
ついてしか要求しないので、任意の `R`・任意の TCS に対して
「充足不能な入力が存在しない」場合には自明に満たされる。
逆に言えば、系3が意味を持つのは `ImplementsSAT R` かつ
`php n` の符号が実際に `R` の入力になる場合である。

---

## 7. 論文 §6.5 への指摘（§12-5）

### 7.1 `minSize` が 0 になる場合の扱い

定義9（`structAsym S F = log₂ (minSize S F)`）は、`F` に反証が
存在しないとき `sInf ∅ = 0` となり `structAsym = 0` になる。
論文では「充足不能な `F`」を暗黙に前提しているはずだが、
`minSize` を単独で解釈するときは注意が要る。

形式化では系3で `structAsym_php_ge` の仮定として
「反証が存在する」を明示的に要求し、それを `ResSolver.extract` から
供給することで回避した。論文側でも定義9に
「充足不能な `F` について」という限定を添えるのが安全である。

### 7.2 定理3の定数の依存関係

指示書は「定数 `C` は `M.c` と `R` の検証器・証拠長の多項式だけに依存し、
`x` には依存しない」と要求している。形式化ではこれを満たしている:

```
C := Cv + Nat.log 2 M.c + 1
```

ここで `Cv` は `vtime_log_bound R M.tcs` が与える定数で、`R.V_poly` と
`R.q_poly` だけから決まる。論文でもこの依存関係を明記すると、
定理3が「一様な」主張であることが伝わりやすい。

### 7.3 木状と一般の関係

`tree_to_gen`（木状 → 一般、サイズ非増加）を証明したので、
Haken の下界は一般 resolution について述べれば木状にも自動的に伝わる
（`hakenLB_tree`）。論文が定理4(i) を一般 resolution で述べているのは
正しく、DPLL 型（木状）には別途の引用が要らない。

逆向き（`minGenSize ≤ minTreeSize`）も証明したが、
これには「木状反証が存在する」という仮定が要る点に注意
（`minGenSize_le_minTreeSize`）。

---

## 8. ファイル構成

```
DirectionalAsymmetry/
├── Concrete/              -- v3（enc_append_inj と vtime_log_bound を追加）
├── Restricted/
│   ├── Prop.lean          -- 変数・リテラル・節・CNF・割り当て・充足
│   ├── Resolution.lean    -- 導出規則、木状/一般反証、健全性、tree_to_gen、minSize
│   ├── Encoding.lean      -- CNF の BStr 符号化、単射性、往復、長さの評価
│   ├── SATRel.lean        -- ImplementsSAT
│   ├── Solvers.lean       -- ResSolver（設定の定義）
│   ├── Bridge.lean        -- 定義9（structAsym）、定理3（bridge_resolution）
│   ├── Pigeonhole.lean    -- php、php_unsat、符号化長の評価
│   └── Corollary.lean     -- HakenLB、系3、ボーナス3
Test/
└── RestrictedExec.lean    -- 小さな反証と健全性のテスト
```

v4 の追加分は約 1540 行。

---

## 9. 論文 §8.4 への反映事項（§13）

v3 の記載に加えて、次を加える。

- **定理3と系3は、Haken の下界を仮定として置いたうえで、v3 と同じ具体
  コストモデルの上で機械検証済みで、独自の公理は使っていない。**
  `#print axioms no_polytime_res_solver` は
  `[propext, Classical.choice, Quot.sound]` のみ。
- **設定の定義（DPLL・CDCL の実行が resolution の反証を与えること）は、
  Beame–Kautz–Sabharwal (2004) に基づくもので、形式化はしていない。**
  Lean では `ResSolver.extract` フィールドとして仮定に置いている。
- **SAT を実装する `NPRel` の存在は形式化していない**（`ImplementsSAT` を
  仮定として受け取る）。したがって定理3・系3は条件つきの主張である。
- 制限された設定では予想A′が定理になること（`conjA_restricted_holds`）を
  形式的に確認した。これは論文の「予想そのものにも設定の写像があり、
  その既知の値は定理だ」に対応する。
