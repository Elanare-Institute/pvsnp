# pvsnp — Computational Directional Asymmetry（Lean 4 形式化 v3）

論文 "Computational Directional Asymmetry: Dissolving the Classical Question Behind P vs NP"（Franny Philos Sophia, rev1）の Lean 4 形式化。

- English version of this README: [`README.md`](README.md)
- 論文: Zenodo（新バージョンの DOI をここに記入）
- 仕様: [`docs/lean4-spec-v3.md`](docs/lean4-spec-v3.md)、[`docs/lean4-spec-v4.md`](docs/lean4-spec-v4.md)
- 検証結果: [`VERIFICATION-v3.md`](VERIFICATION-v3.md)、[`VERIFICATION-v4.md`](VERIFICATION-v4.md)（v2 の記録は [`VERIFICATION.md`](VERIFICATION.md)）

> **注意**: 本形式化は P≠NP を証明していない。定理2は、予想A・Bと「NP 完全な relation が存在すること」を**仮定とする含意**として証明している。予想A・B自体は未証明であり、プロジェクトは独自の `axiom` を一切宣言していない。

## v2 からの訂正（重要）

v2（旧 README および論文プレプリント v1 に対応）には、次の3つの問題があった。

1. **公理系の矛盾。** v2 は予想A・Bを `axiom` として宣言し、予想Bを NP 完全な relation ではなく**すべての** NP relation に量化していた。この公理系は矛盾しており、自明な relation（言語が空で、定数を出力する solver）から `False` が導ける。これは Lean で実証済みである。したがって v2 の `conditional_p_ne_np` は空虚に成立していた。旧 README の「`#print axioms conditional_p_ne_np` が conjecture_A と conjecture_B だけに依存する」という記述は検証として意味を持たないため、撤回する。
2. **時間が抽象フィールド。** solver の時間が実行と無関係な数値だったため、relation 間の solver の移送がコストゼロで行えた。そのため定理1の探索構成を検証していなかった。
3. **各点最適値の退化。** `optimalAsymmetry` がインスタンスごとの下限として定義されており、答えを埋め込んだ solver によって常に O(log n) になっていた。

v3 はこの3点をすべて解消している。予想Bを NP 完全な relation に限定しなければならないことは、回帰テスト `v2_style_inconsistent : ConjA → ConjB_allRel → False` として形式的に証明してある。

## 計算モデル

アルゴリズムは、二進列上の小さなプログラム言語（対、先頭・末尾の操作、条件分岐、ループ）の**構文**として表す。実行時間は、大ステップのコスト意味論 `Eval` から導出する。時間を構造体のフィールドとして持つことはない。各プリミティブのコストは入力長と出力長以上なので、データが実行時間より速く増えることはない。

探索アルゴリズムは実際に動く。

```lean
run 200 (prefixSearch D0 V0) [true, false] = some ([true], 168)   -- rfl で検証
```

**形式化していない仮定**: このプログラム言語がチューリングマシンと多項式同値であること。これは計算量理論の標準的な不変性の仮定である（論文 §8.4）。

## ビルド

```bash
lake exe cache get   # Mathlib のビルド済みキャッシュを取得（初回のみ、必須）
lake build
```

環境: Lean 4 **v4.33.1** / Mathlib **v4.33.1**。

`lake build` は形式化本体に加えて、sorry と公理の監査、および実行テストも実行する。

## 状態

- `lake build`: エラー・警告ゼロ
- `sorry`: ゼロ（151 宣言を証明項レベルで監査）
- 独自の `axiom`: ゼロ（主要定理 32 件が `propext`, `Classical.choice`, `Quot.sound` のみに依存）

```
#print axioms thm2
-- [propext, Classical.choice, Quot.sound]
```

## 主要な結果（論文 rev1 との対応）

| 論文 rev1 | 内容 | Lean |
|---|---|---|
| §3.2 | 普遍下界 g_M(n) ≥ −O(log n) | `asym_lower` |
| §3.2 | インスタンスごとの最適値の退化 | `pointwise_degenerate` |
| §3.3 | prefix 言語 Pref_R とそれを使う探索アルゴリズム | `prefRel`, `prefixSearch_tcs`, `prefixSearch_polyTime` |
| §3.3 | 定理1（(a)⇔(b)、NP 完全な R について (a)⇔(c)） | `thm1_a_iff_b`, `thm1_a_iff_c` |
| §3.3 | 系1・系2 | `cor1`, `cor1'`, `cor2` |
| §3.3 | SAT 型 relation の Pref と可解領域の一致 | `prefix_mem_solvable_iff` |
| §4.3 | 命題1（P = NP ⇔ Σ_NP = {[0]}） | `prop1`（スペクトルは `asymSpectrum`） |
| §5.4 | 命題2（累積等式） | `accumulation_identity` |
| §6.3 | 予想Bの NP 完全への限定が本質的であること | `v2_style_inconsistent` |
| §6.4 | 定理2（予想A・B ⇒ P ≠ NP） | `thm2`（残差非対称性は opaque な `residualAsym`） |
| §6.5 | 定義9（証明体系に相対的な構造的非対称性） | `structAsym` |
| §6.5 | 定理3（制限された設定では「橋」が定理になる） | `bridge_resolution`（`ProofKind` に多相なので DPLL 型・節学習型の両方を覆う） |
| §6.5 | 定理4(i)（Haken 1985） | `HakenLB`（公理ではなく仮定） |
| §6.5 | 系3（DPLL型・節学習型は多項式時間の全候補ソルバーになれない） | `no_polytime_res_solver` |
| §6.5 | 制限された設定では予想A′自体が定理になる | `conjA_restricted_holds`（`ConjA_restricted` は `ConjA` の opaque な `residualAsym` を `structAsym` に置き換えた版） |
| §6.5 | resolution 反証の健全性（定義が空虚でないことの確認） | `tree_sound`, `gen_sound` |

## 形式化していないもの

- プログラム言語とチューリングマシンの多項式同値（上記の仮定）
- Cook–Levin の定理（NP 完全な relation の存在は `thm2` の仮定として明示）
- 長さごとの最適値の退化（インスタンスごとの版のみ形式化）
- 予想A・B（定理2の仮定であり、公理ではない）
- DPLL・CDCL の実行が resolution の反証を与えること（Beame–Kautz–Sabharwal 2004）。
  これは `ResSolver` の `extract` フィールドが仮定しているもので、**制限された設定の定義そのもの**である
- Haken の下界の証明（`HakenLB` は系3の仮定）
- SAT を実装する NP relation の存在（`ImplementsSAT` は仮定）。したがって定理3・系3は条件つきの主張である
- resolution の完全性、Chvátal–Szemerédi (1988)、Buss (1987)

## 構成

```
DirectionalAsymmetry/
├── Concrete/
│   ├── Encoding.lean          -- 二進列と対の符号化
│   ├── Prog.lean              -- プログラム言語とコスト意味論 Eval
│   ├── Interp.lean            -- 燃料付きインタプリタ run と健全性
│   ├── Poly.lean              -- 多項式上界と閉包性
│   ├── Classes.lean           -- PolyTime, ClassP, NPRel, ClassNP, PeqNP, IsNPComplete
│   ├── TCS.lean               -- 全候補ソルバー、非対称性、プロファイル、普遍下界
│   ├── Prefix.lean            -- prefix 言語と探索アルゴリズム
│   ├── Characterization.lean  -- 定理1、系1、系2
│   ├── Spectrum.lean          -- 非対称性クラス、スペクトル、命題1
│   ├── Degeneracy.lean        -- インスタンスごとの最適値の退化
│   └── Separation.lean        -- 予想A・B（Prop）、定理2、回帰テスト
├── Restricted/                -- 論文 §6.5: 橋が定理になる場所
│   ├── Prop.lean              -- 命題論理: リテラル・節・CNF・充足
│   ├── Resolution.lean        -- resolution、木状/一般反証、健全性
│   ├── Encoding.lean          -- CNF の二進列符号化、単射性、長さの評価
│   ├── SATRel.lean            -- ImplementsSAT
│   ├── Solvers.lean           -- ResSolver: 制限された設定
│   ├── Bridge.lean            -- 定義9と定理3
│   ├── Pigeonhole.lean        -- 鳩の巣原理の式と充足不能性
│   └── Corollary.lean         -- HakenLB と系3
├── Search/                    -- 可解領域、局所非対称性、累積等式、構造開示変換、
│                                 ブリッジ補題（Bridge.lean）
├── Distribution.lean          -- 非対称性の分布
└── Main.lean
Legacy/                        -- v2 の抽象層（別ターゲット。矛盾の記録として残してある。
                                  デフォルトのビルド対象には含まれない）
Test/
├── NoSorryInDefs.lean         -- sorry 監査
├── NoCustomAxioms.lean        -- 主要定理の公理監査
├── Exec.lean                  -- 実行テスト
├── RestrictedExec.lean        -- §6.5 層の実行テスト
└── Phase0Inconsistency.lean   -- v2 の矛盾の実証（別ターゲット）
```

v2 の矛盾を再現するには:

```bash
lake build Legacy Phase0Test
# 'v2_axioms_inconsistent' depends on axioms:
#   [conjecture_A, conjecture_B, propext, Classical.choice, Quot.sound]
```

## 仕様からの逸脱

v3 では軽微な逸脱が6件と証明ヒントを強めた箇所が3件、v4 ではさらに6件（多くは Mathlib との名前衝突と、復号をパーサではなく単射な符号化の逆像として定義したこと）。いずれも数学的内容は変えていない。詳細は [`VERIFICATION-v3.md`](VERIFICATION-v3.md) と [`VERIFICATION-v4.md`](VERIFICATION-v4.md) を参照。
