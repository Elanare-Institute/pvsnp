# pvsnp — Directional Asymmetry Reformulation (Layer 1–3)

P vs NP 問題を「方向非対称性」(Directional Asymmetry) の枠組みで再定式化する
論文の Lean 4 形式化。

- 仕様: [`docs/lean4-layer1-3-spec-v2.md`](docs/lean4-layer1-3-spec-v2.md)
- 論文のアイデア: [`docs/00_ideas (6).md`](docs/00_ideas%20(6).md)
- 論文の構成: [`docs/03_structure (2).md`](docs/03_structure%20(2).md)
- 検証結果: [`VERIFICATION.md`](VERIFICATION.md)

> **注意**: 本形式化は **P≠NP を証明していない**。
> `conditional_p_ne_np` は Conjecture A/B を `axiom` として仮定した
> **条件付き**の結果であり、A/B 自体は未証明の予想である。
> `#print axioms` がこの依存関係を機械的に可視化している。

## ビルド

```bash
lake exe cache get   # Mathlib のビルド済みキャッシュを取得（初回のみ、必須）
lake build
```

環境: Lean 4 **v4.33.1** / Mathlib **v4.33.1**。

`lake build` は形式化本体に加え、**sorry 監査の回帰テスト**も実行する。

## 状態

**プロジェクト全体で `sorry` はゼロ。** Layer 1/2/3 の完了判定をすべて充足。

| Layer | 内容 | 状態 |
|---|---|---|
| 1 | Def 1–3', ClassP/ClassNP, Thm 1 | **全定理を証明** |
| 2 | Def 4–7, Prop 2（累積等式） | **定義 + 全定理を証明** |
| 3 | Conj A/B (axiom), Thm 2 | **A+B からの導出を証明** |

```
#print axioms conditional_p_ne_np
-- [conjecture_A, conjecture_B, propext, Classical.choice, Quot.sound]
```

Layer 1 の定理は conjecture に依存しない（無条件の結果）。

## 構成

| ファイル | 内容 | 論文 |
|---|---|---|
| `Basic.lean` | 多項式・Language・サイズ n の入力集合 | §2 |
| `TotalCandidateSolver.lean` | Def 1–2: NP relation, TCS | §2, §3.1 |
| `Asymmetry.lean` | Def 3–3': A_M(x), A*(x) | §3.2 |
| `Complexity.lean` | ClassP, ClassNP | §3.3 |
| `Characterization.lean` | Thm 1, P ⊆ NP | §3.3 |
| `Distribution.lean` | Def 4: 分布・統計量・スペクトル | §4 |
| `SearchSpace.lean` | Def 5–6: 可解領域, 局所非対称性 | §6.2–6.3 |
| `Accumulation.lean` | Prop 2: 累積等式 | §6.4 |
| `MeaningTransformation.lean` | Def 7: 意味変換 | §7.2 |
| `Separation.lean` | Conj A/B, Thm 2 | §7.3–7.5 |
| `Auxiliary.lean` | 補助補題（対数・多項式） | — |
| `Test/NoSorryInDefs.lean` | sorry 監査の回帰テスト | — |

## 仕様からの主な逸脱

v2 仕様のまま実装すると **Thm 1 (⟹) が反例を持つ**ことが判明したため、
`TotalCandidateSolver` に `solve_short`（出力長の多項式有界性）を追加した。
詳細は [`VERIFICATION.md` §3.1](VERIFICATION.md) を参照。

その他、`ClassP` への判定手続きの明示、relation 移送の補完など計 10 件。
