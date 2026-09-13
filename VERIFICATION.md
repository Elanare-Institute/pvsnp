# Layer 1–3 検証レポート (指示書 v2)

対象: `docs/lean4-layer1-3-spec-v2.md`
参考資料: `docs/00_ideas (6).md`, `docs/03_structure (2).md`
実施日: 2026-09-13
環境: Lean 4 **v4.33.1** / Mathlib **v4.33.1**（前回から継続）

---

## 1. 結論

**Layer 1 / 2 / 3 の完了判定はすべて充足した。プロジェクト全体で `sorry` はゼロ。**

v2 §5 の sorry 優先順位 1〜13 のうち、**axiom として宣言すべき 11・12 を除く
全項目（1〜10, 13）を証明済み**。Layer 2 の `accumulation_identity`（優先度 10）も
型チェックのみならず証明まで完了している。

ただし v2 仕様のまま実装すると **Thm 1 (⟹) が反例を持つ**ことが判明し、
`TotalCandidateSolver` に 1 フィールドを追加して修正した（§3）。

> **重要**: 本形式化は **P≠NP を証明していない**。
> `conditional_p_ne_np` は Conjecture A/B を `axiom` として仮定した
> **条件付きの結果**であり、A/B 自体は未証明の予想である。
> `#print axioms` がこの依存関係を機械的に可視化している（§4）。

---

## 2. 完了判定チェックリスト（v2 §6）

### Layer 1

| | 項目 | 結果 |
|---|---|---|
| ✅ | `lake build` がエラーなしで通る | 終了コード 0、**warning もゼロ** |
| ✅ | `NPRelation`, `TotalCandidateSolver` の定義が sorry なし | `#print axioms` で確認 |
| ✅ | `directionalAsymmetry`, `maxAsymmetry` の定義が sorry なし | 同上 |
| ✅ | `ClassP`, `ClassNP` の定義が sorry なし | 同上 |
| ✅ | `p_eq_np_implies_log_bounded` のステートメントが型チェックを通る | **証明まで完了** |
| ✅ | `p_ne_np_iff_superlog_asymmetry` のステートメントが型チェックを通る | **証明まで完了** |
| ✅ | `p_sub_np` が sorry なしで証明される | 完了 |
| ✅ | 前回証明済みの 4 補題が新定義体系で再証明される | 完了（`Nat.log` 版も新規に証明） |

### Layer 2

| | 項目 | 結果 |
|---|---|---|
| ✅ | `PartialAssignment`, `solvableRegion`, `localAsymmetry` が sorry なし定義 | 完了 |
| ✅ | `accumulation_identity` のステートメントが型チェックを通る | **証明まで完了** |
| ✅ | `AsymmetryReducingTransform` の定義が sorry なし | 完了 |
| ✅ | `asymmetryDistribution` の定義が型チェックを通る | 完了（MeasureTheory 使用） |

### Layer 3

| | 項目 | 結果 |
|---|---|---|
| ✅ | `conjecture_A`, `conjecture_B` が axiom として宣言 | 完了 |
| ✅ | `conditional_p_ne_np` のステートメントが型チェックを通る | 完了 |
| ✅ | `conditional_p_ne_np` が axiom A+B を使って sorry なしで証明される | 完了 |
| ✅ | `#print axioms conditional_p_ne_np` が期待どおり | §4 参照 |

---

## 3. 仕様からの逸脱と理由

### 3.1 【重大】Thm 1 (⟹) は v2 仕様のままでは **反例を持つ**

**問題**: `NPRelation.verifyTimePoly` は、証拠長が `witnessBound n` 以下の
対 `(x, w)` に対してしか検証時間を縛らない（`inputsOfSizePairs` の定義）。
一方 `TotalCandidateSolver` は YES インスタンスでの正当性しか要求せず、
**NO インスタンスでの出力長は無制約**だった。

その結果、NO インスタンスで極端に長い出力を返す solver に対し
`R.verifyTime x (M.solve x)` が非有界になり、
非対称性が超対数的に**負へ**振れる。

**実際に Lean で構成・確認した反例**:

```lean
rel         := fun _ _ => False          -- YES インスタンス無し（correct は空虚に成立）
verifyTime  := fun _ w => 2 ^ w.length
witnessBound:= fun _ => 0
solve       := fun x => List.replicate (2 ^ x.length) true
solveTime   := fun _ => 1                -- 定数時間！
```

このとき `verifyTimePoly` は**空虚に成立**する（長さ 0 以下の証拠は `[]` のみ、
検証時間 1）が、`maxAsymmetry M n = -(2 ^ n)` となり
`maxAsymmetryAbs M n = 2 ^ n` は指数的。
solve 時間は定数（多項式）なのに `LogBoundedAsymmetry` が偽になる。

**対処**: `TotalCandidateSolver` に 1 フィールドを追加。

```lean
solve_short : ∀ x, (solve x).length ≤ R.witnessBound x.length
```

- **最小限**: 他の選択肢（`verifyTime` を全証拠で縛る／非対称性を 0 でクランプ／
  定理に仮定を足す）はいずれも意味論を壊すか、定理を空疎にする。
  特に「全証拠で `verifyTime` を多項式に」は、長さ 2^n の証拠を読むだけで
  2^n ステップかかるため**現実の verifier に対して偽**であり `NPRelation` を破壊する。
- **意味論的に自然**: `witnessBound` を超える長さの証拠は意味を持たないので、
  それより長い出力を返す solver は切り詰めればよく一般性を失わない。
- **既存の証明を壊さない**: `bruteForceSolver` は `R.witnessShort` から
  `solve_short` を証明でき、`Nonempty` インスタンスも維持される。
  `p_sub_np` / `log_bounded_implies_in_p` / `p_ne_np_iff_superlog_asymmetry` は無影響。

修正が適切に効いていることも確認済み: 上記反例の関係 `Rbad` 自体は
`NPRelation` として構成できる（`verifyTimePoly` を含む全フィールドを満たす）が、
指数長出力の solver を作ろうとすると `solve_short` のゴールが `False` になって
**構成できない**。過剰に強い制約ではなく、病的な solver のみを排除している。

### 3.2 `ClassP` に判定手続きを明示（利用者承認済み）

v2 §2.5 の `ClassP` は「多項式時間 TCS が存在する」とだけ述べるが、
TCS は YES インスタンスで証拠を出すだけで**判定はしない**（`correct` は YES 方向のみ）。
このままでは Thm 1 の ⟸ 方向 `log_bounded_implies_in_p` が
非対称性の仮定を一切使わず定義展開だけで自明に成立し、定理の内容が空疎になる。

**対処**: 「`M` を走らせた後 `R.rel x (M.solve x)` を検査すれば判定できる」
という判定条件 `(∀ x, M.decide x ↔ x ∈ L)` を `ClassP` の定義に加えた。
論文 §3.3 の iff に忠実な定式化。
なお `TotalCandidateSolver.decide_iff` により、この条件は実は常に成立する
（`language` の定義から逆向きが自動的に従う）ので、定義を強めてはいない。

### 3.3 Thm 1 (⟹) の relation 移送が必要

v2 §2.6 のステートメントは「**与えられた** `R`」に対する TCS を要求するが、
`ClassP` から取り出せるのは**別の** relation `R'` に対する TCS である
（`R'.language = R.language` なだけ）。仕様はこの点を見落としている。

**対処**: `transportSolver` を定義し、`solveTime` を引き継いだまま
`R` 上の TCS へ移送する（多項式性はそのまま保存）。
証拠は `Classical.choose` で取るため `noncomputable`。

### 3.4 `Int.log` → `Nat.log`

v2 §2.3 は `Int.log 2 (M.solveTime x)` と書くが、`Int.log` は
`Semifield` 上の関数で **ℕ に直接適用できない**（ℚ/ℝ へのキャストが要る）。
`Int.log_natCast : Int.log b (↑n) = Nat.log b n` が示すとおり
自然数上では両者は一致するので、無駄なキャストを避け `Nat.log 2` を使い
結果を ℤ にキャストする。意味は変わらない。

### 3.5 `maxAsymmetry` の非空性引数を削除

v2 §2.3 は `(hn : (inputsOfSize α n).Nonempty)` を明示引数に取るが、
それだと `fun n => maxAsymmetry M n` が `ℕ → ℤ` にならず `IsBigO` に渡せない
（v1 で判明した不具合と同型）。`[Nonempty α]` から内部で解決する。

### 3.6 `SearchPath.consecutive` の向きを固定

v2 §3.3 の `consecutive` は 2 方向の選言だったが、
論文 §6.4 は root → leaf の下向き経路を想定している。
選言のままだと Prop 2 が述べられないので向きを一つに固定した。

### 3.7 `structuralAsymmetry` の定義を補完

v2 §3.3 は `structuralAsymmetry` を**未定義のまま** `accumulation_identity` で
参照している。局所非対称性の総和として定義を与えた。

その結果 `accumulation_identity` は定義展開（`rfl`）で成立するので、
**論文の実質的な主張**（log の加法性: 和の形 = 比の積の対数）を
`structuralAsymmetry_eq_log_prod` として別に定式化し、証明した。

### 3.8 `AsymmetryReducingTransform.costPoly` の修正

v2 §3.5 の `costPoly : IsPolynomial (fun n => cost default)` は
束縛変数 `n` を使っておらず（`cost default` は `n` に依存しない）、
意図した多項式性を表していない。仕様も「簡略化」と注記している。

**対処**: コストの一様上界 `costBound` を構造体に持たせ、
多項式性は「サイズごとの変換の族」に対する述語
`PolyTimeTransformFamily` として定義した。

### 3.9 `residualStructuralAsymmetry` は `opaque`

v2 §7.6 が許容している抽象化の形を採り、
署名のみを与えて具体的構成は与えない（`opaque`）。
Conjecture A/B は中身に依存しない形で述べられている。

### 3.10 その他

- `Language` は `abbrev`（`def` だと `Set` の `Membership` が透けず `x ∈ L` が通らない）
- `witnessesUpTo` は「長さちょうど」ではなく**長さ以下**を走査
  （`witnessShort` が与えるのは上界なので、上界以下を全部見ないと worst-case にならない）
- `NPRelation.bruteForceSolver` は `Classical.dec` を使うため `noncomputable`
  （`x ∈ R.language` は一般に決定不能 ＝ NP たる所以）

---

## 4. `#print axioms` による検証

```
'conditional_p_ne_np' depends on axioms:
  [conjecture_A, conjecture_B, propext, Classical.choice, Quot.sound]

'p_eq_np_implies_log_bounded'     [propext, Classical.choice, Quot.sound]
'p_ne_np_iff_superlog_asymmetry'  [propext, Classical.choice, Quot.sound]
'p_sub_np'                        [propext, Classical.choice, Quot.sound]
'log_bounded_implies_in_p'        [propext, Classical.choice, Quot.sound]
'NPRelation' / 'TotalCandidateSolver' / 'directionalAsymmetry' /
'maxAsymmetry' / 'ClassP' / 'ClassNP' / 'localAsymmetry' /
'structuralAsymmetry' / 'accumulation_identity' /
'structuralAsymmetry_eq_log_prod' / 'asymmetryDistribution'
                                  [propext, Classical.choice, Quot.sound]
```

**`sorryAx` はどこにも現れない。**

Layer 3 の完了判定「`#print axioms conditional_p_ne_np` が
`[propext, Classical.choice, Quot.sound, conjecture_A, conjecture_B]` のみ」を
厳密に充足している。Layer 1 の定理が conjecture に依存していないことも重要で、
これにより「Thm 1 は無条件の結果、Thm 2 は条件付きの結果」という
論文の主張の構造が形式化に正しく反映されている。

### 回帰テスト

`Test/NoSorryInDefs.lean` が `lake build` の一部として自動実行され、
以下を機械的に検証する:

- **66 件**の宣言が `sorryAx` 非依存であること
- `conditional_p_ne_np` が `sorryAx` に依存せず、かつ
  `conjecture_A` と `conjecture_B` の**両方**に依存すること
  （conjecture を使わずに P≠NP が"証明"されたら失敗する）

前回同様、違反を故意に混入させてテストが失敗することを確認済み。

---

## 5. ファイル構成

v2 §1 の構成に準拠（`lakefile.toml` は前回から継続、Mathlib v4.33.1）。

```
DirectionalAsymmetry/
├── Basic.lean                  -- 多項式・Language・サイズ n の入力集合
├── TotalCandidateSolver.lean   -- Def 1–2: NPRelation, TCS
├── Asymmetry.lean              -- Def 3–3': A_M(x), A*(x), 各種評価
├── Complexity.lean             -- ClassP, ClassNP
├── Characterization.lean       -- Thm 1, p_sub_np
├── Distribution.lean           -- Def 4: 分布・統計量・スペクトル
├── SearchSpace.lean            -- Def 5–6: 可解領域, 局所非対称性
├── Accumulation.lean           -- Prop 2: 累積等式
├── MeaningTransformation.lean  -- Def 7: 意味変換
├── Separation.lean             -- Conj A/B (axiom), Thm 2
├── Auxiliary.lean              -- 補助補題（対数・多項式）
└── Main.lean                   -- 全体インポートと型確認
Test/
└── NoSorryInDefs.lean          -- sorry 監査の回帰テスト
```

v1 の `Correspondence.lean` は `Characterization.lean` に置き換えたため削除。

---

## 6. 残課題・注意点

### 6.1 `solveTime` と `solve` の乖離（形式化上の根本問題）

`solveTime` は `solve` と無関係な抽象フィールドである。
そのため「定数時間で指数長の出力を返す solver」のような
**計算的に無意味な対象**が型としては構成できてしまう（§3.1 の反例がまさにこれ）。

`solve_short` はその一つの症状を塞いだが、根本原因は残っている。
本枠組みに実際の計算内容を持たせるには、
`solveTime` を `solve` の実行から導出する計算モデル（TM 等）への接続が必要。
これは v2 §5.2 が Layer 2 以降としている課題と一致する。

なお `transportSolver` が `Classical.choose` を使うため、
Thm 1 (⟹) が与えるのは「多項式**時間限界**を持つ solver」であって
構成的な多項式時間アルゴリズムではない。上記の乖離に由来する。

### 6.2 Conjecture A/B は未証明

`axiom` として宣言してあるだけで、証明も反証もされていない。
論文 §8.4 が「Conj A/B の証明は P≠NP の直接証明と同程度に難しいかもしれない」
と正直に述べているとおり。

### 6.3 未着手（v2 が明示的に範囲外としたもの）

- Cook-Levin 定理（v2 §7.7 は Thm 2 に不要と結論、実際そのとおりだった）
- Five Worlds（論文 §5、解釈的内容のため形式化対象外）
- Barrier 分析（論文 §8、メタ分析のため形式化対象外）
- `optimalAsymmetry` の下方有界性（`iInf` が junk 値を返さない条件）

### 6.4 参考

追伸で言及された arXiv の P=NP 主張論文（Pedigree Polytope）は
計算量理論コミュニティで未検証のため、本検証では参照していない。
