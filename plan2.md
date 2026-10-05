# ヒルベルトの零点定理 形式化計画（Phase 2）

## 概要
現在の進捗（Section 2.4、Corollary 2.12 進行中）を基に、ヒルベルトの零点定理の完全な形式化に向けた研究計画。目標は 2027 年 3 月までの完了。

## 参考文献
- [PDF 1]: The tropical Nullstellensatz for congruences (原著論文)
- PDF-SUMMARY.txt: 論文内容要約

## 現在の進捗（2026 年 10 月）
- **完了**: Section 2.4 まで（Generation, restriction and extension of congruences）
- **進行中**: Corollary 2.12 の証明（有限生成合同関係の推移鎖表現）
- **対象セクション**: Section 2.5, 3, 4, 5

## タイムライン（2026 年 10 月 - 2027 年 3 月）

### 第 1 週：2026-10-05 〜 2026-10-11
**目標**: Corollary 2.12 の完了と Section 2.5 の開始
- **Corollary 2.12 の証明**: 有限生成合同関係の推移鎖表現
  - `swappedSumPair` と `swappedSumPairs` の定義と性質
  - `TransGen` と `swappedSumPairs` の同値性の証明
  - 有限生成元から S を構成する手法の完成
- **素合同（Prime congruence）の定義**: `(ac, bc) ∈ E ⇒ (a,b) ∈ E ∨ (c, 0_R) ∈ E`

### 第 2 週：2026-10-12 〜 2026-10-18
**目標**: Section 3.1 の完了（Congruences and congruence varieties）
- **Tropical polynomial ring `T[x]` の定義**
- **評価準同型（Evaluation homomorphism）**: `ev_a: T[x] → T`
- **合同多様体 `V(E)` の定義**: `V(E) = {a ∈ T^n | ∀(f,g)∈E, f(a)=g(a)}`
- **基本性質**: `V(E(S)) = S`, `E(V(E)) ⊇ E`
- Lemma: `V(⟨S⟩) = ⋂_{s∈S} V(s)`

### 第 3 週：2026-10-19 〜 2026-10-25
**目標**: Section 3.2 の完了（Polynomials that never agree）
- **定義**: `f, g` が `T^n` で交わらない場合の解析
- Lemma 3.2: `V(f,g) = ∅ ⇔ ∃a, f(a) ≠ g(a)`
- Maximal congruences との関係
- Example: Constant polynomials の挙動

### 第 4 週：2026-10-26 〜 2026-11-01
**目標**: Section 3.3 の完了（Polynomials that always agree）
- **Desaturated polynomials `f_dsat`**: 係数が最小の代表元
- **Saturated polynomials `f_sat`**: 係数が最大の代表元
- Lemma: `V(f) = V(g) ⇔ [f] = [g]`
- Theorem 1: `E(T^n) = ⋂{P | P is prime}` の確認

### 第 5 週：2026-11-02 〜 2026-11-08
**目標**: Section 4.1 の完了（The principally generated case）
- **単項生成された合同関係 `⟨(f,g)⟩` の解析**
- Weak Nullstellensatz の単項ケース証明
- Explicit zero construction: `V(f,g) ≠ ∅` の条件
- Lemma: Principal case の flatness criterion

### 第 6 週：2026-11-09 〜 2026-11-15
**目標**: Section 4.2 の完了（Flatness）
- **弱平坦（weakly flat）の定義**: `(h, εh) ∈ E ⇒ h の定数項 = 0_T`
- Flatness criterion for congruences
- Lemma: `E は弱平坦 ⇔ V(E) ≠ ∅`
- Application to weak Nullstellensatz

### 第 7 週：2026-11-16 〜 2026-11-22
**目標**: Section 4.3 の完了（The general case - Weak Nullstellensatz）
- **一般ケースの証明**: Inductive argument on number of generators
- **Theorem 2（弱トロピカル零点定理）**: `V(E) = ∅ ⇔ E は弱平坦ではない`
- Section 4 の統合と確認
- Example gallery: Weak Nullstellensatz の具体例

### 第 8 週：2026-11-23 〜 2026-11-29
**目標**: Section 5.1.1 の完了（The radical of a congruence）
- **プレラジカル `rad^-(E)` の定義**: `(1_T, ε) × ((f+g)^N + r, 0_T) × (f,g) ∈ E`
- Theorem 3: `V(E) = ∅ ⇔ (1_T, 0_T) ∈ rad^-(E)`
- Radical の基本性質：idempotence, monotonicity
- Connection to prime congruences

### 第 9 週：2026-11-30 〜 2026-12-06
**目標**: Section 5.1.2 の完了（Limit pairs）
- **極限ペア（Limit pairs）の定義と性質**
- ラジカル `rad(E)` の昇列極限から生成される推移的閉包 `ĤE`
- Lemma: Limit pairs と prime congruences の関係
- Characterization of `ĤE`

### 第 10 週：2026-12-07 〜 2026-12-13
**目標**: Section 5.2 の完了（The tropically vanishing case）
- **トロピカルに消滅する関数の定義**: `(p, 0_T) ∈ E(V(E))`
- Rabinowitsch trick の適用：変数を追加して逆数を作る
- Theorem 4: `(p, 0_T) ∈ E(V(E)) ⇔ (p, 0_T) ∈ rad^-(E)`
- Example: Vanishing polynomials の具体例

### 第 11 週：2026-12-14 〜 2026-12-20
**目標**: Section 5.3 の完了（The tropically constant case）
- **トロピカルに定数となる関数の定義**: `(p, 1_T) ∈ E(V(E))`
- Constant values on congruence varieties の解析
- Classification of tropically constant polynomials
- Lemma: Constant case と prime congruences の関係

### 第 12 週：2026-12-21 〜 2026-12-27
**目標**: Section 5.4 の完了（The general case - Strong Nullstellensatz）
- **一般ケースの統合証明**
- **Theorem 5（強トロピカル零点定理）**: `E(V(E)) = ĤE`
- Main theorem の確認と例の追加
- Section 5 の統合

### 第 13 週：2026-12-28 〜 2027-01-03
**目標**: Weak/Strong Nullstellensatz の相互関係の確認
- Weak と Strong theorem の関係性の確認
- `E ⊆ E(V(E))` の証明（包含関係）
- Equivalence of formulations
- Cross-references between sections

### 第 14 週：2027-01-04 〜 2027-01-10
**目標**: リファクタリングと最適化
- Code organization: Module structure の見直し
- Proof simplification: 冗長な証明の削減
- Naming consistency: 命名規則の統一
- Documentation improvement

### 第 15 週：2027-01-11 〜 2027-01-17
**目標**: テストケースと例の追加
- **Concrete examples**: Section 3, 4, 5 全体に
- Counterexamples: Where applicable
- Test suite for key lemmas and theorems
- Example gallery の作成

### 第 16 週：2027-01-18 〜 2027-01-24
**目標**: ドキュメント作成
- **Comprehensive documentation**: All definitions and theorems
- **Usage examples**: How to use the formalized theory
- **Mathematical context**: Connections to classical algebraic geometry
- README.md の更新

### 第 17 週：2027-01-25 〜 2027-01-31
**目標**: Mathlib 整合性確認とバグフィックス
- Version compatibility check
- Import optimization
- Regression testing
- Corner case handling

### 第 18 週：2027-02-01 〜 2027-02-07
**目標**: Proof verification
- Full proof check: All lemmas and theorems
- Alternative proofs（必要時）
- Proof clarity improvement
- Tactic optimization

### 第 19 週：2027-02-08 〜 2027-02-14
**目標**: 形式の統一と最適化
- Style guide application
- Code cleanup: Remove redundancy
- Performance optimization
- Consistency review

### 第 20 週：2027-02-15 〜 2027-02-21
**目標**: Final polish - Part 1
- Documentation finalization
- Example gallery completion
- Cross-reference check
- Minor fixes

### 第 21 週：2027-02-22 〜 2027-02-28
**目標**: Final polish - Part 2
- Full proof verification
- Consistency check across all sections
- Final documentation review
- Release preparation

### 第 22 週：2027-03-01 〜 2027-03-07
**目標**: 完了と公開準備
- **Final verification**: Complete proof check
- **Release notes**: Summary of formalization
- **Publication preparation**: GitHub release, documentation
- Project completion

## セクション別タスクの依存関係

```
Section 2.5 (Prime/Maximal) ← Section 2.4 (Generation/Restriction)
                              ↓
Section 3.1 (Congruence varieties) ← Section 2.1-2.4
      ↓                    ↓
Section 3.2-3.3 (Polynomials)    ↓
      ↓                         ↓
Section 4.1-4.3 (Weak N.S.)     ↓
                              Section 5.1 (Radical/Limit pairs)
                                      ↓
Section 5.2-5.3 (Vanishing/Constant cases)
                                      ↓
Section 5.4 (Strong N.S.) ← All previous sections
```

## リソース配分

| タスク | 割合 | 内容 |
|--------|------|------|
| Lean コーディング | 60% | 定義、証明、例の形式化 |
| 数学的検討 | 25% | 定理の理解、証明戦略、一般化 |
| ドキュメント/テスト | 15% | 文書化、テストケース、例 |

## 成果物

- `Tropical/Semiring.lean`: Section 2.1-2.5（既存 + 追加）
- `Tropical/Varieties.lean`: Section 3（Congruence varieties）
- `Tropical/WeakNullstellensatz.lean`: Section 4（弱零点定理）
- `Tropical/Radical.lean`: Section 5.1-5.3（ラジカルと intermediate cases）
- `Tropical/StrongNullstellensatz.lean`: Section 5.4（強零点定理）
- `examples/*.lean`: Concrete examples and counterexamples
- `plan2.md`: この研究計画

## 評価基準

- **完全性**: PDF-LIST.txt に記載されたすべての主要セクションの形式化
- **正確性**: すべての主張が完全に証明されている
- **一貫性**: 既存の plan.md と subplan.md との整合性
- **可読性**: コードとドキュメントの明確さ
- **保守性**: Mathlib との整合性

## リスク管理

1. **証明の難易度**: 段階的なアプローチでリスク分散（Section 4→5 の順序）
2. **Mathlib の変更**: 定期的なバージョンチェックとテスト
3. **時間の制約**: パラレルタスクでの進行、優先順位付け
4. **複雑さの管理**: Section 5 の limit pairs は特に複雑なので十分な時間配分

## 参照

- PDF-LIST.txt: 形式化対象セクション一覧
- PDF-SUMMARY.txt: 論文内容要約（Section 別）
- plan.md: 全体の計画（Phase 1）
- subplan.md: 軽量化版の計画（参考用）
