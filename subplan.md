# ヒルベルトの零点定理 形式化 - 軽量化版（Subplan）

## 概要
Tropical semiring 上の環合同を用いたヒルベルトの零点定理の形式化。原著論文の核心部分に焦点を当て、不要な一般化や応用は除外する。

## 参考文献
- 1-s2.0-S0001870815300815-main.pdf (原著論文)

## 現在の進捗（2026 年 10 月）
- **完了**: Section 2.4 まで（Corollary 2.12）
- **対象**: Tropical semirings, Ring congruences, Booleanization

## 軽量化の判断基準
**除外する項目**:
- Section 3: Tropical functions の詳細（congruence varieties は最小限のみ）
- Section 5.1.1, 5.1.2: Radical と limit pairs の詳細な構造論
- Section 6: 応用と一般化（完全には形式化しない）
- 数学的余り：証明の冗長な補題

**保持する項目**:
- Section 2: 環合同の基礎（最小限の定義のみ）
- Section 4: Weak tropical Nullstellensatz（核心部分のみ）
- Section 5.4: Strong tropical Nullstellensatz の最終結果のみ

## 形式化の範囲

### 必須セクション
1. **Section 2.1-2.4**: Semirings and congruences（基本定義のみ）
2. **Section 4.3**: The weak tropical Nullstellensatz（一般ケースのみ）
3. **Section 5.4**: The strong tropical Nullstellensatz（最終定理のみ）

### 省略セクション
- Section 2.5: Prime and maximal congruences（詳細な分類は不要）
- Section 3.1-3.3: Tropical functions（概念的な理解で十分）
- Section 5.1-5.3: Intermediate cases（最終結果への道筋のみ示す）
- Section 6: Applications（完全には形式化しない）

## タイムライン（2026 年 10 月 - 2027 年 3 月）

### 第 1 週：2026-10-05 〜 2026-10-11
**目標**: Section 2.1-2.2 の最小限実装
- Tropical semiring `𝕋` の定義（既存）
- Ring congruence の基本性質（既存を拡張）
- Quotient construction の簡易版

### 第 2 週：2026-10-12 〜 2026-10-18
**目標**: Section 2.3-2.4 の実装完了
- Generated congruence の定義
- Restriction/extension の基本性質
- Corollary 2.12 の証明（既存）

### 第 3 週：2026-10-19 〜 2026-10-25
**目標**: Section 4.1-4.2 の実装
- Principally generated case
- Flatness の簡易版

### 第 4 週：2026-10-26 〜 2026-11-01
**目標**: Section 4.3 の完了（Weak Nullstellensatz）
- General case proof
- Theorem: `E ≠ 𝕋 × 𝕋 ⇒ V(E) ≠ ∅`

### 第 5 週：2026-11-02 〜 2026-11-08
**目標**: Section 5.4 の準備
- Radical congruence の簡易定義
- Prime congruence の基本性質

### 第 6 週：2026-11-09 〜 2026-11-15
**目標**: Section 5.4 の完了（Strong Nullstellensatz）
- Main theorem: `√E = ⋂{F prime | E ⊆ F}`
- 簡易な証明経路

### 第 7 週：2026-11-16 〜 2026-11-22
**目標**: 統合と最適化
- 前後の整合性チェック
- Proof simplification
- Documentation

### 第 8 週：2026-11-23 〜 2026-11-29
**目標**: テストケース追加
- Minimal examples
- Counterexamples（必要最小限）

### 第 9 週：2026-11-30 〜 2026-12-06
**目標**: リファクタリング
- Code organization
- Naming consistency
- Remove redundancy

### 第 10 週：2026-12-07 〜 2026-12-13
**目標**: ドキュメント作成（最小限）
- Key definitions only
- Usage examples

### 第 11 週：2026-12-14 〜 2026-12-20
**目標**: Mathlib 整合性確認
- Version compatibility
- Import optimization

### 第 12 週：2026-12-21 〜 2026-12-27
**目標**: Weak Nullstellensatz の再検証
- Proof clarity improvement
- Alternative approaches（必要時）

### 第 13 週：2026-12-28 〜 2027-01-03
**目標**: Strong Nullstellensatz の再検証
- Proof simplification
- Edge case handling

### 第 14 週：2027-01-04 〜 2027-01-10
**目標**: 全体のレビュー
- Cross-reference check
- Consistency review

### 第 15 週：2027-01-11 〜 2027-01-17
**目標**: Final polish
- Documentation finalization
- Example gallery（最小限）

### 第 16 週：2027-01-18 〜 2027-01-24
**目標**: Performance optimization
- Proof speedup
- Tactic optimization

### 第 17 週：2027-01-25 〜 2027-01-31
**目標**: リソース解放と完了確認
- Cleanup
- Final verification

### 第 18 週：2027-02-01 〜 2027-02-07
**目標**: バグフィックス
- Regression testing
- Corner cases

### 第 19 週：2027-02-08 〜 2027-02-14
**目標**: 形式の統一
- Style guide application
- Final review

### 第 20 週：2027-02-15 〜 2027-02-21
**目標**: ドキュメント最終版
- Comprehensive but minimal docs
- Key examples only

### 第 21 週：2027-02-22 〜 2027-02-28
**目標**: Final verification
- Full proof check
- Consistency check

### 第 22 週：2027-03-01 〜 2027-03-07
**目標**: 完了と公開準備
- Final polish
- Release notes

## リソース配分
- **Lean コーディング**: 70%（効率化重視）
- **数学的検討**: 20%（核心部分のみ）
- **ドキュメント/テスト**: 10%（最小限）

## 依存関係
- Mathlib の RingTheory, Ideal モジュール
- Minimal tropical geometry setup

## 評価基準
- **核心性の達成**: Weak/Strong Nullstellensatz の完全な形式化
- **効率性**: 不要な一般化の排除
- **保守性**: Mathlib との整合性
- **可読性**: コードの明確さ

## リスク管理
1. **証明の簡略化による厳密性の低下**: 慎重なレビューで対応
2. **Mathlib の変更**: 定期的なバージョンチェック
3. **時間の制約**: パラレルタスクでの進行

## 成果物
- `Tropical/Semiring.lean`: Tropical semiring と congruence の定義
- `Tropical/WeakNullstellensatz.lean`: Weak theorem の証明
- `Tropical/StrongNullstellensatz.lean`: Strong theorem の証明
- `plan_sub.md`: このサブプラン

(End of file - total 95 lines)