# ヒルベルトの零点定理 形式化計画

## 概要
ヒルベルトの零点定理（Hilbert's Nullstellensatz）は、代数閉体上の代数集合とイデアルの対応を記述する。本計画では、Tropical geometry の文脈における環合同（Ring Congruences）を用いた零点定理の形式化を目指す。

## 参考文献
- 1-s2.0-S0001870815300815-main.pdf (原著論文)

## 現在の進捗（2026 年 10 月）
- **完了**: Section 2.4 まで（Generation, restriction and extension of congruences、Corollary 2.12）
- **対象**: Tropical semirings, Ring congruences, Booleanization, Maximal congruences

## 形式化の段階

### 第 1 段階：環合同の基礎理論（完了）
- **目標**: Tropical 半環上の環合同の定義と基本性質
- **サブタスク**:
  - [x] `𝔹` (Boolean semiring) と `𝕋` (Tropical semiring) の定義
  - [x] `RingCon`（環合同）の基礎性質
  - [x] `twistProd` およびその保存性 (`twistprod_con`)
  - [x] `booleanization` 準同型の定義と全射性の証明
  - [x] `RingConSimple` の定義と `𝔹` への適用
  - [x] 極大合同関係の証明 (`ker_isMaximal'`, `pr`)
  - [x] Corollary 2.12（有限個の transitive chain）

### 第 2 段階：環合同の生成と商構造
- **目標**: 環合同の生成系と商半環の構築
- **サブタスク**:
  - Relation generation from generating set
  - Transitive closure of relations
  - Quotient semiring construction
  - Congruence homomorphism theorems (1st, 2nd, 3rd isomorphism)

### 第 3 段階：Tropical functions と congruence varieties
- **目標**: Tropical 多項式とそれらが定める合同関係
- **サブタスク**:
  - Tropical polynomials definition
  - Congruence varieties `V(E)` の定義
  - Polynomials that never agree (Lemma 3.2)
  - Polynomials that always agree (Lemma 3.3)
  - Desaturated vs Saturated polynomials

### 第 4 段階：弱トロピカル零点定理
- **目標**: 主生成された場合と一般化
- **サブタスク**:
  - Principally generated case（単項理想の場合）
  - Flatness argument
  - General case proof
  - Theorem: `E ≠ 𝕋 × 𝕋 ⇒ V(E) ≠ ∅`

### 第 5 段階：強トロピカル零点定理
- **目標**: Radical congruence と limit pairs
- **サブタスク**:
  - Radical of a congruence definition
  - Limit pairs concept
  - Tropically vanishing case
  - Tropically constant case
  - General case: `√E = ⋂{F | F is prime, E ⊆ F}`

### 第 6 段階：応用と一般化
- **目標**: より一般的な状況への拡張
- **サブタスク**:
  - Elimination theory in tropical setting
  - Tropical varieties and their properties
  - Connection to classical Nullstellensatz
  - Computational aspects

## タイムライン（2026 年 10 月 - 2027 年 3 月）

### 第 1 週：2026-10-05 〜 2026-10-11
**目標**: Section 2.5 の完了（Prime and maximal congruences）
- Sub-maximal congruences の定義と性質
- Maximal congruence の一意性証明
- `RingConSimple` の一般化

### 第 2 週：2026-10-12 〜 2026-10-18
**目標**: Section 2.3 の完了（Quotient semirings）
- Quotient semiring construction
- Canonical projection homomorphism
- Universal property of quotient

### 第 3 週：2026-10-19 〜 2026-10-25
**目標**: Section 2.4 の完了（Generation, restriction, extension）
- Generated congruence `⟨S⟩`
- Restriction to subsemiring
- Extension to oversemiring
- Lemma 2.11 の証明

### 第 4 週：2026-10-26 〜 2026-11-01
**目標**: Section 3.1 の完了（Congruences and congruence varieties）
- Tropical polynomial ring definition
- Evaluation homomorphism
- Congruence variety `V(E)` の定義
- Basic properties of `V(E)`

### 第 5 週：2026-11-02 〜 2026-11-08
**目標**: Section 3.2 の完了（Polynomials that never agree）
- Definition: polynomials f, g with `V(f-g) = ∅`
- Characterization of such pairs
- Connection to maximal congruences

### 第 6 週：2026-11-09 〜 2026-11-15
**目標**: Section 3.3 の完了（Polynomials that always agree）
- Desaturated polynomials
- Saturated polynomials
- Criterion for `V(f) = V(g)`

### 第 7 週：2026-11-16 〜 2026-11-22
**目標**: Section 4.1 の完了（The principally generated case）
- Weak Nullstellensatz for principal congruences
- `E = ⟨(a,b)⟩ ⇒ V(E) ≠ ∅`
- Explicit construction of zeros

### 第 8 週：2026-11-23 〜 2026-11-29
**目標**: Section 4.2 の完了（Flatness）
- Flatness over tropical semiring
- Flatness criterion for congruences
- Application to weak Nullstellensatz

### 第 9 週：2026-11-30 〜 2026-12-06
**目標**: Section 4.3 の完了（The general case）
- General weak Nullstellensatz proof
- Inductive argument on number of generators
- Completion of Section 4

### 第 10 週：2026-12-07 〜 2026-12-13
**目標**: Section 5.1 の完了（Radical and limit pairs）
- Radical of a congruence `√E`
- Limit pair definition
- Properties of radical

### 第 11 週：2026-12-14 〜 2026-12-20
**目標**: Section 5.1 の完了（Limit pairs continued）
- Characterization of limit pairs
- Connection to prime congruences
- Uniqueness results

### 第 12 週：2026-12-21 〜 2026-12-27
**目標**: Section 5.2 の完了（The tropically vanishing case）
- Definition: `f tropically vanishes on V(E)`
- Equivalence with `f ∈ √E`
- Basic examples

### 第 13 週：2026-12-28 〜 2027-01-03
**目標**: Section 5.3 の完了（The tropically constant case）
- Tropically constant polynomials
- Constant values on congruence varieties
- Classification

### 第 14 週：2027-01-04 〜 2027-01-10
**目標**: Section 5.4 の完了（The general case）
- Main theorem: Strong tropical Nullstellensatz
- `√E = ⋂{F prime | E ⊆ F}`
- Equivalence with classical version

### 第 15 週：2027-01-11 〜 2027-01-17
**目標**: Section 6 の開始（Applications）
- Elimination ideals in tropical setting
- Tropical dimension theory
- Basic applications

### 第 16 週：2027-01-18 〜 2027-01-24
**目標**: Applications の継続
- Tropical morphisms and their properties
- Fiber structures
- More elimination theory

### 第 17 週：2027-01-25 〜 2027-01-31
**目標**: 応用の完成と統合
- Complete applications section
- Cross-references between sections
- Example gallery

### 第 18 週：2027-02-01 〜 2027-02-07
**目標**: 形式の統一と最適化
- Code organization and structure
- Documentation improvements
- Proof optimization

### 第 19 週：2027-02-08 〜 2027-02-14
**目標**: テストケースと例の追加
- Concrete examples throughout
- Counterexamples where applicable
- Test suite for key lemmas

### 第 20 週：2027-02-15 〜 2027-02-21
**目標**: リファクタリング
- Remove redundancy
- Improve readability
- Standardize naming conventions

### 第 21 週：2027-02-22 〜 2027-02-28
**目標**: ドキュメント作成
- Comprehensive documentation
- Usage examples
- Mathematical context

### 第 22 週：2027-03-01 〜 2027-03-07
**目標**: 最終レビューと完成
- Full proof verification
- Consistency check
- Final polish

## リソース配分
- **Lean コーディング**: 60%
- **数学的検討**: 25%
- **ドキュメント/テスト**: 15%

## 依存関係
- Mathlib の RingTheory, Ideal, Congruence モジュール
- Tropical geometry の既存ライブラリ（必要に応じて）
- Proof general tactics (simp, ring, congruence)

## 評価基準
- **数学的厳密性**: すべての主張の完全な証明
- **一般性**: 最も一般的な状況でのステートメント
- **実用性**: 具体的な例の検証可能性
- **可読性**: コードとドキュメントの明確さ
- **保守性**: Mathlib との整合性

## リスク管理
1. **Mathlib の変更**: 定期的なバージョンチェック
2. **証明の難易度**: 段階的なアプローチでリスク分散
3. **リソース不足**: パラレルタスクでの進行

(End of file - total 147 lines)