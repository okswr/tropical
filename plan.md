# 形式化完了プラン

## 現在の変更済みファイル (priority order)

| # | ファイル | 内容 | `sorry`数 | 状態 |
|---|----------|------|-----------|------|
| 1 | `Tropical.lean` | 主要ファイル：ポアンール半群、booleanization、多項式環の核 | ~13 | `lake build` is passing with warnings |
| 2 | `Tropical/TropicalLemma.lean` | 核心代数学：RingConSimple, 第一同型定理、順序同値定理 | 0 | 完成 |
| 3 | `Tropical/TropicalLemma2.lean` | 合同定理：transGen、swappedSumPairs、有限生成合同 | 0 | 完成 |
| 4 | `CalcrationFolderTemp/TropicalLemm.lean` | 実験ファイル | 40+ | 不要、破棄推奨 |
| 5 | `text/*.pdf` | 原著1本 | — | 参照資料 |

## 完了までの作業リスト

### Priority 1 — `Tropical.lean` の `sorry` 埋め (~13 個)

| 行番号 | 内容 | 難易度 | 備考 |
|--------|------|--------|------|
| 145-147 | `MyRing` の可換性 `∀ a b, a+b = b+a` | 低 | 日本語の証明スケッチあり、4 要素 type の enumerate |
| 333-336 | `WithTop Nat` semiring instance の `nsmul_zero`, `nsmul_succ`, `natCast_zero`, `natCast_succ` | 低 | 標準的な帰納法 |
| 396-399 | `WithTop Real` semiring instance の同じ 4lemma | 低 | `WithTop Nat` と同様 |
| 652 | `IsMaximal (RingHom.ker booleanization)` | 中 | 既に `pr : IsCoatom` が線 600 にある。`IsMaximal` ↔ `IsCoatom` の関係を使う |
| 708-711 | `ker_ev₀_eq_ideal`：`f.eval 0 = 0 ↔ ∃ g, f = X * g` | 中 | 日本語スケッチに `f = X * (divX f) + C (f.coeff 0)` の方針あり |

### Priority 2 — クリーンアップ

- `Tropical/Basic.lean` (`def hello := "world"`) → 削除。unused
- `CalcrationFolderTemp/` 全体 → 削除。実験ファイル、`TropicalLemma.lean` に既に正しい実装がある
- `README.md` (boilerplate) → 内容を書き換え、プロジェクトの目的を記載

### Priority 3 — 最終目標：ヒルベルトの零点定理

- `TropicalLemma2.lean` 線 244 に目標としてマークされている
- 現在の成果：`ringConGen_eq_transGen`, `swappedSumPairs`, `ker_ev₀_isConGenX_Zero` が利用可能
- 原著の Section 2.13 以降を Lean で形式化

## 推奨実行順序

```
1. Tropical.lean の sorry 13 個を埋める
   ├─ WithTop Nat/Real の nsmul, natCast (8 個)
   ├─ MyRing 可換性 (1 個)
   ├─ IsMaximal booleanization kernel (1 個)
   └─ ker_ev₀_eq_ideal (3 個)

2. クリーンアップ
   ├─ Basic.lean 削除
   ├─ CalcrationFolderTemp/ 削除
   └─ lake/build artifacts 整理

3. 確認：lake build --clean && leancheck
   └─ sorry-free 状態を確保

4. (追加) ヒルベルトの零点定理へ向けて形式化を続ける
```
