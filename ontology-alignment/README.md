# Provable Ontology Alignment

**証明可能なオントロジーアライメント：メタファー理論に基づくLean4実装**

## 概要

本プロジェクトは、オントロジーアライメントを**形式的証明**として定義することで、**Curry-Howard対応**を活用してアライメントの計算と検証を統一的に扱う理論的フレームワークを提供します。

### 核心的アイデア

```
アライメントの証明 ≡ アライメントアルゴリズム
```

- **証明**を構築する過程が、アライメントを**計算**する過程と同一
- 型検査によりアライメントの**正当性**が保証される
- 証明項の構造がアライメントの**説明**を提供する

## 理論的基盤

### メタファー理論（Lakoff & Johnson）

```
基本領域 (Foundation Ontology)
         │
    φ_A ╱ ╲ φ_B
       ╱   ╲
      ╱     ╲
   O_A       O_B
```

- **基本領域**：イメージスキーマ（Container, Force, PartWhole など）
- **展開写像 φ**：基本領域からドメインオントロジーへのメタファー的写像
- **アライメント**：同じ基本概念から展開された概念間の対応

### アライメント計算の公式

```
Alignment(c_A, c_B) = ∃f ∈ Foundation. φ_A(f) = c_A ∧ φ_B(f) = c_B
```

## プロジェクト構造

```
ontology-alignment/
├── lakefile.lean              # プロジェクト設定
├── lean-toolchain             # Lean4バージョン
├── OntologyAlignment.lean     # メインエクスポート
├── Main.lean                  # 実行可能デモ
├── OntologyAlignment/
│   ├── Basic.lean             # 基本型定義
│   ├── Foundation.lean        # 基本領域オントロジー
│   ├── ExpansionMap.lean      # 展開写像
│   ├── Alignment.lean         # アライメント命題（コア）
│   ├── Tactics.lean           # 自動証明タクティクス
│   └── Examples/
│       ├── Medical.lean       # 医療オントロジー
│       ├── Engineering.lean   # 工学オントロジー
│       └── MedicalEngineeringAlignment.lean  # アライメント証明
└── test/
    └── AlignmentTest.lean     # テストスイート
```

## クイックスタート

### 1. 環境準備

```bash
# elanのインストール
curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh

# プロジェクトのビルド
cd ontology-alignment
lake build
```

### 2. アライメント証明の例

```lean
import OntologyAlignment

-- Disease ≈ Failure の証明
theorem disease_failure_alignment :
    ConceptAlignment MedicalOntology EngineeringOntology 
                     medicalExpansion engineeringExpansion 
                     .Disease .Failure := {
  foundationWitness := .Force  -- 共通基盤：「力/障害」のスキーマ
  fromA := rfl                 -- φ_med(.Force) = .Disease
  fromB := rfl                 -- φ_eng(.Force) = .Failure
}
```

### 3. 自動証明

```lean
-- タクティクスによる自動アライメント発見
theorem auto_alignment :
    ConceptAlignment MedicalOntology EngineeringOntology 
                     medicalExpansion engineeringExpansion 
                     .Treatment .Repair := by
  find_alignment  -- 自動で証明を構築
```

### 4. 決定手続き

```lean
-- アライメントの存在を決定的に判定
#eval (decideAlignment medicalExpansion engineeringExpansion 
        MedicalConcept.Disease EngineeringConcept.Failure).isSome
-- true
```

## 主要なAPI

### 型定義

| 型 | 説明 |
|----|------|
| `Ontology` | オントロジーの基本構造 |
| `FoundationConcept` | 基本領域の概念（イメージスキーマ） |
| `ExpansionMap` | 展開写像（メタファー写像） |
| `ConceptAlignment` | 概念間のアライメント（命題） |
| `OntologyAlignment` | オントロジー全体のアライメント |

### 関数

| 関数 | 説明 |
|------|------|
| `computeAlignment` | アライメントの計算（証明から抽出） |
| `decideAlignment` | アライメントの存在判定 |
| `enumerateAllAlignments` | 全アライメントの列挙 |
| `findAlignmentWithTrace` | トレース付きアライメント発見 |

### タクティクス

| タクティクス | 説明 |
|-------------|------|
| `find_alignment` | 自動アライメント証明 |
| `try_foundation` | 基本概念の探索 |

## 理論的保証

### 健全性（Soundness）

```lean
theorem metaphorical_alignment_soundness :
    ∀ align ∈ alignments, semanticallyCompatible align.c_A align.c_B
```

アライメントが発見された場合、意味的互換性が保証される。

### 完全性（Completeness）

```lean
theorem decideAlignment_complete :
    ConceptAlignment O_A O_B φ_A φ_B c_A c_B → 
    (decideAlignment φ_A φ_B c_A c_B).isSome
```

アライメントが存在すれば、決定手続きが発見する。

### 対称性（Symmetry）

```lean
theorem alignment_symmetric :
    ConceptAlignment O_A O_B φ_A φ_B c_A c_B → 
    ConceptAlignment O_B O_A φ_B φ_A c_B c_A
```

## 拡張方法

### 新しいオントロジーの追加

1. 概念の帰納型を定義
2. 関係の帰納型を定義
3. `Ontology` 構造体を構築
4. 基本領域からの `ExpansionMap` を定義

### 新しい基本概念の追加

1. `FoundationConcept` に構成子を追加
2. 関連する `FoundationRelation` を追加
3. `allFoundationConcepts` リストを更新

## 今後の方向性

- [ ] 圏論的定式化（自然変換としてのアライメント）
- [ ] mathlibとの統合
- [ ] 確率的アライメントスコアの形式化
- [ ] OAEIベンチマークとの比較評価
- [ ] GUI/APIの提供

## 参考文献

1. Lakoff, G., & Johnson, M. (1980). *Metaphors We Live By*
2. Curry-Howard Correspondence (証明と計算の対応)
3. DOLCE, BFO (Foundational Ontologies)
4. OAEI (Ontology Alignment Evaluation Initiative)

## ライセンス

MIT License

## 著者

Claude (Anthropic) との共同設計
