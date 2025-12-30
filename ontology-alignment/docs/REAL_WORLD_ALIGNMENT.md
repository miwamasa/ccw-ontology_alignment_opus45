# SNOMED CT と Gene Ontology のアライメント

## 概要

本ドキュメントでは、メタファー理論に基づく証明可能なオントロジーアライメント手法を、実世界の生物医学オントロジーに適用した結果を説明します。

### 対象オントロジー

| オントロジー | 概要 | 規模 |
|-------------|------|------|
| **SNOMED CT** | 臨床医学用語の標準オントロジー | 約311,000概念 |
| **Gene Ontology** | 遺伝子機能の標準オントロジー | 約45,000用語 |

## 理論的基盤

### メタファー的視点

SNOMED CTとGOは、生物医学領域を異なる「視点」から記述しています：

```
                    基本領域
                   （イメージスキーマ + BFO）
                         │
            ┌────────────┴────────────┐
            │                         │
            ▼                         ▼
       SNOMED CT                Gene Ontology
    （臨床医学的視点）         （分子生物学的視点）
    
    ・疾患、診断、治療          ・分子機能、細胞過程
    ・身体構造                  ・細胞成分
    ・臨床所見                  ・生物学的調節
```

### 主要なアライメント対応

| 基本概念 | SNOMED CT | Gene Ontology | 意味的根拠 |
|---------|-----------|---------------|-----------|
| Container | BodyStructure | CellularComponent | 両方とも「容器」構造 |
| Force | Disease | BiologicalRegulation | 機能への「力/影響」 |
| Enablement | TherapeuticProcedure | MolecularFunction | 「可能化」の側面 |
| Process | Procedure | BiologicalProcess | 時間的展開 |
| Change | Symptom | ResponseToStimulus | 状態変化 |
| PartWhole | Organ | ProteinComplex | 部分-全体構造 |
| Path | DiagnosticProcedure | SignalTransduction | 経路メタファー |
| Link | Tissue | Membrane | 結合/境界 |

## Lean4実装

### ファイル構成

```
OntologyAlignment/RealWorld/
├── SNOMEDCT.lean           # SNOMED CTの形式化
├── GeneOntology.lean       # Gene Ontologyの形式化
├── BiomedicalFoundation.lean  # 拡張基本領域（BFO統合）
└── SNOMEDGOAlignment.lean  # アライメント証明
```

### SNOMED CTの形式化

```lean
/-- SNOMED CTのトップレベル階層 -/
inductive SNOMEDHierarchy where
  | ClinicalFinding       -- 臨床所見（最大の階層）
  | Procedure             -- 処置
  | BodyStructure         -- 身体構造
  | Organism              -- 生物
  | Substance             -- 物質
  | PharmaceuticalProduct -- 医薬品
  ...

/-- SNOMED CT概念の統合表現 -/
inductive SNOMEDConcept where
  | hierarchy : SNOMEDHierarchy → SNOMEDConcept
  | clinicalFinding : ClinicalFindingType → SNOMEDConcept
  | bodyStructure : BodyStructureType → SNOMEDConcept
  | procedure : ProcedureType → SNOMEDConcept
  | MyocardialInfarction    -- 具体例
  | Pneumonia
  ...
```

### Gene Ontologyの形式化

```lean
/-- GOの3つのアスペクト -/
inductive GOAspect where
  | MolecularFunction   -- 分子機能
  | CellularComponent   -- 細胞成分
  | BiologicalProcess   -- 生物学的過程

/-- GO概念の統合表現 -/
inductive GOConcept where
  | aspect : GOAspect → GOConcept
  | molecularFunction : MolecularFunctionType → GOConcept
  | cellularComponent : CellularComponentType → GOConcept
  | biologicalProcess : BiologicalProcessType → GOConcept
  | Apoptosis           -- 具体例
  | DNAReplication
  ...
```

### アライメント証明の例

```lean
/-- Disease ↔ BiologicalRegulation のアライメント証明 -/
theorem disease_regulation_alignment :
    ConceptAlignment SNOMEDOntology GeneOntology 
                     snomedExpansion goExpansion 
                     (.clinicalFinding .Disease) 
                     (.biologicalProcess .BiologicalRegulation) := {
  foundationWitness := .Force  -- 共通基盤：「力/障害」
  fromA := rfl
  fromB := rfl
}
```

## 使用例

### アライメントの検証

```lean
-- Disease-Regulation のアライメントを決定的に検証
#eval (decideAlignment snomedExpansion goExpansion 
        (.clinicalFinding .Disease) 
        (.biologicalProcess .BiologicalRegulation)).isSome
-- true
```

### 対応概念の検索

```lean
-- SNOMED CT概念に対応するGO概念を検索
#eval findGOEquivalent (.clinicalFinding .Disease)
-- some (biologicalProcess BiologicalRegulation)

-- GO概念に対応するSNOMED CT概念を検索
#eval findSNOMEDEquivalent (.aspect .BiologicalProcess)
-- some (hierarchy Procedure)
```

### アライメントレポートの生成

```lean
#eval generateAlignmentReport
-- === SNOMED CT - Gene Ontology Alignment Report ===
-- • SNOMED:BodyStructure ↔ CC:IntracellularOrganelle
--   Foundation: Container
-- • CF:Disease ↔ BP:BiologicalRegulation
--   Foundation: Force
-- ...
```

## BFOとの統合

Basic Formal Ontology (BFO) との統合により、より精密なアライメントが可能：

```lean
/-- 生物医学向け拡張基本概念 -/
inductive BiomedicalFoundationConcept where
  -- イメージスキーマ
  | Container | Path | Force | ...
  
  -- BFO拡張
  | Continuant    -- 持続体
  | Occurrent     -- 生起体
  | Disposition   -- 傾性
  
  -- OGMS拡張
  | Disease       -- 疾患傾性
  | Disorder      -- 障害
  | PathologicalProcess
  ...
```

## 理論的保証

### 健全性

```lean
theorem snomed_go_alignable :
    ∀ f : FoundationConcept,
    ConceptAlignment SNOMEDOntology GeneOntology 
                     snomedExpansion goExpansion 
                     (snomedExpansion.conceptMap f) 
                     (goExpansion.conceptMap f)
```

同じ基本概念から展開された概念は必ずアライメント可能。

### 対称性

```lean
theorem snomed_go_symmetric :
    ConceptAlignment SNOMED GO φ_S φ_G c_S c_G →
    ConceptAlignment GO SNOMED φ_G φ_S c_G c_S
```

アライメントは双方向。

## 制限事項と今後の課題

### 現在の制限

1. **サブセットのみ**: 完全なSNOMED CT/GOではなく代表的サブセット
2. **IS-A中心**: 属性関係の多くは未実装
3. **静的写像**: 展開写像は手動で定義

### 今後の拡張

1. OWL/OBOファイルからの自動インポート
2. 機械学習による展開写像の学習
3. 確率的アライメントスコアの形式化
4. OAEIベンチマークとの比較評価

## 参考文献

1. SNOMED International. SNOMED CT Documentation.
2. Gene Ontology Consortium. The Gene Ontology Resource.
3. Smith et al. (2005). Relations in Biomedical Ontologies.
4. Schulz et al. (2023). SNOMED CT and Basic Formal Ontology.
5. El-Sappagh et al. (2018). SNOMED CT standard ontology based on OGMS.
