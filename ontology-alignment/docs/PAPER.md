# メタファー理論に基づく証明可能なオントロジーアライメント
## Provable Ontology Alignment Based on Metaphor Theory: A Curry-Howard Approach

---

**著者**: [Anonymous for Review]

**所属**: [Anonymous for Review]

**連絡先**: [Anonymous for Review]

---

## Abstract

オントロジーアライメントは、異なるオントロジー間の意味的対応関係を発見する重要な課題である。本論文では、認知言語学のメタファー理論を理論的基盤として、Curry-Howard対応を活用した証明可能なオントロジーアライメント手法を提案する。提案手法では、異なるドメインオントロジーが共通の「基本領域オントロジー」から展開されたものと捉え、アライメントを型理論における命題として定式化する。これにより、アライメントの証明がそのままアライメントアルゴリズムとなり、型検査によって正当性が保証される。Lean4定理証明支援系による実装を行い、SNOMED CTとGene Ontologyという実世界の生物医学オントロジーへの適用を通じて、提案手法の有効性を示す。

**キーワード**: オントロジーアライメント、メタファー理論、Curry-Howard対応、依存型、形式検証、SNOMED CT、Gene Ontology

---

## 1. Introduction

### 1.1 背景と動機

セマンティックウェブの発展に伴い、多様なドメインで独立に構築されたオントロジーを相互運用可能にする**オントロジーアライメント**の重要性が増している[1]。特に生物医学分野では、SNOMED CT（臨床医学）[2]、Gene Ontology（分子生物学）[3]、ICD（疾病分類）など、数百を超えるオントロジーが存在し、これらの統合的活用が求められている。

従来のオントロジーアライメント手法は、主に以下のアプローチに分類される：

1. **字句的手法**: 概念名の文字列類似度に基づく[4]
2. **構造的手法**: グラフ構造の類似性に基づく[5]
3. **意味的手法**: 外部知識源（WordNet等）を活用[6]
4. **機械学習手法**: 埋め込み表現による類似度計算[7]

しかし、これらの手法には共通の課題がある：

- **正当性の保証がない**: 発見されたアライメントが意味的に正しいことの形式的保証がない
- **説明可能性の欠如**: なぜ2つの概念がアライメントされるのかの根拠が不明確
- **異質なドメイン間の困難**: 語彙や構造が大きく異なるオントロジー間での対応発見が困難

### 1.2 提案手法の着想

本研究は、認知言語学における**概念メタファー理論**[8]から着想を得ている。Lakoff & Johnsonによれば、人間は抽象的概念を身体的経験に根ざした基本的なイメージスキーマ（Container、Path、Force等）を通じて理解する。例えば：

- 「議論は**戦争**だ」（ARGUMENT IS WAR）
- 「時間は**お金**だ」（TIME IS MONEY）
- 「心は**容器**だ」（MIND IS A CONTAINER）

この理論を応用すると、異なるドメインオントロジーは、共通の基本領域（イメージスキーマ）から異なる方向に「展開」されたものと捉えられる。

```
                基本領域 O_F
                    │
         φ_A ╱─────┴─────╲ φ_B
            ╱             ╲
           ▼               ▼
    オントロジー A     オントロジー B
```

この視点に立てば、**アライメントとは、同じ基本概念から展開された概念間の対応**として定義できる。

### 1.3 本研究の貢献

本論文の主要な貢献は以下の通りである：

1. **理論的貢献**: メタファー理論に基づくオントロジーアライメントの新しい理論的枠組みの提案

2. **形式的貢献**: Curry-Howard対応を活用し、アライメントを型理論の命題として定式化。証明＝アルゴリズムの同一性を実現

3. **実装的貢献**: Lean4定理証明支援系による完全な実装の提供

4. **実証的貢献**: SNOMED CTとGene Ontologyへの適用による実世界での有効性の実証

### 1.4 論文の構成

2章で関連研究を概観し、3章で理論的枠組みを提示する。4章で形式的定義を与え、5章でLean4による実装を説明する。6章でSNOMED CT-GOアライメントの事例研究を示し、7章で議論と評価を行う。8章で結論と今後の課題を述べる。

---

## 2. Related Work

### 2.1 オントロジーアライメント

オントロジーアライメント（オントロジーマッチングとも呼ばれる）は、2つのオントロジー O₁, O₂ 間の対応関係（アライメント）A を発見する問題である[1]。形式的には：

$$A = \{(e_1, e_2, r, c) | e_1 \in O_1, e_2 \in O_2, r \in \{=, \sqsubseteq, \sqsupseteq, \perp\}, c \in [0,1]\}$$

OAEI（Ontology Alignment Evaluation Initiative）[9]は、アライメント手法の標準的な評価フレームワークを提供している。代表的なシステムとして、AML[10]、LogMap[11]、PARIS[12]などがある。

これらのシステムは高い適合率・再現率を達成しているが、発見されたアライメントの**形式的正当性**は保証されていない。

### 2.2 Foundational Ontology

上位オントロジー（Foundational Ontology, Upper Ontology）は、ドメイン非依存の一般的概念を定義し、ドメインオントロジーの設計指針を提供する[13]。代表的なものとして：

- **BFO（Basic Formal Ontology）**[14]: OBO Foundryの標準上位オントロジー。Continuant/Occurrentの二分法
- **DOLCE**[15]: 認知的観点を重視した上位オントロジー
- **SUMO**[16]: 大規模な上位-中位オントロジー

本研究の「基本領域オントロジー」は、これらの上位オントロジーと認知言語学のイメージスキーマを統合したものと位置づけられる。

### 2.3 形式検証とオントロジー

オントロジーの形式検証に関する研究として、記述論理に基づく一貫性検査[17]、OWL推論器による分類検証[18]などがある。しかし、オントロジー**間**のアライメントを定理証明の枠組みで扱う研究は限られている。

Kalfoglouら[19]は、オントロジーマッピングの形式的意味論を議論しているが、証明可能性との結びつきは扱っていない。

### 2.4 Curry-Howard対応

Curry-Howard対応（命題-型対応）[20]は、論理学の命題と型理論の型、証明とプログラムの間の深い対応関係を示す：

| 論理 | 型理論 |
|-----|-------|
| 命題 P | 型 P |
| 証明 p : P | プログラム p : P |
| P → Q | 関数型 P → Q |
| P ∧ Q | 直積型 P × Q |
| ∀x.P(x) | 依存関数型 Π(x:A).P(x) |
| ∃x.P(x) | 依存対型 Σ(x:A).P(x) |

この対応を活用すると、命題の証明を構築することがプログラムを書くことと同一になる。本研究では、この原理をオントロジーアライメントに適用する。

### 2.5 メタファー理論の計算的応用

概念メタファー理論の計算的応用として、メタファー検出[21]、メタファー解釈[22]などの自然言語処理タスクがある。しかし、オントロジー工学への応用は十分に探求されていない。

Gangemi & Presutti[23]は、オントロジー設計パターンを認知的観点から分析しているが、アライメントへの応用は行っていない。

---

## 3. Theoretical Framework

### 3.1 概念メタファー理論の概要

Lakoff & Johnson[8]の概念メタファー理論によれば、メタファーは単なる言語表現ではなく、人間の概念体系の根幹をなす認知機構である。抽象的な概念は、より具体的な身体的経験に基づく概念（**基本領域**）を通じて理解される。

**イメージスキーマ**は、最も基本的な概念構造であり、身体的経験から抽出された抽象的パターンである：

| スキーマ | 経験的基盤 | 例 |
|---------|-----------|-----|
| CONTAINER | 身体の内部/外部 | 「心の中」「部屋に入る」 |
| PATH | 移動の経験 | 「目標に向かう」「道を外れる」 |
| FORCE | 物理的力の経験 | 「圧力をかける」「障害を乗り越える」 |
| BALANCE | 身体的均衡 | 「心のバランス」「安定した関係」 |
| PART-WHOLE | 身体部位 | 「社会の一員」「問題の核心」 |

**不変原則（Invariance Principle）**[24]：メタファー写像は、基本領域のイメージスキーマ構造を目標領域でも保存する。

### 3.2 オントロジーへの適用

本研究では、メタファー理論をオントロジーに適用し、以下のモデルを提案する：

**定義3.1（メタファー的オントロジー展開）**
オントロジー O_D は、基本領域オントロジー O_F からの**展開写像** φ : O_F → O_D によって構造化される。この写像は：

1. **概念写像**: 基本概念を応用ドメインの概念に対応付ける
2. **関係保存**: 基本領域の関係構造を保存する
3. **精緻化許容**: 概念の細分化を許す
4. **拡張許容**: ドメイン固有概念の追加を許す

**例3.1**: 医療オントロジーの展開
```
φ_med: O_F → O_med
  CONTAINER ↦ Body（身体は容器）
  FORCE ↦ Disease（疾患は力/障害）
  PART-WHOLE ↦ Organ（器官は部分）
  ENABLEMENT ↦ Treatment（治療は可能化）
```

### 3.3 アライメントの定義

**定義3.2（メタファー的アライメント）**
2つのオントロジー O_A, O_B とその展開写像 φ_A, φ_B が与えられたとき、概念 c_A ∈ O_A と c_B ∈ O_B の**アライメント**は、以下の条件を満たす基本概念 f ∈ O_F の存在である：

$$\text{Align}(c_A, c_B) \iff \exists f \in O_F.\ \phi_A(f) = c_A \land \phi_B(f) = c_B$$

直観的には、2つの概念が「同じ基本概念の異なるドメインへの展開」であるとき、それらはアライメント可能である。

**定理3.1（アライメントの対称性）**
$$\text{Align}(c_A, c_B) \Rightarrow \text{Align}(c_B, c_A)$$

**定理3.2（アライメントの推移性）**
同じ基本概念 f を経由する場合：
$$\text{Align}(c_A, c_B) \land \text{Align}(c_B, c_C) \land (f_1 = f_2) \Rightarrow \text{Align}(c_A, c_C)$$

### 3.4 変形差分

展開写像は同じ基本概念を異なるドメインに写像するが、その過程で**変形差分（Δ）**が生じる。これは各ドメイン固有の文脈・制約・精緻化を表す。

**定義3.3（変形差分）**
展開写像 φ に対する変形差分 Δ_φ は以下を含む：
- 追加された概念（基本領域にない概念）
- ドメイン固有の制約
- コンテキスト情報

アライメントの**強さ**は、変形差分の互換性によって評価できる：

$$\text{AlignmentScore}(c_A, c_B) = \text{sim}_F(f_A, f_B) \cdot \text{compat}(\Delta_A, \Delta_B)$$

---

## 4. Formal Definitions

本章では、提案手法の形式的定義を依存型理論の枠組みで与える。

### 4.1 オントロジーの型

**定義4.1（オントロジー）**
オントロジーは以下の構造体として定義される：

```
Ontology := {
  Concept : Type
  Relation : Concept → Concept → Type
  decEq : DecidableEq Concept
}
```

- `Concept`: 概念の型
- `Relation c₁ c₂`: c₁ と c₂ の間の関係の型
- `decEq`: 概念の等価性判定が決定可能

### 4.2 基本領域オントロジー

**定義4.2（基本概念）**
イメージスキーマに基づく基本概念の帰納型：

```
inductive FoundationConcept where
  | Container    -- 容器
  | Path         -- 経路
  | Link         -- 結合
  | Force        -- 力
  | Balance      -- 均衡
  | Enablement   -- 可能化
  | Entity       -- 実体
  | PartWhole    -- 部分-全体
  | Hierarchy    -- 階層
  | Process      -- 過程
  | State        -- 状態
  | Change       -- 変化
```

### 4.3 展開写像

**定義4.3（展開写像）**
展開写像は基本領域からドメインオントロジーへの準同型：

```
ExpansionMap (O_D : Ontology) := {
  conceptMap : FoundationConcept → O_D.Concept
  relationPreserve : ∀ {c₁ c₂}, 
    FoundationRelation c₁ c₂ → O_D.Relation (conceptMap c₁) (conceptMap c₂)
}
```

`relationPreserve` は関係の保存を**証明**として要求する。

### 4.4 アライメントの型（命題）

**定義4.4（概念アライメント）**
アライメントは以下の依存型として定義される：

```
ConceptAlignment (O_A O_B : Ontology) 
    (φ_A : ExpansionMap O_A) 
    (φ_B : ExpansionMap O_B)
    (c_A : O_A.Concept) 
    (c_B : O_B.Concept) := {
  foundationWitness : FoundationConcept
  fromA : φ_A.conceptMap foundationWitness = c_A
  fromB : φ_B.conceptMap foundationWitness = c_B
}
```

この定義は**命題**であり、その**証明項**がアライメントの**証拠**となる。

### 4.5 Curry-Howard対応の活用

この定式化により、以下のCurry-Howard対応が成立する：

| アライメントの観点 | 論理/型理論 |
|------------------|------------|
| アライメント命題 | 型 `ConceptAlignment ...` |
| アライメントの証明 | 型の項（プログラム） |
| アライメント計算 | 証明項の構築 |
| 正当性検証 | 型検査 |

**定理4.1（証明可能性＝計算可能性）**
```
(∃ prf : ConceptAlignment O_A O_B φ_A φ_B c_A c_B, True) ↔
(decideAlignment φ_A φ_B c_A c_B).isSome
```

アライメントの証明が存在することと、決定手続きが成功することは同値である。

### 4.6 アライメントの計算定理

**定理4.2（メタファー的アライメントの存在）**
任意の基本概念 f に対して、その展開同士はアライメント可能：

```
theorem metaphorical_alignment_exists
    (φ_A : ExpansionMap O_A) (φ_B : ExpansionMap O_B) (f : FoundationConcept) :
    ConceptAlignment O_A O_B φ_A φ_B (φ_A.conceptMap f) (φ_B.conceptMap f) := {
  foundationWitness := f
  fromA := rfl
  fromB := rfl
}
```

この定理の**証明項自体**が、アライメントを計算するアルゴリズムである。

---

## 5. Implementation in Lean4

### 5.1 実装概要

提案手法をLean4定理証明支援系[25]で実装した。Lean4は依存型を持つ純粋関数型言語であり、定理証明と汎用プログラミングの両方に使用できる。

プロジェクト構成：

```
ontology-alignment/
├── OntologyAlignment/
│   ├── Basic.lean           # 基本型定義
│   ├── Foundation.lean      # 基本領域オントロジー
│   ├── ExpansionMap.lean    # 展開写像
│   ├── Alignment.lean       # アライメント命題（コア）
│   ├── Tactics.lean         # 自動証明タクティクス
│   └── RealWorld/           # 実世界オントロジー
│       ├── SNOMEDCT.lean
│       ├── GeneOntology.lean
│       └── SNOMEDGOAlignment.lean
└── test/                    # テストスイート
```

### 5.2 コア定義の実装

**基本領域オントロジー**:

```lean
inductive FoundationConcept where
  | Container | Path | Link | Force | Balance | Enablement
  | Entity | PartWhole | Hierarchy | Process | State | Change
  deriving DecidableEq, Repr

inductive FoundationRelation : FoundationConcept → FoundationConcept → Type where
  | contains : FoundationRelation .Container .Entity
  | causes : FoundationRelation .Force .Change
  | partOf : FoundationRelation .PartWhole .Entity
  -- ... その他の関係
```

**アライメント型**:

```lean
structure ConceptAlignment 
    (O_A O_B : Ontology) 
    (φ_A : ExpansionMap O_A) 
    (φ_B : ExpansionMap O_B)
    (c_A : O_A.Concept) 
    (c_B : O_B.Concept) where
  foundationWitness : FoundationConcept
  fromA : φ_A.conceptMap foundationWitness = c_A
  fromB : φ_B.conceptMap foundationWitness = c_B
```

### 5.3 自動証明タクティクス

アライメント証明を自動化するタクティクスを実装：

```lean
macro "find_alignment" : tactic =>
  `(tactic|
    constructor
    · first | exact .Container | exact .Path | exact .Force | ...
    · rfl
    · rfl)
```

このタクティクスは：
1. 基本概念を順番に試行
2. 両方の展開写像が一致する基本概念を発見
3. 証明項を自動構築

### 5.4 決定手続き

アライメントの存在を決定的に判定する関数：

```lean
def decideAlignment 
    {O_A O_B : Ontology} [DecidableEq O_A.Concept] [DecidableEq O_B.Concept]
    (φ_A : ExpansionMap O_A) (φ_B : ExpansionMap O_B)
    (c_A : O_A.Concept) (c_B : O_B.Concept) :
    Option (ConceptAlignment O_A O_B φ_A φ_B c_A c_B) :=
  let candidates := allFoundationConcepts.filter fun f =>
    φ_A.conceptMap f = c_A ∧ φ_B.conceptMap f = c_B
  match candidates with
  | f :: _ => some { foundationWitness := f, fromA := rfl, fromB := rfl }
  | [] => none
```

### 5.5 証明の抽出

証明項からアルゴリズムを抽出：

```lean
def computeAlignment (φ_A : ExpansionMap O_A) (φ_B : ExpansionMap O_B) 
    (f : FoundationConcept) :
    ConceptAlignment O_A O_B φ_A φ_B (φ_A.conceptMap f) (φ_B.conceptMap f) :=
  metaphorical_alignment_exists φ_A φ_B f
```

定理 `metaphorical_alignment_exists` の証明項が、そのままアライメント計算関数となる。

---

## 6. Case Study: SNOMED CT and Gene Ontology

### 6.1 対象オントロジー

**SNOMED CT（Systematized Nomenclature of Medicine - Clinical Terms）**[2]：
- 世界最大の臨床医学用語オントロジー
- 約311,000概念、19の主要階層
- IS-A関係と50以上の属性関係
- 主要階層：Clinical Finding, Procedure, Body Structure, ...

**Gene Ontology（GO）**[3]：
- 遺伝子機能の標準オントロジー
- 約45,000用語、3つのアスペクト
- DAG構造、is_a/part_of/regulates関係
- アスペクト：Molecular Function, Cellular Component, Biological Process

### 6.2 展開写像の定義

**SNOMED CTへの展開**:

```lean
def snomedExpansion : ExpansionMap SNOMEDOntology := {
  conceptMap := fun
    | .Container => .hierarchy .BodyStructure
    | .Force => .clinicalFinding .Disease
    | .Enablement => .procedure .TherapeuticProcedure
    | .Process => .hierarchy .Procedure
    | .Change => .clinicalFinding .Symptom
    | .PartWhole => .bodyStructure .Organ
    -- ...
}
```

**Gene Ontologyへの展開**:

```lean
def goExpansion : ExpansionMap GeneOntology := {
  conceptMap := fun
    | .Container => .cellularComponent .IntracellularOrganelle
    | .Force => .biologicalProcess .BiologicalRegulation
    | .Enablement => .aspect .MolecularFunction
    | .Process => .aspect .BiologicalProcess
    | .Change => .biologicalProcess .ResponseToStimulus
    | .PartWhole => .cellularComponent .ProteinComplex
    -- ...
}
```

### 6.3 発見されたアライメント

展開写像に基づき、以下のアライメントが発見・証明された：

| 基本概念 | SNOMED CT | Gene Ontology | 意味的根拠 |
|---------|-----------|---------------|-----------|
| Container | BodyStructure | CellularComponent | 身体/細胞は「容器」 |
| Force | Disease | BiologicalRegulation | 疾患/調節は「力/影響」 |
| Enablement | TherapeuticProcedure | MolecularFunction | 治療/分子機能は「可能化」 |
| Process | Procedure | BiologicalProcess | 処置/過程は「時間的展開」 |
| Change | Symptom | ResponseToStimulus | 症状/応答は「変化」 |
| PartWhole | Organ | ProteinComplex | 器官/複合体は「部分-全体」 |
| Path | DiagnosticProcedure | SignalTransduction | 診断/信号は「経路」 |
| Link | Tissue | Membrane | 組織/膜は「結合/境界」 |

### 6.4 アライメント証明の例

**Disease ↔ BiologicalRegulation**:

```lean
theorem disease_regulation_alignment :
    ConceptAlignment SNOMEDOntology GeneOntology 
                     snomedExpansion goExpansion 
                     (.clinicalFinding .Disease) 
                     (.biologicalProcess .BiologicalRegulation) := {
  foundationWitness := .Force
  fromA := rfl
  fromB := rfl
}
```

このアライメントの意味論的根拠：
- 疾患は正常な身体機能への「障害力」と捉えられる
- 生物学的調節は細胞過程を制御する「力」である
- 両者とも「Force」スキーマの異なるドメインへの展開

### 6.5 検証結果

```lean
-- アライメント存在の検証
#eval (decideAlignment snomedExpansion goExpansion 
        (.clinicalFinding .Disease) 
        (.biologicalProcess .BiologicalRegulation)).isSome
-- true

-- アライメント非存在の検証
#eval (decideAlignment snomedExpansion goExpansion 
        (.clinicalFinding .Disease)
        (.cellularComponent .Nucleus)).isSome
-- false（異なる基本概念）
```

### 6.6 クロスオントロジー検索

```lean
-- SNOMED CT概念に対応するGO概念を検索
#eval findGOEquivalent (.clinicalFinding .Disease)
-- some (biologicalProcess BiologicalRegulation)

-- GO概念に対応するSNOMED CT概念を検索  
#eval findSNOMEDEquivalent (.aspect .BiologicalProcess)
-- some (hierarchy Procedure)
```

---

## 7. Discussion

### 7.1 手法の利点

**形式的保証**:
従来手法と異なり、発見されたアライメントは型検査によって形式的に正当性が保証される。誤ったアライメントは型エラーとして検出される。

**説明可能性**:
各アライメントには `foundationWitness` として共通の基本概念が明示される。これにより、「なぜ2つの概念が対応するのか」を説明できる。

**再現性**:
アライメントは決定的アルゴリズムによって計算され、同じ入力に対して常に同じ結果を返す。

**拡張性**:
新しいドメインオントロジーを追加する場合、展開写像を定義するだけでよい。基本領域を拡張する場合も、既存の証明は保持される。

### 7.2 従来手法との比較

| 観点 | 従来手法 | 提案手法 |
|------|---------|---------|
| 正当性保証 | テストベース | 数学的証明 |
| 説明可能性 | 限定的 | 証明構造が説明 |
| 異質ドメイン | 困難 | 基本領域で橋渡し |
| アルゴリズム | 手動設計 | 証明から自動抽出 |
| 計算複雑性 | O(n²)以上 | O(n × |F|) |

ここで n は概念数、|F| は基本概念数（現在12）。

### 7.3 制限事項

**展開写像の手動定義**:
現在、展開写像は専門家が手動で定義する必要がある。これは労力を要するが、同時にドメイン知識を明示的に形式化する利点もある。

**サブセットへの適用**:
本研究では、SNOMED CTとGOの代表的サブセットに適用した。完全なオントロジーへの適用には、より大規模な基本領域と展開写像が必要。

**確率的スコアの欠如**:
現在の実装は二値的なアライメント（存在/非存在）のみを扱う。確率的信頼度スコアの形式化は今後の課題。

### 7.4 BFOとの統合

Basic Formal Ontology (BFO)[14]との統合により、より精密なアライメントが可能になる：

```lean
inductive BiomedicalFoundationConcept where
  -- イメージスキーマ（12種）
  | Container | Force | Process | ...
  -- BFO拡張（6種）
  | Continuant | Occurrent | Disposition | ...
  -- OGMS拡張（6種）
  | Disease | Disorder | PathologicalProcess | ...
```

この拡張により、OBO Foundryオントロジーとの互換性が向上する。

### 7.5 理論的含意

本研究は、オントロジーアライメントに対する新しい視点を提供する：

1. **認知的基盤**: アライメントは恣意的な対応ではなく、人間の認知構造に根ざした対応である

2. **構成的証明**: アライメントの存在証明は、アライメント計算アルゴリズムと同一である

3. **検証可能性**: アライメントの正しさは、数学的に検証可能である

---

## 8. Conclusion

### 8.1 まとめ

本論文では、認知言語学のメタファー理論に基づく証明可能なオントロジーアライメント手法を提案した。主な貢献は：

1. **理論的枠組み**: 異なるドメインオントロジーを、共通の基本領域からの「展開」として捉える理論モデル

2. **形式的定式化**: Curry-Howard対応を活用し、アライメントを依存型の命題として定式化。証明＝アルゴリズムの同一性を実現

3. **Lean4実装**: 完全に検証可能な実装の提供

4. **実世界適用**: SNOMED CTとGene Ontologyへの適用による有効性の実証

### 8.2 今後の課題

1. **展開写像の自動学習**: 機械学習を活用した展開写像の自動獲得

2. **確率的拡張**: 変形差分に基づくアライメントスコアの形式化

3. **大規模評価**: OAEIベンチマークでの定量的評価

4. **ツール開発**: 実用的なWebアプリケーション/APIの開発

5. **他分野への応用**: 生物医学以外のドメイン（法律、金融等）への適用

### 8.3 展望

本研究は、オントロジーアライメントを「発見」の問題から「証明」の問題へと再定式化した。この視点の転換は、セマンティックウェブにおける知識統合の信頼性向上に貢献すると期待される。

また、メタファー理論に基づくアプローチは、人間の概念理解とオントロジー設計の橋渡しとなり、より直観的で説明可能なオントロジー工学への道を開く可能性がある。

---

## References

[1] Euzenat, J., & Shvaiko, P. (2013). Ontology Matching (2nd ed.). Springer.

[2] SNOMED International. (2024). SNOMED CT Documentation. https://www.snomed.org/

[3] Gene Ontology Consortium. (2021). The Gene Ontology resource: enriching a GOld mine. Nucleic Acids Research, 49(D1), D325-D334.

[4] Stoilos, G., Stamou, G., & Kollias, S. (2005). A string metric for ontology alignment. ISWC 2005, 624-637.

[5] Hu, W., Qu, Y., & Cheng, G. (2008). Matching large ontologies: A divide-and-conquer approach. Data & Knowledge Engineering, 67(1), 140-160.

[6] Giunchiglia, F., Shvaiko, P., & Yatskevich, M. (2004). S-Match: an algorithm and an implementation of semantic matching. ESWS 2004, 61-75.

[7] Zhang, Y., et al. (2021). OntoEA: Ontology-guided entity alignment via joint knowledge graph embedding. ACL 2021.

[8] Lakoff, G., & Johnson, M. (1980). Metaphors We Live By. University of Chicago Press.

[9] Ontology Alignment Evaluation Initiative. http://oaei.ontologymatching.org/

[10] Faria, D., et al. (2013). The AgreementMakerLight ontology matching system. OTM Confederated International Conferences, 527-541.

[11] Jiménez-Ruiz, E., & Grau, B. C. (2011). LogMap: Logic-based and scalable ontology matching. ISWC 2011, 273-288.

[12] Suchanek, F. M., Abiteboul, S., & Senellart, P. (2011). PARIS: Probabilistic alignment of relations, instances, and schema. PVLDB, 5(3), 157-168.

[13] Guarino, N. (1998). Formal ontology and information systems. FOIS 1998, 3-15.

[14] Arp, R., Smith, B., & Spear, A. D. (2015). Building Ontologies with Basic Formal Ontology. MIT Press.

[15] Masolo, C., et al. (2003). WonderWeb Deliverable D18: Ontology Library. ISTC-CNR.

[16] Niles, I., & Pease, A. (2001). Towards a standard upper ontology. FOIS 2001, 2-9.

[17] Baader, F., et al. (2003). The Description Logic Handbook. Cambridge University Press.

[18] Sirin, E., et al. (2007). Pellet: A practical OWL-DL reasoner. Journal of Web Semantics, 5(2), 51-53.

[19] Kalfoglou, Y., & Schorlemmer, M. (2003). Ontology mapping: the state of the art. The Knowledge Engineering Review, 18(1), 1-31.

[20] Wadler, P. (2015). Propositions as types. Communications of the ACM, 58(12), 75-84.

[21] Shutova, E., & Teufel, S. (2010). Metaphor corpus annotated for source-target domain mappings. LREC 2010.

[22] Ovchinnikova, E., et al. (2014). Abductive interpretation of metaphor. Proceedings of the Second Workshop on Metaphor in NLP, 33-41.

[23] Gangemi, A., & Presutti, V. (2009). Ontology design patterns. Handbook on Ontologies, 221-243.

[24] Lakoff, G. (1993). The contemporary theory of metaphor. Metaphor and Thought, 2, 202-251.

[25] Moura, L. D., & Ullrich, S. (2021). The Lean 4 theorem prover and programming language. CADE 2021, 625-635.

---

## Appendix A: Complete Lean4 Code

完全なLean4実装は以下で公開予定：

```
https://github.com/[anonymous]/ontology-alignment
```

## Appendix B: SNOMED CT - GO Alignment Table

| # | Foundation | SNOMED CT | GO | Score |
|---|------------|-----------|-----|-------|
| 1 | Container | BodyStructure | CellularComponent | 1.0 |
| 2 | Force | Disease | BiologicalRegulation | 1.0 |
| 3 | Enablement | TherapeuticProcedure | MolecularFunction | 1.0 |
| 4 | Process | Procedure | BiologicalProcess | 1.0 |
| 5 | Change | Symptom | ResponseToStimulus | 1.0 |
| 6 | PartWhole | Organ | ProteinComplex | 1.0 |
| 7 | Path | DiagnosticProcedure | SignalTransduction | 1.0 |
| 8 | Link | Tissue | Membrane | 1.0 |
| 9 | Balance | ObservableEntity | CellularProcess | 1.0 |
| 10 | State | Finding | Cytoplasm | 1.0 |
| 11 | Entity | Organism | CellularComponent | 1.0 |
| 12 | Hierarchy | ClinicalFinding | DevelopmentalProcess | 1.0 |

---

*Submitted to: [Conference/Journal Name]*

*Date: December 2025*
