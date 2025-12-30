# 理論概要図

## 1. メタファー的アライメントの全体像

```mermaid
graph TB
    subgraph Foundation["基本領域オントロジー O_F"]
        F1[Container]
        F2[Force]
        F3[PartWhole]
        F4[Enablement]
        F5[Process]
        F6[Balance]
    end
    
    subgraph Medical["医療オントロジー O_med"]
        M1[Body]
        M2[Disease]
        M3[Organ]
        M4[Treatment]
        M5[Recovery]
        M6[HealthState]
    end
    
    subgraph Engineering["工学オントロジー O_eng"]
        E1[Machine]
        E2[Failure]
        E3[Part]
        E4[Repair]
        E5[Restoration]
        E6[Status]
    end
    
    F1 -->|φ_med| M1
    F1 -->|φ_eng| E1
    F2 -->|φ_med| M2
    F2 -->|φ_eng| E2
    F3 -->|φ_med| M3
    F3 -->|φ_eng| E3
    F4 -->|φ_med| M4
    F4 -->|φ_eng| E4
    F5 -->|φ_med| M5
    F5 -->|φ_eng| E5
    F6 -->|φ_med| M6
    F6 -->|φ_eng| E6
    
    M1 <-.->|alignment| E1
    M2 <-.->|alignment| E2
    M3 <-.->|alignment| E3
    M4 <-.->|alignment| E4
    M5 <-.->|alignment| E5
    M6 <-.->|alignment| E6
```

## 2. Curry-Howard対応の活用

```mermaid
graph LR
    subgraph Logic["論理の世界"]
        L1[命題 P]
        L2[証明 p : P]
        L3[P → Q]
        L4[∃x.P x]
    end
    
    subgraph Program["プログラムの世界"]
        P1[型 P]
        P2[プログラム p : P]
        P3[関数型 P → Q]
        P4[Σ x : A, P x]
    end
    
    subgraph Alignment["アライメントの世界"]
        A1[アライメント命題]
        A2[アライメント証明]
        A3[アライメント関数]
        A4[アライメント発見]
    end
    
    L1 <--> P1
    L2 <--> P2
    L3 <--> P3
    L4 <--> P4
    
    P1 --> A1
    P2 --> A2
    P3 --> A3
    P4 --> A4
```

## 3. アライメント計算の流れ

```mermaid
sequenceDiagram
    participant U as User
    participant T as Type System
    participant P as Proof Search
    participant A as Alignment
    
    U->>T: ConceptAlignment O_A O_B φ_A φ_B c_A c_B
    T->>P: 型の有人性を判定
    P->>P: 基本概念を列挙
    loop 各基本概念 f
        P->>P: φ_A(f) = c_A ?
        P->>P: φ_B(f) = c_B ?
    end
    P-->>T: 証明項を構築
    T-->>U: アライメント証明
    U->>A: 証明からアルゴリズムを抽出
    A-->>U: 実行可能なアライメント
```

## 4. プロジェクト構造

```mermaid
graph TB
    subgraph Core["コア理論"]
        Basic[Basic.lean<br/>基本型]
        Foundation[Foundation.lean<br/>基本領域]
        ExpansionMap[ExpansionMap.lean<br/>展開写像]
        Alignment[Alignment.lean<br/>アライメント命題]
    end
    
    subgraph Auto["自動化"]
        Tactics[Tactics.lean<br/>タクティクス]
    end
    
    subgraph Examples["実例"]
        Medical[Medical.lean]
        Engineering[Engineering.lean]
        MedEng[MedicalEngineeringAlignment.lean]
    end
    
    subgraph Future["将来の拡張"]
        Category[Category.lean<br/>圏論的定式化]
    end
    
    Basic --> Foundation
    Foundation --> ExpansionMap
    ExpansionMap --> Alignment
    Alignment --> Tactics
    
    Foundation --> Medical
    Foundation --> Engineering
    ExpansionMap --> Medical
    ExpansionMap --> Engineering
    Alignment --> MedEng
    Medical --> MedEng
    Engineering --> MedEng
    
    Alignment --> Category
```

## 5. 型階層

```
Universe
└── Type
    └── Ontology
        ├── Concept : Type
        ├── Relation : Concept → Concept → Type
        └── decEq : DecidableEq Concept
    
    └── ExpansionMap (O_F → O_D)
        ├── conceptMap : O_F.Concept → O_D.Concept
        └── relationPreserve : ∀ r, O_F.Relation → O_D.Relation
    
    └── ConceptAlignment (O_A, O_B, φ_A, φ_B, c_A, c_B)
        ├── foundationWitness : FoundationConcept
        ├── fromA : φ_A.conceptMap f = c_A
        └── fromB : φ_B.conceptMap f = c_B
```

## 6. 証明戦略

```mermaid
flowchart TD
    Start[アライメント証明開始]
    
    Start --> Check{展開写像は<br/>正しく定義?}
    Check -->|No| Fix[展開写像を修正]
    Fix --> Check
    
    Check -->|Yes| Search[基本概念を探索]
    
    Search --> Try{φ_A f = c_A<br/>かつ<br/>φ_B f = c_B ?}
    
    Try -->|Yes| Construct[証明項を構築]
    Construct --> Done[アライメント完了]
    
    Try -->|No| Next{次の基本概念<br/>が存在?}
    Next -->|Yes| Search
    Next -->|No| Fail[アライメントなし]
```
