/-
  OntologyAlignment/Examples/Engineering.lean
  
  機械工学ドメインオントロジーの定義
  
  機械を「システム」として捉える：
  - Machine ← Container
  - Part ← PartWhole
  - Failure ← Force（dysfunction）
  - Repair ← Enablement
-/

import OntologyAlignment.ExpansionMap
import OntologyAlignment.Alignment

namespace OntologyAlignment.Examples

/-! ## 工学概念 -/

/-- 機械工学ドメインの概念 -/
inductive EngineeringConcept where
  | Machine      -- 機械（全体）
  | Part         -- 部品
  | Component    -- コンポーネント
  | Assembly     -- アセンブリ
  | Failure      -- 故障
  | Malfunction  -- 不具合
  | Repair       -- 修理
  | Maintenance  -- メンテナンス
  | Operator     -- オペレーター
  | Status       -- 動作状態
  | Restoration  -- 復旧
  deriving DecidableEq, Repr, BEq

instance : HasLabel EngineeringConcept where
  label := fun
    | .Machine => "Machine"
    | .Part => "Part"
    | .Component => "Component"
    | .Assembly => "Assembly"
    | .Failure => "Failure"
    | .Malfunction => "Malfunction"
    | .Repair => "Repair"
    | .Maintenance => "Maintenance"
    | .Operator => "Operator"
    | .Status => "Status"
    | .Restoration => "Restoration"

/-! ## 工学関係 -/

/-- 機械工学ドメインの関係 -/
inductive EngineeringRelation : EngineeringConcept → EngineeringConcept → Type where
  -- 構造関係
  | hasPart : EngineeringRelation .Machine .Part
  | hasComponent : EngineeringRelation .Part .Component
  | assembledFrom : EngineeringRelation .Assembly .Part
  -- 故障関係
  | causesMalfunction : EngineeringRelation .Failure .Malfunction
  | affectsPart : EngineeringRelation .Failure .Part
  -- 修理関係
  | repairs : EngineeringRelation .Repair .Failure
  | restores : EngineeringRelation .Repair .Status
  | prevents : EngineeringRelation .Maintenance .Failure
  -- 操作関係
  | operates : EngineeringRelation .Operator .Machine
  | monitors : EngineeringRelation .Operator .Status
  -- 状態関係
  | hasStatus : EngineeringRelation .Machine .Status
  | restoresTo : EngineeringRelation .Restoration .Status

/-! ## 工学オントロジー -/

/-- 機械工学オントロジーの定義 -/
def EngineeringOntology : Ontology := {
  Concept := EngineeringConcept
  Relation := EngineeringRelation
  decEq := inferInstance
}

/-- 工学概念の全リスト -/
def allEngineeringConcepts : List EngineeringConcept := [
  .Machine, .Part, .Component, .Assembly,
  .Failure, .Malfunction, .Repair, .Maintenance,
  .Operator, .Status, .Restoration
]

instance : Finite EngineeringOntology where
  concepts := allEngineeringConcepts
  complete := fun c => by cases c <;> simp [allEngineeringConcepts]

/-! ## 基本領域からの展開写像 -/

/-- 基本領域 → 工学ドメインの展開写像 -/
def engineeringExpansion : ExpansionMap EngineeringOntology := {
  conceptMap := fun
    | .Container => .Machine       -- 容器 → 機械
    | .PartWhole => .Part          -- 部分-全体 → 部品
    | .Entity => .Operator         -- 実体 → オペレーター
    | .Force => .Failure           -- 力（障害） → 故障
    | .Balance => .Status          -- 均衡 → 動作状態
    | .Enablement => .Repair       -- 可能化 → 修理
    | .Process => .Restoration     -- 過程 → 復旧
    | .State => .Status            -- 状態 → 動作状態
    | .Change => .Malfunction      -- 変化 → 不具合
    | .Path => .Maintenance        -- 経路 → メンテナンス（予防経路）
    | .Link => .Assembly           -- 結合 → アセンブリ
    | .Hierarchy => .Part          -- 階層 → 部品（部品階層）
  relationPreserve := fun r => by
    cases r
    all_goals (constructor <;> try rfl)
  name := "engineering"
}

/-! ## 工学ドメインの変形差分 -/

/-- 工学ドメイン固有の拡張 -/
def engineeringExtension : DomainExtension EngineeringOntology engineeringExpansion := {
  extraConcepts := [.Component]  -- コンポーネントは工学固有の精緻化
  constraints := []
  context := "機械工学的文脈：物理的構造、機械的因果関係"
}

/-! ## 工学オントロジーの公理 -/

/-- 工学オントロジーの公理的バージョン -/
def EngineeringAxiomaticOntology : AxiomaticOntology := {
  toOntology := EngineeringOntology
  axioms := [
    { statement := ∀ f : EngineeringConcept, f = .Failure → 
        ∃ r : EngineeringConcept, r = .Repair
      name := "RepairExists" },
    { statement := True  -- 簡略化
      name := "MaintenancePrevents" }
  ]
}

end OntologyAlignment.Examples
