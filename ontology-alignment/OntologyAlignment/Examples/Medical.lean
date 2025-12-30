/-
  OntologyAlignment/Examples/Medical.lean
  
  医療ドメインオントロジーの定義
  
  人体を「システム」として捉えるメタファーに基づく：
  - Body ← Container
  - Organ ← PartWhole  
  - Disease ← Force（dysfunction）
  - Treatment ← Enablement
-/

import OntologyAlignment.ExpansionMap
import OntologyAlignment.Alignment

namespace OntologyAlignment.Examples

/-! ## 医療概念 -/

/-- 医療ドメインの概念 -/
inductive MedicalConcept where
  | Body         -- 身体（全体）
  | Organ        -- 器官
  | Cell         -- 細胞
  | Tissue       -- 組織
  | Disease      -- 疾病
  | Symptom      -- 症状
  | Treatment    -- 治療
  | Diagnosis    -- 診断
  | Patient      -- 患者
  | HealthState  -- 健康状態
  | Recovery     -- 回復
  deriving DecidableEq, Repr, BEq

instance : HasLabel MedicalConcept where
  label := fun
    | .Body => "Body"
    | .Organ => "Organ"
    | .Cell => "Cell"
    | .Tissue => "Tissue"
    | .Disease => "Disease"
    | .Symptom => "Symptom"
    | .Treatment => "Treatment"
    | .Diagnosis => "Diagnosis"
    | .Patient => "Patient"
    | .HealthState => "HealthState"
    | .Recovery => "Recovery"

/-! ## 医療関係 -/

/-- 医療ドメインの関係 -/
inductive MedicalRelation : MedicalConcept → MedicalConcept → Type where
  -- 構造関係
  | hasOrgan : MedicalRelation .Body .Organ
  | hasTissue : MedicalRelation .Organ .Tissue
  | hasCell : MedicalRelation .Tissue .Cell
  -- 病理関係
  | causesSymprom : MedicalRelation .Disease .Symptom
  | affectsOrgan : MedicalRelation .Disease .Organ
  -- 治療関係
  | treats : MedicalRelation .Treatment .Disease
  | restores : MedicalRelation .Treatment .HealthState
  -- 診断関係
  | diagnoses : MedicalRelation .Diagnosis .Disease
  | basedOnSymptom : MedicalRelation .Diagnosis .Symptom
  -- 状態関係
  | hasState : MedicalRelation .Patient .HealthState
  | undergoes : MedicalRelation .Patient .Treatment
  | recoversTo : MedicalRelation .Recovery .HealthState

/-! ## 医療オントロジー -/

/-- 医療オントロジーの定義 -/
def MedicalOntology : Ontology := {
  Concept := MedicalConcept
  Relation := MedicalRelation
  decEq := inferInstance
}

/-- 医療概念の全リスト -/
def allMedicalConcepts : List MedicalConcept := [
  .Body, .Organ, .Cell, .Tissue,
  .Disease, .Symptom, .Treatment, .Diagnosis,
  .Patient, .HealthState, .Recovery
]

instance : Finite MedicalOntology where
  concepts := allMedicalConcepts
  complete := fun c => by cases c <;> simp [allMedicalConcepts]

/-! ## 基本領域からの展開写像 -/

/-- 基本領域 → 医療ドメインの展開写像 -/
def medicalExpansion : ExpansionMap MedicalOntology := {
  conceptMap := fun
    | .Container => .Body       -- 容器 → 身体
    | .PartWhole => .Organ      -- 部分-全体 → 器官
    | .Entity => .Patient       -- 実体 → 患者
    | .Force => .Disease        -- 力（障害） → 疾病
    | .Balance => .HealthState  -- 均衡 → 健康状態
    | .Enablement => .Treatment -- 可能化 → 治療
    | .Process => .Recovery     -- 過程 → 回復
    | .State => .HealthState    -- 状態 → 健康状態
    | .Change => .Symptom       -- 変化 → 症状
    | .Path => .Diagnosis       -- 経路 → 診断（思考の経路）
    | .Link => .Tissue          -- 結合 → 組織
    | .Hierarchy => .Organ      -- 階層 → 器官（器官系統）
  relationPreserve := fun r => by
    cases r
    -- 各関係の保存を証明
    all_goals (constructor <;> try rfl)
  name := "medical"
}

/-! ## 医療ドメインの変形差分 -/

/-- 医療ドメイン固有の拡張 -/
def medicalExtension : DomainExtension MedicalOntology medicalExpansion := {
  extraConcepts := [.Cell]  -- 細胞は基本領域にない医療固有概念
  constraints := []
  context := "生物医学的文脈：細胞レベルの構造、病理学的因果関係"
}

/-! ## 医療オントロジーの公理 -/

/-- 医療オントロジーの公理的バージョン -/
def MedicalAxiomaticOntology : AxiomaticOntology := {
  toOntology := MedicalOntology
  axioms := [
    { statement := ∀ d : MedicalConcept, d = .Disease → 
        ∃ t : MedicalConcept, t = .Treatment
      name := "TreatmentExists" },
    { statement := True  -- 簡略化：実際には複雑な公理
      name := "RecoveryPossible" }
  ]
}

end OntologyAlignment.Examples
