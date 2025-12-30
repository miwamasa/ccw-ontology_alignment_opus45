/-
  OntologyAlignment/RealWorld/BiomedicalFoundation.lean
  
  生物医学ドメイン向けの拡張基本領域オントロジー
  
  標準的なFoundational Ontologyとの関係：
  - BFO (Basic Formal Ontology)：OBO Foundryの上位オントロジー
  - OGMS (Ontology for General Medical Science)：医学の上位オントロジー
  - RO (Relations Ontology)：関係の標準オントロジー
  
  これらとイメージスキーマを統合した拡張基本領域を定義
-/

import OntologyAlignment.Foundation
import OntologyAlignment.Basic

namespace OntologyAlignment.RealWorld

open OntologyAlignment

/-! ## BFO (Basic Formal Ontology) との対応 -/

/-- BFOの基本分類：Continuant vs Occurrent -/
inductive BFOCategory where
  | Continuant    -- 持続体（時間を通じて存在）
  | Occurrent     -- 生起体（時間的に展開）
  deriving DecidableEq, Repr

/-- BFO Continuantのサブカテゴリ -/
inductive ContinuantType where
  | IndependentContinuant   -- 独立持続体（物質的実体）
  | DependentContinuant     -- 依存持続体（性質、役割）
  | SpatialRegion           -- 空間領域
  deriving DecidableEq, Repr

/-- BFO Occurrentのサブカテゴリ -/
inductive OccurrentType where
  | Process                 -- 過程
  | ProcessBoundary         -- 過程境界（瞬間）
  | TemporalRegion          -- 時間領域
  deriving DecidableEq, Repr

/-! ## 生物医学拡張基本概念 -/

/-- 生物医学向け拡張基本概念
    
    イメージスキーマ + BFOカテゴリ + 医学特有概念
-/
inductive BiomedicalFoundationConcept where
  -- === イメージスキーマ（元の基本領域） ===
  | Container
  | Path
  | Link
  | Force
  | Balance
  | Enablement
  | Entity
  | PartWhole
  | Hierarchy
  | Process
  | State
  | Change
  
  -- === BFO拡張 ===
  | Continuant              -- BFO: 持続体
  | Occurrent               -- BFO: 生起体
  | Quality                 -- BFO: 性質
  | Role                    -- BFO: 役割
  | Function                -- BFO: 機能
  | Disposition             -- BFO: 傾性
  
  -- === 医学特有（OGMS準拠） ===
  | Disease                 -- OGMS: 疾患傾性
  | Disorder                -- OGMS: 障害（病的状態）
  | PathologicalProcess     -- OGMS: 病理過程
  | HealthcareProcess       -- 医療過程
  | BiologicalAttribute     -- 生物学的属性
  | ClinicalPhenotype       -- 臨床表現型
  
  -- === 分子生物学特有 ===
  | MolecularEntity         -- 分子実体
  | MolecularProcess        -- 分子過程
  | MolecularFunction       -- 分子機能
  | CellularLocation        -- 細胞内局在
  deriving DecidableEq, Repr, BEq

instance : HasLabel BiomedicalFoundationConcept where
  label := fun
    -- イメージスキーマ
    | .Container => "Container"
    | .Path => "Path"
    | .Link => "Link"
    | .Force => "Force"
    | .Balance => "Balance"
    | .Enablement => "Enablement"
    | .Entity => "Entity"
    | .PartWhole => "PartWhole"
    | .Hierarchy => "Hierarchy"
    | .Process => "Process"
    | .State => "State"
    | .Change => "Change"
    -- BFO
    | .Continuant => "BFO:Continuant"
    | .Occurrent => "BFO:Occurrent"
    | .Quality => "BFO:Quality"
    | .Role => "BFO:Role"
    | .Function => "BFO:Function"
    | .Disposition => "BFO:Disposition"
    -- OGMS
    | .Disease => "OGMS:Disease"
    | .Disorder => "OGMS:Disorder"
    | .PathologicalProcess => "OGMS:PathologicalProcess"
    | .HealthcareProcess => "OGMS:HealthcareProcess"
    | .BiologicalAttribute => "BiologicalAttribute"
    | .ClinicalPhenotype => "ClinicalPhenotype"
    -- 分子生物学
    | .MolecularEntity => "MolecularEntity"
    | .MolecularProcess => "MolecularProcess"
    | .MolecularFunction => "MolecularFunction"
    | .CellularLocation => "CellularLocation"

/-! ## 生物医学基本領域の関係 -/

/-- 生物医学基本領域の関係 -/
inductive BiomedicalFoundationRelation : 
    BiomedicalFoundationConcept → BiomedicalFoundationConcept → Type where
  -- 包含関係（Container系）
  | contains : BiomedicalFoundationRelation .Container .Entity
  | locatedIn : BiomedicalFoundationRelation .Entity .Container
  | cellularLocatedIn : BiomedicalFoundationRelation .MolecularEntity .CellularLocation
  
  -- 部分-全体関係
  | partOf : BiomedicalFoundationRelation .PartWhole .Entity
  | hasPart : BiomedicalFoundationRelation .Entity .PartWhole
  
  -- 過程関係
  | participatesIn : BiomedicalFoundationRelation .Entity .Process
  | hasParticipant : BiomedicalFoundationRelation .Process .Entity
  | precedes : BiomedicalFoundationRelation .Process .Process
  
  -- 因果関係
  | causes : BiomedicalFoundationRelation .Force .Change
  | enables : BiomedicalFoundationRelation .Enablement .Process
  | regulates : BiomedicalFoundationRelation .Force .Process
  
  -- 性質・傾性関係
  | hasQuality : BiomedicalFoundationRelation .Entity .Quality
  | hasDisposition : BiomedicalFoundationRelation .Entity .Disposition
  | realizesDisposition : BiomedicalFoundationRelation .Process .Disposition
  
  -- BFO分類関係
  | continuantIsA : BiomedicalFoundationRelation .Entity .Continuant
  | occurrentIsA : BiomedicalFoundationRelation .Process .Occurrent
  
  -- 医学特有関係
  | hasPathology : BiomedicalFoundationRelation .Disease .PathologicalProcess
  | manifestsAs : BiomedicalFoundationRelation .Disorder .ClinicalPhenotype
  | treatedBy : BiomedicalFoundationRelation .Disorder .HealthcareProcess
  
  -- 分子生物学関係
  | hasMolecularFunction : BiomedicalFoundationRelation .MolecularEntity .MolecularFunction
  | involvedIn : BiomedicalFoundationRelation .MolecularFunction .MolecularProcess

/-! ## 生物医学基本領域オントロジー -/

/-- 生物医学基本領域オントロジー -/
def BiomedicalFoundationOntology : Ontology := {
  Concept := BiomedicalFoundationConcept
  Relation := BiomedicalFoundationRelation
  decEq := inferInstance
}

/-- 全概念リスト -/
def allBiomedicalFoundationConcepts : List BiomedicalFoundationConcept := [
  -- イメージスキーマ
  .Container, .Path, .Link, .Force, .Balance, .Enablement,
  .Entity, .PartWhole, .Hierarchy, .Process, .State, .Change,
  -- BFO
  .Continuant, .Occurrent, .Quality, .Role, .Function, .Disposition,
  -- OGMS
  .Disease, .Disorder, .PathologicalProcess, .HealthcareProcess,
  .BiologicalAttribute, .ClinicalPhenotype,
  -- 分子生物学
  .MolecularEntity, .MolecularProcess, .MolecularFunction, .CellularLocation
]

instance : Finite BiomedicalFoundationOntology where
  concepts := allBiomedicalFoundationConcepts
  complete := fun c => by
    cases c <;> simp [allBiomedicalFoundationConcepts]

/-! ## イメージスキーマとの対応 -/

/-- 元のFoundationConceptへの写像（精緻化の逆） -/
def toBasicFoundation : BiomedicalFoundationConcept → Option FoundationConcept
  | .Container => some .Container
  | .Path => some .Path
  | .Link => some .Link
  | .Force => some .Force
  | .Balance => some .Balance
  | .Enablement => some .Enablement
  | .Entity => some .Entity
  | .PartWhole => some .PartWhole
  | .Hierarchy => some .Hierarchy
  | .Process => some .Process
  | .State => some .State
  | .Change => some .Change
  | _ => none  -- 拡張概念は対応なし

/-- イメージスキーマの精緻化としての拡張概念 -/
def isRefinementOf : BiomedicalFoundationConcept → FoundationConcept → Bool
  | .Continuant, .Entity => true
  | .Occurrent, .Process => true
  | .Quality, .State => true
  | .Function, .Enablement => true
  | .Disposition, .State => true
  | .Disease, .Force => true
  | .Disorder, .State => true
  | .PathologicalProcess, .Process => true
  | .HealthcareProcess, .Process => true
  | .MolecularEntity, .Entity => true
  | .MolecularProcess, .Process => true
  | .MolecularFunction, .Enablement => true
  | .CellularLocation, .Container => true
  | _, _ => false

/-! ## SNOMED CT への拡張展開写像 -/

/-- 拡張基本領域 → SNOMED CTの展開写像 -/
def extendedSnomedExpansion : OntologyHomomorphism BiomedicalFoundationOntology SNOMEDOntology := {
  conceptMap := fun
    -- イメージスキーマ系
    | .Container => .hierarchy .BodyStructure
    | .PartWhole => .bodyStructure .Organ
    | .Entity => .hierarchy .Organism
    | .Force => .clinicalFinding .Disease
    | .Balance => .hierarchy .ObservableEntity
    | .Enablement => .procedure .TherapeuticProcedure
    | .Process => .hierarchy .Procedure
    | .State => .clinicalFinding .Finding
    | .Change => .clinicalFinding .Symptom
    | .Path => .procedure .DiagnosticProcedure
    | .Link => .bodyStructure .Tissue
    | .Hierarchy => .hierarchy .ClinicalFinding
    -- BFO系
    | .Continuant => .hierarchy .BodyStructure
    | .Occurrent => .hierarchy .Event
    | .Quality => .hierarchy .ObservableEntity
    | .Role => .hierarchy .SocialContext
    | .Function => .hierarchy .ObservableEntity
    | .Disposition => .clinicalFinding .Finding
    -- OGMS系（直接対応）
    | .Disease => .clinicalFinding .Disease
    | .Disorder => .clinicalFinding .Abnormality
    | .PathologicalProcess => .hierarchy .Event
    | .HealthcareProcess => .hierarchy .Procedure
    | .BiologicalAttribute => .hierarchy .ObservableEntity
    | .ClinicalPhenotype => .clinicalFinding .Sign
    -- 分子生物学系
    | .MolecularEntity => .hierarchy .Substance
    | .MolecularProcess => .hierarchy .Event
    | .MolecularFunction => .hierarchy .ObservableEntity
    | .CellularLocation => .bodyStructure .Cell
  relationPreserve := fun r => by
    cases r
    all_goals constructor
}

/-! ## Gene Ontology への拡張展開写像 -/

/-- 拡張基本領域 → Gene Ontologyの展開写像 -/
def extendedGOExpansion : OntologyHomomorphism BiomedicalFoundationOntology GeneOntology := {
  conceptMap := fun
    -- イメージスキーマ系
    | .Container => .cellularComponent .IntracellularOrganelle
    | .PartWhole => .cellularComponent .ProteinComplex
    | .Entity => .aspect .CellularComponent
    | .Force => .biologicalProcess .BiologicalRegulation
    | .Balance => .biologicalProcess .CellularProcess
    | .Enablement => .aspect .MolecularFunction
    | .Process => .aspect .BiologicalProcess
    | .State => .cellularComponent .Cytoplasm
    | .Change => .biologicalProcess .ResponseToStimulus
    | .Path => .biologicalProcess .SignalTransduction
    | .Link => .cellularComponent .Membrane
    | .Hierarchy => .biologicalProcess .DevelopmentalProcess
    -- BFO系
    | .Continuant => .aspect .CellularComponent
    | .Occurrent => .aspect .BiologicalProcess
    | .Quality => .biologicalProcess .CellularProcess
    | .Role => .biologicalProcess .BiologicalRegulation
    | .Function => .aspect .MolecularFunction
    | .Disposition => .biologicalProcess .ResponseToStimulus
    -- OGMS系
    | .Disease => .biologicalProcess .CellDeath  -- 病理 → 細胞死
    | .Disorder => .biologicalProcess .CellularProcess
    | .PathologicalProcess => .biologicalProcess .CellDeath
    | .HealthcareProcess => .aspect .BiologicalProcess
    | .BiologicalAttribute => .biologicalProcess .CellularProcess
    | .ClinicalPhenotype => .biologicalProcess .ResponseToStimulus
    -- 分子生物学系（直接対応）
    | .MolecularEntity => .aspect .CellularComponent
    | .MolecularProcess => .aspect .BiologicalProcess
    | .MolecularFunction => .aspect .MolecularFunction
    | .CellularLocation => .cellularComponent .IntracellularOrganelle
  relationPreserve := fun r => by
    cases r
    all_goals constructor
}

/-! ## 精緻化されたアライメント -/

/-- 拡張基本領域を使ったより精密なアライメント -/
structure RefinedAlignment 
    (O_A O_B : Ontology)
    (φ_A : OntologyHomomorphism BiomedicalFoundationOntology O_A)
    (φ_B : OntologyHomomorphism BiomedicalFoundationOntology O_B)
    (c_A : O_A.Concept)
    (c_B : O_B.Concept) where
  /-- 拡張基本概念（より精密なwiness） -/
  biomedicalWitness : BiomedicalFoundationConcept
  /-- 元のイメージスキーマ（あれば） -/
  basicWitness : Option FoundationConcept := toBasicFoundation biomedicalWitness
  /-- SNOMED CT側の対応証明 -/
  fromA : φ_A.conceptMap biomedicalWitness = c_A
  /-- GO側の対応証明 -/
  fromB : φ_B.conceptMap biomedicalWitness = c_B
  /-- BFOカテゴリ -/
  bfoCategory : BFOCategory := 
    if biomedicalWitness = .Continuant ∨ biomedicalWitness = .Entity then .Continuant
    else .Occurrent

end OntologyAlignment.RealWorld
