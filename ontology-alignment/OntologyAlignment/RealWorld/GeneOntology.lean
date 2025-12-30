/-
  OntologyAlignment/RealWorld/GeneOntology.lean
  
  Gene Ontology (GO) の形式化
  
  GOは遺伝子機能の標準オントロジー：
  - 約45,000の用語
  - 3つのアスペクト：Molecular Function, Cellular Component, Biological Process
  - DAG（有向非巡回グラフ）構造
  
  ここでは核心的なサブセットをLean4で形式化する
-/

import OntologyAlignment.Basic
import OntologyAlignment.Foundation
import OntologyAlignment.ExpansionMap

namespace OntologyAlignment.RealWorld

/-! ## Gene Ontology 3つのアスペクト -/

/-- GOの3つのアスペクト（ルート） -/
inductive GOAspect where
  | MolecularFunction   -- GO:0003674 - 分子機能
  | CellularComponent   -- GO:0005575 - 細胞成分
  | BiologicalProcess   -- GO:0008150 - 生物学的過程
  deriving DecidableEq, Repr, BEq

/-! ## Molecular Function サブ階層 -/

/-- 分子機能の主要カテゴリ -/
inductive MolecularFunctionType where
  -- 触媒活性
  | CatalyticActivity         -- GO:0003824
  -- 結合活性
  | BindingActivity           -- GO:0005488
  -- 輸送活性
  | TransporterActivity       -- GO:0005215
  -- 転写調節活性
  | TranscriptionRegulator    -- GO:0140110
  -- シグナル受容体活性
  | SignalReceptorActivity    -- GO:0038023
  -- 構造分子活性
  | StructuralMolecule        -- GO:0005198
  -- 抗酸化活性
  | AntioxidantActivity       -- GO:0016209
  deriving DecidableEq, Repr, BEq

/-- 触媒活性の詳細 -/
inductive CatalyticActivityType where
  | Kinase                    -- キナーゼ活性
  | Phosphatase               -- ホスファターゼ活性
  | Protease                  -- プロテアーゼ活性
  | Oxidoreductase            -- 酸化還元酵素活性
  | Transferase               -- 転移酵素活性
  | Hydrolase                 -- 加水分解酵素活性
  | Ligase                    -- リガーゼ活性
  deriving DecidableEq, Repr, BEq

/-! ## Cellular Component サブ階層 -/

/-- 細胞成分の主要カテゴリ -/
inductive CellularComponentType where
  -- 細胞内
  | IntracellularOrganelle    -- GO:0043229
  -- 膜
  | Membrane                  -- GO:0016020
  -- 細胞質
  | Cytoplasm                 -- GO:0005737
  -- 核
  | Nucleus                   -- GO:0005634
  -- ミトコンドリア
  | Mitochondrion             -- GO:0005739
  -- 小胞体
  | EndoplasmicReticulum      -- GO:0005783
  -- ゴルジ体
  | GolgiApparatus            -- GO:0005794
  -- 細胞骨格
  | Cytoskeleton              -- GO:0005856
  -- 細胞外
  | ExtracellularRegion       -- GO:0005576
  -- タンパク質複合体
  | ProteinComplex            -- GO:0032991
  deriving DecidableEq, Repr, BEq

/-! ## Biological Process サブ階層 -/

/-- 生物学的過程の主要カテゴリ -/
inductive BiologicalProcessType where
  -- 代謝過程
  | MetabolicProcess          -- GO:0008152
  -- 細胞過程
  | CellularProcess           -- GO:0009987
  -- 生物学的調節
  | BiologicalRegulation      -- GO:0065007
  -- 応答（刺激への）
  | ResponseToStimulus        -- GO:0050896
  -- シグナル伝達
  | SignalTransduction        -- GO:0007165
  -- 発生過程
  | DevelopmentalProcess      -- GO:0032502
  -- 細胞周期
  | CellCycle                 -- GO:0007049
  -- 細胞死
  | CellDeath                 -- GO:0008219
  -- 免疫系過程
  | ImmuneSystemProcess       -- GO:0002376
  -- DNA修復
  | DNARepair                 -- GO:0006281
  -- 転写
  | Transcription             -- GO:0006351
  -- 翻訳
  | Translation               -- GO:0006412
  deriving DecidableEq, Repr, BEq

/-! ## Gene Ontology 概念（統合） -/

/-- GO概念の統合表現 -/
inductive GOConcept where
  -- アスペクト（ルート）
  | aspect : GOAspect → GOConcept
  -- 分子機能の詳細
  | molecularFunction : MolecularFunctionType → GOConcept
  -- 触媒活性の詳細
  | catalyticActivity : CatalyticActivityType → GOConcept
  -- 細胞成分の詳細
  | cellularComponent : CellularComponentType → GOConcept
  -- 生物学的過程の詳細
  | biologicalProcess : BiologicalProcessType → GOConcept
  -- 具体的なGO term例
  | ATPBinding                -- GO:0005524
  | ProteinKinaseActivity     -- GO:0004672
  | Apoptosis                 -- GO:0006915
  | CellProliferation         -- GO:0008283
  | GlucoseMetabolism         -- GO:0006006
  | DNAReplication            -- GO:0006260
  | ProteinFolding            -- GO:0006457
  deriving DecidableEq, Repr, BEq

instance : HasLabel GOConcept where
  label := fun
    | .aspect a => s!"GO:{repr a}"
    | .molecularFunction mf => s!"MF:{repr mf}"
    | .catalyticActivity ca => s!"CA:{repr ca}"
    | .cellularComponent cc => s!"CC:{repr cc}"
    | .biologicalProcess bp => s!"BP:{repr bp}"
    | .ATPBinding => "ATPBinding"
    | .ProteinKinaseActivity => "ProteinKinaseActivity"
    | .Apoptosis => "Apoptosis"
    | .CellProliferation => "CellProliferation"
    | .GlucoseMetabolism => "GlucoseMetabolism"
    | .DNAReplication => "DNAReplication"
    | .ProteinFolding => "ProteinFolding"

/-! ## Gene Ontology 関係 -/

/-- GOの関係タイプ -/
inductive GORelation : GOConcept → GOConcept → Type where
  -- is_a（分類関係）
  | isA : GORelation child parent
  
  -- part_of（部分関係）
  | partOf : GORelation part whole
  
  -- has_part（逆方向）
  | hasPart : GORelation whole part
  
  -- regulates（調節関係）
  | regulates : GORelation regulator regulated
  
  -- positively_regulates
  | positivelyRegulates : GORelation regulator regulated
  
  -- negatively_regulates
  | negativelyRegulates : GORelation regulator regulated
  
  -- occurs_in（発生場所）
  | occursIn : GORelation 
      (.biologicalProcess _) (.cellularComponent _)
  
  -- enables（可能化：MF → BP）
  | enables : GORelation 
      (.molecularFunction _) (.biologicalProcess _)
  
  -- located_in（位置）
  | locatedIn : GORelation
      (.molecularFunction _) (.cellularComponent _)

  -- 具体的関係の例
  | kinaseIsCatalytic : GORelation 
      (.molecularFunction .CatalyticActivity) 
      (.aspect .MolecularFunction)
  | apoptosisIsCellDeath : GORelation 
      .Apoptosis 
      (.biologicalProcess .CellDeath)
  | metabolismInCytoplasm : GORelation
      (.biologicalProcess .MetabolicProcess)
      (.cellularComponent .Cytoplasm)

/-! ## Gene Ontology定義 -/

/-- Gene Ontology -/
def GeneOntology : Ontology := {
  Concept := GOConcept
  Relation := GORelation
  decEq := inferInstance
}

/-- GO概念の全リスト（サブセット） -/
def allGOConcepts : List GOConcept := [
  -- アスペクト
  .aspect .MolecularFunction,
  .aspect .CellularComponent,
  .aspect .BiologicalProcess,
  -- 分子機能
  .molecularFunction .CatalyticActivity,
  .molecularFunction .BindingActivity,
  .molecularFunction .TransporterActivity,
  .molecularFunction .TranscriptionRegulator,
  .molecularFunction .SignalReceptorActivity,
  -- 触媒活性
  .catalyticActivity .Kinase,
  .catalyticActivity .Phosphatase,
  .catalyticActivity .Protease,
  -- 細胞成分
  .cellularComponent .IntracellularOrganelle,
  .cellularComponent .Membrane,
  .cellularComponent .Cytoplasm,
  .cellularComponent .Nucleus,
  .cellularComponent .Mitochondrion,
  -- 生物学的過程
  .biologicalProcess .MetabolicProcess,
  .biologicalProcess .CellularProcess,
  .biologicalProcess .BiologicalRegulation,
  .biologicalProcess .ResponseToStimulus,
  .biologicalProcess .SignalTransduction,
  .biologicalProcess .CellCycle,
  .biologicalProcess .CellDeath,
  -- 具体的概念
  .ATPBinding,
  .ProteinKinaseActivity,
  .Apoptosis,
  .CellProliferation,
  .GlucoseMetabolism,
  .DNAReplication,
  .ProteinFolding
]

instance : Finite GeneOntology where
  concepts := allGOConcepts
  complete := fun c => by
    cases c <;> try simp [allGOConcepts]
    all_goals sorry

/-! ## 基本領域からの展開写像 -/

/-- 基本領域 → Gene Ontologyの展開写像
    
    メタファー的解釈：
    - Container → CellularComponent（細胞成分は「容器」）
    - Force → BiologicalRegulation（調節は「力」）
    - Process → BiologicalProcess（生物学的過程）
    - Enablement → MolecularFunction（分子機能は「可能化」）
    - State → CellularComponent（状態としての構造）
-/
def goExpansion : ExpansionMap GeneOntology := {
  conceptMap := fun
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
  relationPreserve := fun r => by
    cases r
    all_goals constructor
  name := "GeneOntology"
}

/-! ## GO固有の拡張（変形差分） -/

/-- Gene Ontologyの変形差分 -/
def goExtension : DomainExtension GeneOntology goExpansion := {
  extraConcepts := [
    .molecularFunction .CatalyticActivity,
    .catalyticActivity .Kinase,
    .Apoptosis,
    .GlucoseMetabolism,
    .DNAReplication
  ]
  constraints := []
  context := "分子生物学的文脈：遺伝子産物の機能、細胞内局在、生化学的過程"
}

/-! ## GO内部のアライメント補助定理 -/

/-- 触媒活性は分子機能の一種 -/
theorem catalytic_is_molecular_function :
    GORelation.isA 
      (.molecularFunction .CatalyticActivity) 
      (.aspect .MolecularFunction) :=
  .isA

/-- 代謝過程は生物学的過程の一種 -/
theorem metabolism_is_biological_process :
    GORelation.isA 
      (.biologicalProcess .MetabolicProcess) 
      (.aspect .BiologicalProcess) :=
  .isA

/-- 分子機能は生物学的過程を可能にする -/
theorem mf_enables_bp :
    ∀ (mf : MolecularFunctionType) (bp : BiologicalProcessType),
    GORelation.enables (.molecularFunction mf) (.biologicalProcess bp) :=
  fun _ _ => .enables

end OntologyAlignment.RealWorld
