/-
  OntologyAlignment/Foundation.lean
  
  基本領域オントロジー（Foundation Ontology）の定義
  
  Lakoff & Johnsonのイメージスキーマ理論に基づく：
  - 空間スキーマ（Container, Path, Link）
  - 力学スキーマ（Force, Balance, Enablement）
  - 存在スキーマ（PartWhole, Hierarchy, Cycle）
  
  これらは人間の身体的経験に根ざした概念構造であり、
  すべてのドメインオントロジーの「共通基盤」として機能する
-/

import OntologyAlignment.Basic

namespace OntologyAlignment

/-! ## 基本概念（イメージスキーマ） -/

/-- 基本領域の概念（イメージスキーマ） -/
inductive FoundationConcept where
  -- 空間スキーマ
  | Container    -- 容器（内部/外部/境界）
  | Path         -- 経路（始点/終点/軌跡）
  | Link         -- 結合（接続関係）
  -- 力学スキーマ
  | Force        -- 力（作用/反作用）
  | Balance      -- 均衡（安定/不安定）
  | Enablement   -- 可能化（条件/結果）
  -- 存在スキーマ
  | Entity       -- 実体（存在するもの）
  | PartWhole    -- 部分-全体
  | Hierarchy    -- 階層（上位/下位）
  | Process      -- 過程（時間的展開）
  | State        -- 状態（静的性質）
  | Change       -- 変化（状態遷移）
  deriving DecidableEq, Repr, BEq

/-- 基本概念のラベル -/
instance : HasLabel FoundationConcept where
  label := fun
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

/-! ## 基本関係 -/

/-- 基本領域の関係 -/
inductive FoundationRelation : FoundationConcept → FoundationConcept → Type where
  -- 包含関係
  | contains : FoundationRelation .Container .Entity
  | containedIn : FoundationRelation .Entity .Container
  
  -- 経路関係
  | traverses : FoundationRelation .Path .Container
  | connectsTo : FoundationRelation .Path .Entity
  
  -- 部分-全体関係
  | partOf : FoundationRelation .PartWhole .Entity
  | hasPart : FoundationRelation .Entity .PartWhole
  
  -- 階層関係
  | above : FoundationRelation .Hierarchy .Hierarchy
  | below : FoundationRelation .Hierarchy .Hierarchy
  
  -- 因果関係
  | causes : FoundationRelation .Force .Change
  | enables : FoundationRelation .Enablement .Process
  | prevents : FoundationRelation .Force .Process
  
  -- 状態関係
  | hasState : FoundationRelation .Entity .State
  | inProcess : FoundationRelation .Entity .Process
  | changesTo : FoundationRelation .State .State
  
  -- 均衡関係
  | maintains : FoundationRelation .Balance .State
  | disrupts : FoundationRelation .Force .Balance

/-! ## 基本領域オントロジー -/

/-- 基本領域オントロジーの定義 -/
def FoundationOntology : Ontology := {
  Concept := FoundationConcept
  Relation := FoundationRelation
  decEq := inferInstance
}

/-- 基本領域の全概念リスト -/
def allFoundationConcepts : List FoundationConcept := [
  .Container, .Path, .Link,
  .Force, .Balance, .Enablement,
  .Entity, .PartWhole, .Hierarchy,
  .Process, .State, .Change
]

instance : Finite FoundationOntology where
  concepts := allFoundationConcepts
  complete := fun c => by
    cases c <;> simp [allFoundationConcepts]

/-! ## スキーマカテゴリ -/

/-- スキーマのカテゴリ分類 -/
inductive SchemaCategory where
  | Spatial    -- 空間的
  | Dynamic    -- 力学的
  | Existential -- 存在的
  deriving DecidableEq, Repr

/-- 概念のカテゴリ判定 -/
def FoundationConcept.category : FoundationConcept → SchemaCategory
  | .Container | .Path | .Link => .Spatial
  | .Force | .Balance | .Enablement => .Dynamic
  | .Entity | .PartWhole | .Hierarchy | .Process | .State | .Change => .Existential

/-! ## 不変原則（Invariance Principle） -/

/-- Lakoffの不変原則を型として表現
    メタファー写像はイメージスキーマ構造を保存しなければならない -/
structure InvariancePrinciple (O_D : Ontology) 
    (φ : OntologyHomomorphism FoundationOntology O_D) where
  /-- 空間構造の保存 -/
  spatialPreserved : ∀ c : FoundationConcept, 
    c.category = .Spatial → 
    ∃ (prop : O_D.Concept → Prop), prop (φ.conceptMap c)
  
  /-- 階層構造の保存 -/
  hierarchyPreserved : ∀ c₁ c₂ : FoundationConcept,
    FoundationRelation.above = (FoundationRelation.above : FoundationRelation .Hierarchy .Hierarchy) →
    Connected (O := O_D) (φ.conceptMap c₁) (φ.conceptMap c₂) ∨ 
    Connected (O := O_D) (φ.conceptMap c₂) (φ.conceptMap c₁) ∨
    φ.conceptMap c₁ = φ.conceptMap c₂

/-- 不変原則を満たす写像は「正当なメタファー」 -/
def ValidMetaphor (O_D : Ontology) (φ : OntologyHomomorphism FoundationOntology O_D) : Prop :=
  Nonempty (InvariancePrinciple O_D φ)

end OntologyAlignment
