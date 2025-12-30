/-
  OntologyAlignment/Basic.lean
  
  オントロジーの基本構造を定義する
  
  核心的アイデア：
  - オントロジーは概念の集合と関係の集合で構成される
  - 依存型を用いて関係を型付けする
-/

namespace OntologyAlignment

/-- オントロジーの基本構造 -/
structure Ontology where
  /-- 概念の型 -/
  Concept : Type
  /-- 関係の型（2つの概念間の関係を型として表現） -/
  Relation : Concept → Concept → Type
  /-- 概念の等価性判定が決定可能 -/
  decEq : DecidableEq Concept

/-- オントロジーに対するDecidableEqインスタンス -/
instance (O : Ontology) : DecidableEq O.Concept := O.decEq

/-- 概念間の接続可能性（推移閉包） -/
inductive Connected {O : Ontology} : O.Concept → O.Concept → Prop where
  | direct : O.Relation c₁ c₂ → Connected c₁ c₂
  | trans : Connected c₁ c₂ → Connected c₂ c₃ → Connected c₁ c₃

/-- 概念のプロパティ -/
structure ConceptProperty (O : Ontology) where
  property : O.Concept → Prop
  name : String

/-- オントロジーの公理 -/
structure OntologyAxiom (O : Ontology) where
  statement : Prop
  name : String

/-- 公理付きオントロジー -/
structure AxiomaticOntology extends Ontology where
  axioms : List (OntologyAxiom toOntology)

/-- オントロジー間の準同型写像 -/
structure OntologyHomomorphism (O₁ O₂ : Ontology) where
  /-- 概念の写像 -/
  conceptMap : O₁.Concept → O₂.Concept
  /-- 関係の保存（証明項として） -/
  relationPreserve : ∀ {c₁ c₂ : O₁.Concept}, 
    O₁.Relation c₁ c₂ → O₂.Relation (conceptMap c₁) (conceptMap c₂)

/-- 準同型写像の合成 -/
def OntologyHomomorphism.comp 
    {O₁ O₂ O₃ : Ontology}
    (f : OntologyHomomorphism O₁ O₂)
    (g : OntologyHomomorphism O₂ O₃) : 
    OntologyHomomorphism O₁ O₃ := {
  conceptMap := g.conceptMap ∘ f.conceptMap
  relationPreserve := fun r => g.relationPreserve (f.relationPreserve r)
}

/-- 恒等準同型 -/
def OntologyHomomorphism.id (O : Ontology) : OntologyHomomorphism O O := {
  conceptMap := id
  relationPreserve := id
}

/-- 概念のラベル（文字列表現） -/
class HasLabel (α : Type) where
  label : α → String

/-- オントロジーの概念数 -/
class Finite (O : Ontology) where
  concepts : List O.Concept
  complete : ∀ c : O.Concept, c ∈ concepts

end OntologyAlignment
