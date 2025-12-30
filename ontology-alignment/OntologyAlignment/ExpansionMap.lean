/-
  OntologyAlignment/ExpansionMap.lean
  
  展開写像（Expansion Map）の定義
  
  メタファー理論における「基本領域→目標領域」の写像を形式化
  
  重要な性質：
  1. 構造保存性：関係構造が保存される
  2. 精緻化許容：概念の細分化を許す
  3. 拡張許容：ドメイン固有概念の追加を許す
-/

import OntologyAlignment.Basic
import OntologyAlignment.Foundation

namespace OntologyAlignment

/-! ## 展開写像の定義 -/

/-- 展開写像：基本領域からドメインオントロジーへの写像 -/
structure ExpansionMap (O_D : Ontology) extends 
    OntologyHomomorphism FoundationOntology O_D where
  /-- 写像の名前（デバッグ用） -/
  name : String := "unnamed"

/-! ## ドメイン固有拡張（変形差分 Δ） -/

/-- 変形差分：展開時に追加されるドメイン固有の情報 -/
structure DomainExtension (O_D : Ontology) (φ : ExpansionMap O_D) where
  /-- 追加された概念（基本領域にない概念） -/
  extraConcepts : List O_D.Concept
  /-- ドメイン固有の制約 -/
  constraints : List Prop
  /-- コンテキスト情報（自然言語での説明） -/
  context : String

/-- 概念がφの像に含まれるか判定 -/
def isInImage (O_D : Ontology) (φ : ExpansionMap O_D) (c : O_D.Concept) : Prop :=
  ∃ f : FoundationConcept, φ.conceptMap f = c

/-- 概念が拡張部分に含まれるか判定 -/
def isExtension (O_D : Ontology) (φ : ExpansionMap O_D) 
    (Δ : DomainExtension O_D φ) (c : O_D.Concept) : Prop :=
  c ∈ Δ.extraConcepts

/-! ## 逆写像（疑似逆） -/

/-- 逆写像の結果：基本概念 または 拡張概念 -/
inductive InverseResult (O_D : Ontology) (φ : ExpansionMap O_D) where
  | foundation : FoundationConcept → InverseResult O_D φ
  | extension : O_D.Concept → InverseResult O_D φ
  | unknown : InverseResult O_D φ

/-- 逆写像の計算（疑似逆写像） -/
def computeInverse (O_D : Ontology) [DecidableEq O_D.Concept]
    (φ : ExpansionMap O_D) (c : O_D.Concept) : InverseResult O_D φ :=
  let candidates := allFoundationConcepts.filter fun f => φ.conceptMap f = c
  match candidates with
  | f :: _ => .foundation f
  | [] => .extension c

/-! ## 展開写像の性質 -/

/-- 写像が単射か -/
def ExpansionMap.isInjective (O_D : Ontology) (φ : ExpansionMap O_D) : Prop :=
  ∀ f₁ f₂ : FoundationConcept, φ.conceptMap f₁ = φ.conceptMap f₂ → f₁ = f₂

/-- 写像が全射か -/
def ExpansionMap.isSurjective (O_D : Ontology) [Finite O_D] (φ : ExpansionMap O_D) : Prop :=
  ∀ c : O_D.Concept, ∃ f : FoundationConcept, φ.conceptMap f = c

/-- 展開の「深さ」：基本概念からの精緻化度合い -/
structure ExpansionDepth (O_D : Ontology) (φ : ExpansionMap O_D) (c : O_D.Concept) where
  /-- 元となる基本概念 -/
  source : FoundationConcept
  /-- 精緻化の段階数 -/
  depth : Nat
  /-- 正当性証明 -/
  valid : φ.conceptMap source = c ∨ depth > 0

/-! ## 展開写像の構成補助 -/

/-- 部分的な展開写像を定義するためのビルダー -/
structure PartialExpansionMap (O_D : Ontology) where
  /-- 定義された概念写像 -/
  mappings : List (FoundationConcept × O_D.Concept)
  /-- デフォルト概念（未定義の場合） -/
  default : O_D.Concept

/-- 部分写像から完全な写像を構築 -/
def PartialExpansionMap.toExpansionMap 
    {O_D : Ontology} [DecidableEq O_D.Concept]
    (partial : PartialExpansionMap O_D)
    (relPreserve : ∀ {c₁ c₂ : FoundationConcept}, 
      FoundationRelation c₁ c₂ → 
      O_D.Relation (partial.lookup c₁) (partial.lookup c₂)) :
    ExpansionMap O_D := {
  conceptMap := partial.lookup
  relationPreserve := relPreserve
}
where
  lookup (f : FoundationConcept) : O_D.Concept :=
    match partial.mappings.find? (fun p => p.1 == f) with
    | some (_, c) => c
    | none => partial.default

/-! ## 展開の合成 -/

/-- 2段階展開：基本→中間→ドメイン -/
structure TwoStageExpansion (O_mid O_D : Ontology) where
  /-- 第1段階：基本→中間 -/
  stage1 : ExpansionMap O_mid
  /-- 第2段階：中間→ドメイン -/
  stage2 : OntologyHomomorphism O_mid O_D
  /-- 合成された展開 -/
  composed : ExpansionMap O_D := {
    conceptMap := stage2.conceptMap ∘ stage1.conceptMap
    relationPreserve := fun r => stage2.relationPreserve (stage1.relationPreserve r)
    name := s!"{stage1.name} ∘ {stage2.conceptMap}"
  }

end OntologyAlignment
