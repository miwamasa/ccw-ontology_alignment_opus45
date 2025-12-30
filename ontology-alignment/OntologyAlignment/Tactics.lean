/-
  OntologyAlignment/Tactics.lean
  
  アライメント証明を自動化するタクティクス
  
  タクティクス = 証明探索アルゴリズム
  
  証明が見つかる ⟺ アライメントが存在する
  証明の構造 ⟺ アライメントの計算方法
-/

import OntologyAlignment.Alignment

namespace OntologyAlignment

/-! ## 基本タクティクス -/

/-- 基本概念を順番に試すタクティクス -/
macro "try_foundation" : tactic =>
  `(tactic| first 
    | exact .Container
    | exact .Path  
    | exact .Link
    | exact .Force
    | exact .Balance
    | exact .Enablement
    | exact .Entity
    | exact .PartWhole
    | exact .Hierarchy
    | exact .Process
    | exact .State
    | exact .Change)

/-- アライメント証明を自動で構築するタクティクス -/
macro "find_alignment" : tactic =>
  `(tactic|
    constructor
    · try_foundation
    · rfl
    · rfl)

/-- 複数の候補から最初に成功するものを選ぶ -/
macro "try_alignments" : tactic =>
  `(tactic| first
    | find_alignment
    | (constructor; exact .Entity; rfl; rfl)
    | (constructor; exact .Process; rfl; rfl)
    | (constructor; exact .State; rfl; rfl))

/-! ## 決定手続き -/

/-- アライメントの存在を決定する -/
def findFoundationWitness 
    {O_A O_B : Ontology} [DecidableEq O_A.Concept] [DecidableEq O_B.Concept]
    (φ_A : ExpansionMap O_A)
    (φ_B : ExpansionMap O_B)
    (c_A : O_A.Concept)
    (c_B : O_B.Concept) :
    Option FoundationConcept :=
  allFoundationConcepts.find? fun f =>
    φ_A.conceptMap f = c_A && φ_B.conceptMap f = c_B

/-- 決定手続きを使った証明タクティクス -/
macro "decide_alignment" φ_A:term φ_B:term c_A:term c_B:term : tactic =>
  `(tactic| 
    match findFoundationWitness $φ_A $φ_B $c_A $c_B with
    | some f => exact { foundationWitness := f, fromA := rfl, fromB := rfl }
    | none => fail "No alignment found")

/-! ## 全探索タクティクス -/

/-- すべての可能なアライメントを発見 -/
def discoverAllAlignments
    {O_A O_B : Ontology}
    (φ_A : ExpansionMap O_A)
    (φ_B : ExpansionMap O_B) :
    List (FoundationConcept × O_A.Concept × O_B.Concept) :=
  allFoundationConcepts.map fun f =>
    (f, φ_A.conceptMap f, φ_B.conceptMap f)

/-- アライメントマトリクスの構築 -/
structure AlignmentMatrix (O_A O_B : Ontology) where
  /-- 行（O_Aの概念） -/
  rows : List O_A.Concept
  /-- 列（O_Bの概念） -/
  cols : List O_B.Concept
  /-- スコア行列 -/
  scores : List (List Float)

/-- アライメントマトリクスの計算 -/
def computeAlignmentMatrix
    {O_A O_B : Ontology} 
    [Finite O_A] [Finite O_B]
    [DecidableEq O_A.Concept] [DecidableEq O_B.Concept]
    (φ_A : ExpansionMap O_A)
    (φ_B : ExpansionMap O_B) :
    AlignmentMatrix O_A O_B := {
  rows := Finite.concepts
  cols := Finite.concepts
  scores := Finite.concepts.map fun c_A =>
    Finite.concepts.map fun c_B =>
      match findFoundationWitness φ_A φ_B c_A c_B with
      | some _ => 1.0
      | none => 0.0
}

/-! ## 証明ログ付きタクティクス -/

/-- 証明過程を記録する構造 -/
structure ProofTrace where
  /-- 試行した基本概念 -/
  attempts : List FoundationConcept
  /-- 成功した基本概念（あれば） -/
  success : Option FoundationConcept
  /-- 試行回数 -/
  numAttempts : Nat := attempts.length

/-- 証明探索とログの同時実行 -/
def findAlignmentWithTrace
    {O_A O_B : Ontology} [DecidableEq O_A.Concept] [DecidableEq O_B.Concept]
    (φ_A : ExpansionMap O_A)
    (φ_B : ExpansionMap O_B)
    (c_A : O_A.Concept)
    (c_B : O_B.Concept) :
    ProofTrace × Option (ConceptAlignment O_A O_B φ_A φ_B c_A c_B) :=
  let rec go (remaining : List FoundationConcept) (tried : List FoundationConcept) :
      ProofTrace × Option (ConceptAlignment O_A O_B φ_A φ_B c_A c_B) :=
    match remaining with
    | [] => ({ attempts := tried.reverse, success := none }, none)
    | f :: rest =>
      if h₁ : φ_A.conceptMap f = c_A then
        if h₂ : φ_B.conceptMap f = c_B then
          ({ attempts := (f :: tried).reverse, success := some f },
           some { foundationWitness := f, fromA := h₁, fromB := h₂ })
        else go rest (f :: tried)
      else go rest (f :: tried)
  go allFoundationConcepts []

/-! ## カスタムエラーメッセージ -/

/-- アライメント失敗時のエラー情報 -/
structure AlignmentError (O_A O_B : Ontology) where
  conceptA : O_A.Concept
  conceptB : O_B.Concept
  reason : String
  suggestions : List String

/-- エラー付きアライメント検索 -/
def findAlignmentOrError
    {O_A O_B : Ontology} 
    [DecidableEq O_A.Concept] [DecidableEq O_B.Concept]
    [HasLabel O_A.Concept] [HasLabel O_B.Concept]
    (φ_A : ExpansionMap O_A)
    (φ_B : ExpansionMap O_B)
    (c_A : O_A.Concept)
    (c_B : O_B.Concept) :
    Sum (AlignmentError O_A O_B) (ConceptAlignment O_A O_B φ_A φ_B c_A c_B) :=
  match decideAlignment φ_A φ_B c_A c_B with
  | some proof => .inr proof
  | none => .inl {
      conceptA := c_A
      conceptB := c_B
      reason := s!"No common foundation concept found for {HasLabel.label c_A} and {HasLabel.label c_B}"
      suggestions := [
        "Check if the expansion maps are correctly defined",
        "Consider adding intermediate concepts to the foundation ontology",
        "The concepts may be genuinely unaligned (different semantic domains)"
      ]
    }

end OntologyAlignment
