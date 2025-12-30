/-
  test/AlignmentTest.lean
  
  オントロジーアライメントのテストスイート
-/

import OntologyAlignment

open OntologyAlignment
open OntologyAlignment.Examples

/-! ## 基本構造のテスト -/

#check FoundationOntology
#check MedicalOntology
#check EngineeringOntology

/-! ## 展開写像のテスト -/

-- 写像が正しく定義されているか
#check medicalExpansion
#check engineeringExpansion

-- 写像の結果を確認
#eval medicalExpansion.conceptMap .Force      -- Disease
#eval engineeringExpansion.conceptMap .Force  -- Failure

/-! ## アライメント証明のテスト -/

-- 証明が存在することを確認
#check disease_failure_alignment
#check treatment_repair_alignment
#check body_machine_alignment

-- 自動証明のテスト
#check patient_operator_alignment_auto
#check symptom_malfunction_alignment_auto

/-! ## 決定手続きのテスト -/

-- アライメントが発見されるべきケース
#eval (decideAlignment medicalExpansion engineeringExpansion 
        MedicalConcept.Disease EngineeringConcept.Failure).isSome
-- true

#eval (decideAlignment medicalExpansion engineeringExpansion 
        MedicalConcept.Treatment EngineeringConcept.Repair).isSome
-- true

-- 間違ったペアではアライメントなし
#eval (decideAlignment medicalExpansion engineeringExpansion 
        MedicalConcept.Disease EngineeringConcept.Repair).isSome
-- false（Disease と Repair は異なる基本概念から展開）

/-! ## 対称性のテスト -/

-- Disease-Failure のアライメントから Failure-Disease のアライメントを導出
#check alignment_symmetric disease_failure_alignment

/-! ## 全アライメント列挙のテスト -/

#eval allMedEngAlignments.length  -- 12

/-! ## 証明トレースのテスト -/

#eval (findAlignmentWithTrace medicalExpansion engineeringExpansion 
        MedicalConcept.Disease EngineeringConcept.Failure).1.success
-- some Force

/-! ## 説明生成のテスト -/

#eval explainAlignment disease_failure_alignment
-- "Disease ≈ Failure via foundation concept 'Force'"

#eval explainAlignment treatment_repair_alignment
-- "Treatment ≈ Repair via foundation concept 'Enablement'"

/-! ## 性能テスト用の大きなクエリ -/

-- 全ペアに対するアライメント検査
def testAllPairs : List (MedicalConcept × EngineeringConcept × Bool) :=
  allMedicalConcepts.bind fun m =>
    allEngineeringConcepts.map fun e =>
      (m, e, (decideAlignment medicalExpansion engineeringExpansion m e).isSome)

#eval testAllPairs.filter (·.2.2)  -- アライメントが存在するペアのみ

/-! ## テスト結果サマリー -/

def runTests : IO Unit := do
  IO.println "=== Running Tests ==="
  
  -- 基本テスト
  let test1 := (decideAlignment medicalExpansion engineeringExpansion 
                 MedicalConcept.Disease EngineeringConcept.Failure).isSome
  IO.println s!"Disease-Failure alignment exists: {test1}"
  
  let test2 := (decideAlignment medicalExpansion engineeringExpansion 
                 MedicalConcept.Disease EngineeringConcept.Repair).isSome
  IO.println s!"Disease-Repair alignment exists: {test2}"
  
  -- 全アライメント数
  IO.println s!"Total alignments: {allMedEngAlignments.length}"
  
  IO.println "=== Tests Complete ==="
