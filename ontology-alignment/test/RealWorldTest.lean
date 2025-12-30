/-
  test/RealWorldTest.lean
  
  実世界オントロジー（SNOMED CT, Gene Ontology）のテストスイート
-/

import OntologyAlignment
import OntologyAlignment.RealWorld.SNOMEDGOAlignment

open OntologyAlignment
open OntologyAlignment.RealWorld

/-! ## SNOMED CT テスト -/

-- SNOMED CTオントロジーの基本テスト
#check SNOMEDOntology
#check SNOMEDConcept.MyocardialInfarction
#check SNOMEDConcept.clinicalFinding

-- 展開写像のテスト
#eval snomedExpansion.conceptMap .Force  -- Disease
#eval snomedExpansion.conceptMap .Container  -- BodyStructure

/-! ## Gene Ontology テスト -/

-- GOオントロジーの基本テスト
#check GeneOntology
#check GOConcept.Apoptosis
#check GOConcept.aspect

-- 展開写像のテスト
#eval goExpansion.conceptMap .Force  -- BiologicalRegulation
#eval goExpansion.conceptMap .Container  -- IntracellularOrganelle

/-! ## アライメント証明テスト -/

-- 個別アライメント証明の存在確認
#check bodyStructure_cellularComponent_alignment
#check disease_regulation_alignment
#check procedure_molecularFunction_alignment
#check symptom_response_alignment

-- 対称性のテスト
#check snomed_go_symmetric disease_regulation_alignment

/-! ## 決定手続きテスト -/

-- アライメントが存在するケース
#eval (decideAlignment snomedExpansion goExpansion 
        (.hierarchy .BodyStructure) 
        (.cellularComponent .IntracellularOrganelle)).isSome
-- expected: true

#eval (decideAlignment snomedExpansion goExpansion 
        (.clinicalFinding .Disease) 
        (.biologicalProcess .BiologicalRegulation)).isSome
-- expected: true

-- アライメントが存在しないケース
#eval (decideAlignment snomedExpansion goExpansion 
        (.clinicalFinding .Disease)
        (.cellularComponent .Nucleus)).isSome
-- expected: false

/-! ## 全アライメント列挙テスト -/

#eval allSNOMEDGOAlignments.length
-- expected: 12

/-! ## 検索機能テスト -/

-- SNOMED CT → GO 検索
#eval findGOEquivalent (.clinicalFinding .Disease)
-- expected: some (biologicalProcess BiologicalRegulation)

#eval findGOEquivalent (.hierarchy .BodyStructure)
-- expected: some (cellularComponent IntracellularOrganelle)

-- GO → SNOMED CT 検索
#eval findSNOMEDEquivalent (.aspect .BiologicalProcess)
-- expected: some (hierarchy Procedure)

#eval findSNOMEDEquivalent (.biologicalProcess .ResponseToStimulus)
-- expected: some (clinicalFinding Symptom)

/-! ## 拡張基本領域テスト -/

#check BiomedicalFoundationOntology
#check BiomedicalFoundationConcept.Disease
#check extendedSnomedExpansion
#check extendedGOExpansion

-- イメージスキーマへの逆写像
#eval toBasicFoundation .Container  -- some Container
#eval toBasicFoundation .Disease    -- none

-- 精緻化関係のテスト
#eval isRefinementOf .Disease .Force  -- true
#eval isRefinementOf .MolecularFunction .Enablement  -- true
#eval isRefinementOf .Container .Force  -- false

/-! ## レポート生成テスト -/

#eval generateAlignmentReport

/-! ## 統合テスト -/

/-- 全テストの実行 -/
def runAllRealWorldTests : IO Unit := do
  IO.println "=== Real World Ontology Tests ==="
  IO.println ""
  
  -- SNOMED CT テスト
  IO.println "SNOMED CT Tests:"
  let snomedConceptCount := allSNOMEDConcepts.length
  IO.println s!"  Concepts: {snomedConceptCount}"
  
  -- GO テスト
  IO.println "Gene Ontology Tests:"
  let goConceptCount := allGOConcepts.length
  IO.println s!"  Concepts: {goConceptCount}"
  
  -- アライメントテスト
  IO.println "Alignment Tests:"
  let alignmentCount := allSNOMEDGOAlignments.length
  IO.println s!"  Total alignments: {alignmentCount}"
  
  -- 決定手続きテスト
  IO.println "Decision Procedure Tests:"
  let test1 := (decideAlignment snomedExpansion goExpansion 
                 (.clinicalFinding .Disease) 
                 (.biologicalProcess .BiologicalRegulation)).isSome
  IO.println s!"  Disease-Regulation: {test1}"
  
  let test2 := (decideAlignment snomedExpansion goExpansion 
                 (.clinicalFinding .Disease)
                 (.cellularComponent .Nucleus)).isSome
  IO.println s!"  Disease-Nucleus (should be false): {test2}"
  
  -- 拡張基本領域テスト
  IO.println "Extended Foundation Tests:"
  let extConceptCount := allBiomedicalFoundationConcepts.length
  IO.println s!"  Extended concepts: {extConceptCount}"
  
  IO.println ""
  IO.println "=== All Tests Complete ==="
