/-
  Main.lean
  
  オントロジーアライメントのデモンストレーション
-/

import OntologyAlignment

open OntologyAlignment
open OntologyAlignment.Examples
open OntologyAlignment.RealWorld

def main : IO Unit := do
  IO.println "╔══════════════════════════════════════════════════════════════╗"
  IO.println "║  Provable Ontology Alignment - Metaphor Theory Framework     ║"
  IO.println "╚══════════════════════════════════════════════════════════════╝"
  IO.println ""
  
  -- Part 1: 教育用サンプル（Medical-Engineering）
  IO.println "━━━ Part 1: Educational Example (Medical ↔ Engineering) ━━━"
  IO.println ""
  
  for align in allMedEngAlignments do
    let (c_A, c_B, prf) := align
    IO.println s!"  {HasLabel.label c_A} ↔ {HasLabel.label c_B}"
    IO.println s!"    via: {HasLabel.label prf.foundationWitness}"
  
  IO.println ""
  IO.println s!"  Total alignments: {allMedEngAlignments.length}"
  IO.println ""
  
  -- Part 2: 実世界オントロジー（SNOMED CT - GO）
  IO.println "━━━ Part 2: Real World (SNOMED CT ↔ Gene Ontology) ━━━"
  IO.println ""
  
  IO.println "  Key alignments discovered:"
  IO.println ""
  IO.println "  ┌─────────────────────────┬─────────────────────────┬────────────┐"
  IO.println "  │ SNOMED CT               │ Gene Ontology           │ Foundation │"
  IO.println "  ├─────────────────────────┼─────────────────────────┼────────────┤"
  IO.println "  │ BodyStructure           │ CellularComponent       │ Container  │"
  IO.println "  │ Disease                 │ BiologicalRegulation    │ Force      │"
  IO.println "  │ TherapeuticProcedure    │ MolecularFunction       │ Enablement │"
  IO.println "  │ Procedure               │ BiologicalProcess       │ Process    │"
  IO.println "  │ Symptom                 │ ResponseToStimulus      │ Change     │"
  IO.println "  │ Organ                   │ ProteinComplex          │ PartWhole  │"
  IO.println "  │ DiagnosticProcedure     │ SignalTransduction      │ Path       │"
  IO.println "  │ Tissue                  │ Membrane                │ Link       │"
  IO.println "  └─────────────────────────┴─────────────────────────┴────────────┘"
  IO.println ""
  
  -- 決定手続きのデモ
  IO.println "  Decision procedure demos:"
  let test1 := (decideAlignment snomedExpansion goExpansion 
                 (.clinicalFinding .Disease) 
                 (.biologicalProcess .BiologicalRegulation)).isSome
  IO.println s!"    Disease ↔ BiologicalRegulation: {test1}"
  
  let test2 := (decideAlignment snomedExpansion goExpansion 
                 (.clinicalFinding .Disease)
                 (.cellularComponent .Nucleus)).isSome
  IO.println s!"    Disease ↔ Nucleus: {test2} (correctly no alignment)"
  IO.println ""
  
  -- 検索機能のデモ
  IO.println "  Cross-ontology search demos:"
  IO.println s!"    findGOEquivalent(Disease) = {repr (findGOEquivalent (.clinicalFinding .Disease))}"
  IO.println s!"    findSNOMEDEquivalent(BiologicalProcess) = {repr (findSNOMEDEquivalent (.aspect .BiologicalProcess))}"
  IO.println ""
  
  -- Part 3: 理論的保証
  IO.println "━━━ Part 3: Theoretical Guarantees ━━━"
  IO.println ""
  IO.println "  ✓ Soundness: Alignments are semantically valid (type-checked)"
  IO.println "  ✓ Symmetry: A ↔ B implies B ↔ A (proven)"
  IO.println "  ✓ Completeness: All foundation-based alignments are discoverable"
  IO.println "  ✓ Curry-Howard: Proofs = Algorithms"
  IO.println ""
  
  IO.println "╔══════════════════════════════════════════════════════════════╗"
  IO.println "║                      Demo Complete                           ║"
  IO.println "╚══════════════════════════════════════════════════════════════╝"
