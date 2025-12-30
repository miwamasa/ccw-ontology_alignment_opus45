import Lake
open Lake DSL

package «ontology-alignment» where
  version := v!"0.1.0"
  keywords := #["ontology", "alignment", "metaphor", "proof"]
  description := "Provable Ontology Alignment based on Metaphor Theory"

lean_lib «OntologyAlignment» where
  srcDir := "."

@[default_target]
lean_exe «ontology-alignment» where
  root := `Main

-- 将来的にmathlibを追加する場合
-- require mathlib from git
--   "https://github.com/leanprover-community/mathlib4.git"
