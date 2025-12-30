/-
  OntologyAlignment.lean
  
  オントロジーアライメントライブラリのメインエクスポート
  
  使用方法：
  ```lean
  import OntologyAlignment
  ```
-/

-- コア理論
import OntologyAlignment.Basic
import OntologyAlignment.Foundation
import OntologyAlignment.ExpansionMap
import OntologyAlignment.Alignment
import OntologyAlignment.Tactics
import OntologyAlignment.Category

-- 教育用サンプル
import OntologyAlignment.Examples.Medical
import OntologyAlignment.Examples.Engineering
import OntologyAlignment.Examples.MedicalEngineeringAlignment

-- 実世界オントロジー
import OntologyAlignment.RealWorld.SNOMEDCT
import OntologyAlignment.RealWorld.GeneOntology
import OntologyAlignment.RealWorld.BiomedicalFoundation
import OntologyAlignment.RealWorld.SNOMEDGOAlignment
