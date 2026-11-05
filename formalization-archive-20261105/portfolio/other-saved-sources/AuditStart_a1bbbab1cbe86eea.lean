import PaperILean.PortfolioHolderEnvelope
import PaperILean.PortfolioHolder
import PaperILean.PortfolioAtlasNorms
import PaperILean.PortfolioAtlasOverlap
import PaperILean.PortfolioAtlasStage
import Lean
open Lean Elab Command
run_cmd do
  liftIO <| IO.FS.writeFile "evidence/audit_started.txt" "STARTED\n"
  let env ← getEnv
  let mut names := ""
  for modName in env.header.moduleNames, md in env.header.moduleData do
    if #[`PaperILean.PortfolioHolderEnvelope, `PaperILean.PortfolioHolder, `PaperILean.PortfolioAtlasNorms, `PaperILean.PortfolioAtlasOverlap, `PaperILean.PortfolioAtlasStage].contains modName then
      for n in md.constNames do
        let some ci := env.find? n | throwError "missing {n}"
        names := names ++ s!"{n}	{ci.isUnsafe}\n"
  liftIO <| IO.FS.writeFile "evidence/audit_inventory.tsv" names
