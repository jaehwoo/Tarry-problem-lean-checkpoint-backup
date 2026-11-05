import PaperILean.PortfolioHolderEnvelope
import PaperILean.PortfolioHolder
import PaperILean.PortfolioAtlasNorms
import PaperILean.PortfolioAtlasOverlap
import PaperILean.PortfolioAtlasStage
import PaperILean.PortfolioSlopesData
import PaperILean.PortfolioSlopesCoefficients
import PaperILean.PortfolioSlopesPLU
import PaperILean.PortfolioSlopesMf
import PaperILean.PortfolioSlopesPf
import PaperILean.PortfolioSlopesCf5
import PaperILean.PortfolioSlopesCf4
import PaperILean.PortfolioSlopesPa
import PaperILean.PortfolioSlopesMe
import PaperILean.PortfolioSlopesLe
import PaperILean.PortfolioSlopesCe
import PaperILean.PortfolioSlopesMd
import PaperILean.PortfolioSlopesCd
import PaperILean.PortfolioSlopesMatrixStage
import PaperILean.PortfolioMinorStability
import PaperILean.PortfolioSlopesWhole
import Lean
open Lean Elab Command
run_cmd do
  liftIO <| IO.FS.writeFile "evidence/audit_started.txt" "STARTED\n"
  let env ← getEnv
  let mut names := ""
  for modName in env.header.moduleNames, md in env.header.moduleData do
    if #[`PaperILean.PortfolioHolderEnvelope, `PaperILean.PortfolioHolder, `PaperILean.PortfolioAtlasNorms, `PaperILean.PortfolioAtlasOverlap, `PaperILean.PortfolioAtlasStage, `PaperILean.PortfolioSlopesData, `PaperILean.PortfolioSlopesCoefficients, `PaperILean.PortfolioSlopesPLU, `PaperILean.PortfolioSlopesMf, `PaperILean.PortfolioSlopesPf, `PaperILean.PortfolioSlopesCf5, `PaperILean.PortfolioSlopesCf4, `PaperILean.PortfolioSlopesPa, `PaperILean.PortfolioSlopesMe, `PaperILean.PortfolioSlopesLe, `PaperILean.PortfolioSlopesCe, `PaperILean.PortfolioSlopesMd, `PaperILean.PortfolioSlopesCd, `PaperILean.PortfolioSlopesMatrixStage, `PaperILean.PortfolioMinorStability, `PaperILean.PortfolioSlopesWhole].contains modName then
      for n in md.constNames do
        let some ci := env.find? n | throwError "missing {n}"
        names := names ++ s!"{n}	{ci.isUnsafe}\n"
  liftIO <| IO.FS.writeFile "evidence/audit_inventory.tsv" names
