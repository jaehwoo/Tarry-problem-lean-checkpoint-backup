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

open Lean Elab Command Meta

run_cmd do
  let some selected ← liftIO (IO.getEnv "AFFINE_AUDIT_NAMES") | throwError "missing selected names"
  let targets := selected.splitOn "\n"
  let some output ← liftIO (IO.getEnv "AFFINE_AUDIT_OUTPUT") | throwError "missing output path"
  liftIO <| IO.FS.writeFile (output ++ ".progress") "AUDIT START\n"
  let env ← getEnv
  let mut count := 0
  let mut summary := ""
  for modName in env.header.moduleNames, md in env.header.moduleData do
    if #[`PaperILean.PortfolioHolderEnvelope, `PaperILean.PortfolioHolder, `PaperILean.PortfolioAtlasNorms, `PaperILean.PortfolioAtlasOverlap, `PaperILean.PortfolioAtlasStage, `PaperILean.PortfolioSlopesData, `PaperILean.PortfolioSlopesCoefficients, `PaperILean.PortfolioSlopesPLU, `PaperILean.PortfolioSlopesMf, `PaperILean.PortfolioSlopesPf, `PaperILean.PortfolioSlopesCf5, `PaperILean.PortfolioSlopesCf4, `PaperILean.PortfolioSlopesPa, `PaperILean.PortfolioSlopesMe, `PaperILean.PortfolioSlopesLe, `PaperILean.PortfolioSlopesCe, `PaperILean.PortfolioSlopesMd, `PaperILean.PortfolioSlopesCd, `PaperILean.PortfolioSlopesMatrixStage, `PaperILean.PortfolioMinorStability, `PaperILean.PortfolioSlopesWhole].contains modName then
     for n in md.constNames do
      unless targets.contains n.toString do continue
      let some ci := env.find? n | throwError "missing constant {n}"
      liftIO <| IO.FS.withFile (output ++ ".progress") .append (fun h => h.putStrLn s!"BEGIN {n}")
      if ci.isUnsafe then
        logInfo m!"EXCLUDED compiler-unsafe declaration: {n}"
        continue
      if ci.isPartial then throwError "partial mathematical declaration: {n}"
      if ci.type.hasSorry || ci.type.hasMVar || ci.type.hasFVar then
        throwError "nonclosed or sorry type: {n}"
      match Kernel.check env {} ci.type with
      | .error _ => throwError "kernel type check failed: {n}"
      | .ok _ => pure ()
      let mut bodyDescription := ""
      match ci.value? true with
      | some body =>
        if body.hasSorry || body.hasMVar || body.hasFVar then
          throwError "nonclosed or sorry body: {n}"
        for ref in ci.type.getUsedConstants ++ body.getUsedConstants do
          if let some dep := env.find? ref then
            if dep.isUnsafe then throwError "unsafe dependency {ref} in {n}"
        let actualType ← match Kernel.check env {} body with
          | .error _ => throwError "kernel body check failed: {n}"
          | .ok t => pure t
        liftTermElabM do
          unless ← isDefEq actualType ci.type do
            throwError "body/type mismatch: {n}"
        bodyDescription := s!"body_hash={body.hash}"
      | none =>
        throwError "unplanned bodyless declaration {n}: a reviewed new structural replay is required"
      let axioms ← collectAxioms n
      for ax in axioms do
        unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
          throwError "unapproved axiom {ax} in {n}"
      liftIO <| IO.FS.withFile (output ++ ".progress") .append (fun h => h.putStrLn s!"CHECKED {n}; axioms={axioms}")
      summary := summary ++ s!"{n}; type_hash={ci.type.hash}; {bodyDescription}; axioms={axioms}\n"
      count := count + 1
  unless count == targets.length do throwError "incomplete batch: checked {count} expected {targets.length}"
  liftIO <| IO.FS.writeFile (output ++ ".hashes") summary
  logInfo m!"All {count} namespace declarations passed full kernel type/body, closure, safety and axiom checks."
