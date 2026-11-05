import PaperILean.PortfolioHolderEnvelope
import PaperILean.PortfolioHolder
import PaperILean.PortfolioAtlasNorms
import PaperILean.PortfolioAtlasOverlap
import PaperILean.PortfolioAtlasStage
import Lean

open Lean Elab Command Meta

private def auditKind : ConstantInfo → String
  | .axiomInfo _ => "axiom"
  | .defnInfo _ => "definition"
  | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quotient"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"

private def auditPayloads (ci : ConstantInfo) : List Expr :=
  ci.type :: ((ci.value? true).toList ++ match ci with
    | .recInfo r => r.rules.map (·.rhs)
    | _ => [])

run_cmd do
  let env ← getEnv
  let mut constants : Array ConstantInfo := #[]
  for modName in env.header.moduleNames, md in env.header.moduleData do
    if #[`PaperILean.PortfolioHolderEnvelope, `PaperILean.PortfolioHolder, `PaperILean.PortfolioAtlasNorms, `PaperILean.PortfolioAtlasOverlap, `PaperILean.PortfolioAtlasStage].contains modName then
      for n in md.constNames do
        let some ci := env.find? n | throwError "missing constant {n}"
        constants := constants.push ci
  let unsafeNames := constants.filter (·.isUnsafe) |>.map (·.name)
  let mut rows : Array Json := #[]
  let mut unsafeText := ""
  let mut safeCount := 0
  for ci in constants do
    let refs := ((auditPayloads ci).flatMap (fun e => e.getUsedConstants.toList)).eraseDups
    let hits := refs.filter unsafeNames.contains
    if !ci.isUnsafe then
      safeCount := safeCount + 1
      unless hits.isEmpty do throwError "unsafe reference in safe payload {ci.name}: {hits}"
    let bodyHash := match ci.value? true with
      | some e => Json.str (toString e.hash)
      | none => Json.null
    let kindFields := match ci with
      | .inductInfo i => [
          ("numParams", toJson i.numParams), ("numIndices", toJson i.numIndices),
          ("numNested", toJson i.numNested), ("isRec", toJson i.isRec),
          ("isReflexive", toJson i.isReflexive),
          ("all", toJson (i.all.map toString)), ("constructors", toJson (i.ctors.map toString))]
      | .ctorInfo c => [("inductive", toJson c.induct.toString)]
      | .recInfo r => [("all", toJson (r.all.map toString)),
          ("rule_rhs_hashes", toJson (r.rules.map (fun a => toString a.rhs.hash))),
          ("rule_constructors", toJson (r.rules.map (fun a => a.ctor.toString)))]
      | _ => []
    rows := rows.push (Json.mkObj ([
      ("name", toJson ci.name.toString), ("kind", toJson (auditKind ci)),
      ("isUnsafe", toJson ci.isUnsafe), ("isPartial", toJson ci.isPartial),
      ("type_hash", toJson (toString ci.type.hash)), ("body_hash", bodyHash),
      ("payload_references", toJson (refs.map toString)),
      ("unsafe_references", toJson (hits.map toString))] ++ kindFields))
    if ci.isUnsafe then
      let text ← liftTermElabM do
        withOptions (fun o => o.setBool `pp.proofs true |>.setBool `pp.universes true |>.setBool `pp.explicit true) do
          let ty ← ppExpr ci.type
          let value ← match ci.value? true with
            | some e => pure (toString (← ppExpr e))
            | none => pure "<no value>"
          return s!"NAME {ci.name}\nKIND {auditKind ci}\nTYPE\n{ty}\nBODY\n{value}\nREFERENCES {refs}\n\n"
      unsafeText := unsafeText ++ text
  let result := Json.mkObj [
    ("status", toJson "PASS_READ_ONLY_INVENTORY"),
    ("constant_count", toJson constants.size), ("safe_count", toJson safeCount),
    ("unsafe_count", toJson unsafeNames.size),
    ("all_safe_payloads_exclude_unsafe", toJson true),
    ("payloads_include_recursor_rule_rhs", toJson true),
    ("constants", Json.arr rows)]
  liftIO <| IO.FS.writeFile "evidence/Compiled_Kind_Inventory.json" (result.pretty ++ "\n")
  liftIO <| IO.FS.writeFile "evidence/Unsafe_Compiled_Payloads.txt" unsafeText
  logInfo m!"READ_ONLY_KIND_INVENTORY constants={constants.size} safe={safeCount} unsafe={unsafeNames.size}"
