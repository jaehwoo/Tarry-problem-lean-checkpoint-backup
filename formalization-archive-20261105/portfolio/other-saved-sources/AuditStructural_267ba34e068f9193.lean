import PaperILean.PortfolioHolder
import Lean

/-! Replay only the two frozen nonrecursive record families. The reference
environment supplies expressions to compare, never primitive declarations to
insert. A separate import environment excludes PortfolioHolder throughout. -/

open Lean Elab Command

namespace PortfolioStructuralAudit

private def holderModule : Name := `PaperILean.PortfolioHolder
private def commonName : Name := `PaperI.PortfolioHolder.CommonRateAssignment
private def boundsName : Name := `PaperI.PortfolioHolder.AssignmentBounds

private def primitiveNames : Array Name := #[
  `PaperI.PortfolioHolder.CommonRateAssignment,
  `PaperI.PortfolioHolder.CommonRateAssignment.mk,
  `PaperI.PortfolioHolder.CommonRateAssignment.rec,
  `PaperI.PortfolioHolder.AssignmentBounds,
  `PaperI.PortfolioHolder.AssignmentBounds.mk,
  `PaperI.PortfolioHolder.AssignmentBounds.rec]

private def projectionNames : Array Name := #[
  `PaperI.PortfolioHolder.CommonRateAssignment.pieces,
  `PaperI.PortfolioHolder.CommonRateAssignment.assignment,
  `PaperI.PortfolioHolder.CommonRateAssignment.rate,
  `PaperI.PortfolioHolder.CommonRateAssignment.scale,
  `PaperI.PortfolioHolder.CommonRateAssignment.aspect,
  `PaperI.PortfolioHolder.CommonRateAssignment.measurable_fibre]

/-- These hashes bind the exact compiled inventory being independently replayed;
they are not used instead of structural expression equality. -/
private def expectedTypeHash (n : Name) : Option String :=
  if n == commonName then some "3480822437"
  else if n == `PaperI.PortfolioHolder.CommonRateAssignment.mk then some "314107036"
  else if n == `PaperI.PortfolioHolder.CommonRateAssignment.rec then some "3680989545"
  else if n == boundsName then some "4168283043"
  else if n == `PaperI.PortfolioHolder.AssignmentBounds.mk then some "1315246404"
  else if n == `PaperI.PortfolioHolder.AssignmentBounds.rec then some "2257196713"
  else if n == `PaperI.PortfolioHolder.CommonRateAssignment.pieces then some "877878641"
  else if n == `PaperI.PortfolioHolder.CommonRateAssignment.assignment then some "848352759"
  else if n == `PaperI.PortfolioHolder.CommonRateAssignment.rate then some "968134866"
  else if n == `PaperI.PortfolioHolder.CommonRateAssignment.scale then some "271916559"
  else if n == `PaperI.PortfolioHolder.CommonRateAssignment.aspect then some "271916559"
  else if n == `PaperI.PortfolioHolder.CommonRateAssignment.measurable_fibre then some "4124245621"
  else none

private def expectedBodyHash (n : Name) : Option String :=
  if n == `PaperI.PortfolioHolder.CommonRateAssignment.pieces then some "3494548653"
  else if n == `PaperI.PortfolioHolder.CommonRateAssignment.assignment then some "1189739092"
  else if n == `PaperI.PortfolioHolder.CommonRateAssignment.rate then some "1895430546"
  else if n == `PaperI.PortfolioHolder.CommonRateAssignment.scale then some "88716250"
  else if n == `PaperI.PortfolioHolder.CommonRateAssignment.aspect then some "3615922470"
  else if n == `PaperI.PortfolioHolder.CommonRateAssignment.measurable_fibre then some "1351090792"
  else none

private def sameBase (a b : ConstantVal) : Bool :=
  a.name == b.name && a.levelParams == b.levelParams && Expr.equal a.type b.type

private def sameRules (xs ys : List RecursorRule) : Bool :=
  xs.length == ys.length && (xs.zip ys).all (fun (a, b) =>
    a.ctor == b.ctor && a.nfields == b.nfields && Expr.equal a.rhs b.rhs)

/-- Exact types include binder names and annotations, not only definitional or
alpha equality. All constructor, inductive and recursor metadata are compared. -/
private def sameConstant (a b : ConstantInfo) : Bool :=
  sameBase a.toConstantVal b.toConstantVal && match a, b with
  | .inductInfo x, .inductInfo y =>
      x.numParams == y.numParams && x.numIndices == y.numIndices &&
      x.all == y.all && x.ctors == y.ctors && x.numNested == y.numNested &&
      x.isRec == y.isRec && x.isUnsafe == y.isUnsafe && x.isReflexive == y.isReflexive
  | .ctorInfo x, .ctorInfo y =>
      x.induct == y.induct && x.cidx == y.cidx && x.numParams == y.numParams &&
      x.numFields == y.numFields && x.isUnsafe == y.isUnsafe
  | .recInfo x, .recInfo y =>
      x.all == y.all && x.numParams == y.numParams && x.numIndices == y.numIndices &&
      x.numMotives == y.numMotives && x.numMinors == y.numMinors &&
      sameRules x.rules y.rules && x.k == y.k && x.isUnsafe == y.isUnsafe
  | .defnInfo x, .defnInfo y =>
      Expr.equal x.value y.value && x.hints == y.hints && x.safety == y.safety && x.all == y.all
  | .thmInfo x, .thmInfo y => Expr.equal x.value y.value && x.all == y.all
  | _, _ => false

private def payloads (ci : ConstantInfo) : List Expr :=
  ci.type :: ((ci.value? true).toList ++ match ci with
    | .recInfo r => r.rules.map (·.rhs)
    | _ => [])

private def kind (ci : ConstantInfo) : String :=
  match ci with
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"
  | .defnInfo _ => "definition"
  | .thmInfo _ => "theorem"
  | _ => "unsupported"

private def checkClosedAndSafe (env : Kernel.Environment) (ci : ConstantInfo) : CommandElabM Unit := do
  if ci.isUnsafe || ci.isPartial then throwError "unsafe or partial replay payload {ci.name}"
  unless ci.levelParams.eraseDups.length == ci.levelParams.length do
    throwError "repeated universe parameter in {ci.name}"
  for e in payloads ci do
    if e.hasSorry || e.hasMVar || e.hasFVar || e.hasLooseBVars then
      throwError "nonclosed or sorry expression in {ci.name}"
    for u in (collectLevelParams {} e).params do
      unless ci.levelParams.contains u do
        throwError "undeclared universe parameter {u} in {ci.name}"
    for ref in e.getUsedConstants do
      let some dep := env.find? ref | throwError "missing reference {ref} in {ci.name}"
      if dep.isUnsafe || dep.isPartial then
        throwError "unsafe or partial reference {ref} in {ci.name}"

private def checkFrozen (env : Environment) (n : Name) : CommandElabM ConstantInfo := do
  let some ci := env.find? n | throwError "missing frozen declaration {n}"
  let some expected := expectedTypeHash n | throwError "unplanned replay name {n}"
  unless toString ci.type.hash == expected do throwError "frozen type hash mismatch {n}"
  if let some expected := expectedBodyHash n then
    let some body := ci.value? true | throwError "missing frozen projection body {n}"
    unless toString body.hash == expected do throwError "frozen projection body hash mismatch {n}"
  checkClosedAndSafe env.toKernelEnv ci
  return ci

private def replayDecl (env : Kernel.Environment) (decl : Declaration) :
    CommandElabM Kernel.Environment := do
  let opts : Options := {}
  unless maxHeartbeats.get opts == 200000 && maxRecDepth.get opts == 512 do
    throwError "unexpected pinned default proof limits"
  if debug.skipKernelTC.get opts then throwError "kernel checking must remain enabled"
  unless env.header.trustLevel == 0 do throwError "replay trust level is not zero"
  -- getMaxHeartbeats converts the public 200000 allocation-thousands to
  -- 200000000 kernel allocation units. Zero (unlimited) is never passed.
  match env.addDeclCore (Core.getMaxHeartbeats opts).toUSize decl none with
  | .ok result => return result
  | .error _ => throwError "kernel rejected structural replay {decl.getNames}"

private def declarationRow (ci : ConstantInfo) : Json :=
  let extra := match ci with
    | .inductInfo i => [
        ("num_params", toJson i.numParams), ("num_indices", toJson i.numIndices),
        ("num_nested", toJson i.numNested), ("is_recursive", toJson i.isRec),
        ("is_reflexive", toJson i.isReflexive), ("all", toJson (i.all.map toString)),
        ("constructors", toJson (i.ctors.map toString))]
    | .ctorInfo c => [("inductive", toJson c.induct.toString),
        ("constructor_index", toJson c.cidx), ("num_params", toJson c.numParams),
        ("num_fields", toJson c.numFields)]
    | .recInfo r => [("all", toJson (r.all.map toString)),
        ("num_params", toJson r.numParams), ("num_indices", toJson r.numIndices),
        ("num_motives", toJson r.numMotives), ("num_minors", toJson r.numMinors),
        ("k", toJson r.k), ("rules", toJson (r.rules.map fun rule => Json.mkObj [
          ("constructor", toJson rule.ctor.toString), ("num_fields", toJson rule.nfields),
          ("rhs_hash", toJson (toString rule.rhs.hash))]))]
    | _ => []
  Json.mkObj ([
    ("name", toJson ci.name.toString), ("kind", toJson (kind ci)),
    ("level_params", toJson (ci.levelParams.map toString)),
    ("type_hash", toJson (toString ci.type.hash)),
    ("body_hash", match ci.value? true with
      | some body => toJson (toString body.hash)
      | none => Json.null),
    ("exact_type_and_metadata_match", toJson true),
    ("exact_rule_rhs_match", toJson true),
    ("closed_within_declared_universes", toJson true),
    ("safe_payloads_and_references", toJson true)] ++ extra)

private def compareGenerated (reference : Environment) (fresh : Kernel.Environment)
    (n : Name) : CommandElabM Json := do
  let expected ← checkFrozen reference n
  let some actual := fresh.find? n | throwError "kernel did not generate {n}"
  unless sameConstant expected actual do throwError "structural replay mismatch for {n}"
  checkClosedAndSafe fresh actual
  return declarationRow actual

private def replayFamily (reference : Environment) (fresh : Kernel.Environment)
    (family : Name) (params fields : Nat) : CommandElabM (Kernel.Environment × Array Json) := do
  unless family == commonName || family == boundsName do throwError "unplanned family {family}"
  let .inductInfo iv ← checkFrozen reference family | throwError "not an inductive family {family}"
  let ctor := family ++ `mk
  let recursor := family ++ `rec
  let .ctorInfo cv ← checkFrozen reference ctor | throwError "not a constructor {ctor}"
  let .recInfo rv ← checkFrozen reference recursor | throwError "not a recursor {recursor}"
  unless iv.numParams == params && iv.numIndices == 0 && iv.all == [family] &&
      iv.ctors == [ctor] && iv.numNested == 0 && !iv.isRec && !iv.isReflexive do
    throwError "family is outside the reviewed nonrecursive singleton shape: {family}"
  unless cv.induct == family && cv.cidx == 0 && cv.numParams == params &&
      cv.numFields == fields && cv.levelParams == iv.levelParams do
    throwError "unexpected constructor shape: {ctor}"
  unless rv.all == [family] && rv.numParams == params && rv.numIndices == 0 &&
      rv.numMotives == 1 && rv.numMinors == 1 && rv.rules.length == 1 do
    throwError "unexpected recursor shape: {recursor}"
  for rule in rv.rules do
    let expectedRuleHash := if family == commonName then "2666655828" else "3521257039"
    unless rule.ctor == ctor && rule.nfields == fields && toString rule.rhs.hash == expectedRuleHash do
      throwError "unexpected frozen recursor rule: {recursor}"
  for n in #[family, ctor, recursor] do
    if (fresh.find? n).isSome then throwError "replay destination already contains {n}"
  let decl := Declaration.inductDecl iv.levelParams iv.numParams
    [{ name := family, type := iv.type, ctors := [{ name := ctor, type := cv.type }] }] false
  let fresh ← replayDecl fresh decl
  let mut rows := #[]
  for n in #[family, ctor, recursor] do rows := rows.push (← compareGenerated reference fresh n)
  return (fresh, rows)

run_cmd do
  let reference ← getEnv
  let mut imports? : Option (Array Import) := none
  let mut actualBodyless : Array Name := #[]
  for moduleName in reference.header.moduleNames, md in reference.header.moduleData do
    if moduleName == holderModule then
      if imports?.isSome then throwError "duplicate Holder module in reference environment"
      imports? := some md.imports
      for ci in md.constants do
        if !ci.isUnsafe && (ci.value? true).isNone then actualBodyless := actualBodyless.push ci.name
  let some imports := imports? | throwError "Holder module was not imported"
  unless actualBodyless.size == primitiveNames.size && actualBodyless.all primitiveNames.contains do
    throwError "bodyless declaration inventory differs from the six reviewed names"
  if imports.any (fun i => i.module == holderModule) then throwError "self import in replay base"
  let fresh ← liftIO <| importModules imports {} 0
  if fresh.header.moduleNames.contains holderModule then throwError "Holder leaked into fresh import base"
  unless fresh.header.trustLevel == 0 do throwError "fresh import base is not at trust level zero"
  for n in primitiveNames ++ projectionNames do
    if (fresh.find? n).isSome then throwError "target declaration is already in fresh base: {n}"
  let (replayed, commonRows) ← replayFamily reference fresh.toKernelEnv commonName 3 6
  let mut replayed := replayed
  let mut rows := commonRows
  for n in projectionNames do
    let ci ← checkFrozen reference n
    let decl ← match ci with
      | .defnInfo d => pure (Declaration.defnDecl d)
      | .thmInfo t => pure (Declaration.thmDecl t)
      | _ => throwError "projection is not a definition/theorem: {n}"
    if (replayed.find? n).isSome then throwError "projection already in replay destination: {n}"
    replayed ← replayDecl replayed decl
    rows := rows.push (← compareGenerated reference replayed n)
  let (finalReplayed, boundsRows) ← replayFamily reference replayed boundsName 10 5
  rows := rows ++ boundsRows
  if finalReplayed.header.moduleNames.contains holderModule then throwError "Holder leaked into replay result"
  unless rows.size == 12 do throwError "incomplete structural replay"
  let result := Json.mkObj [
    ("status", toJson "PASS_EXACT_KERNEL_STRUCTURAL_REPLAY"),
    ("api", toJson "Lean.Kernel.Environment.addDeclCore"),
    ("trust_level", toJson (0 : Nat)), ("max_heartbeats_option", toJson (200000 : Nat)),
    ("kernel_heartbeat_units", toJson (Core.getMaxHeartbeats ({} : Options))),
    ("max_rec_depth_option", toJson (512 : Nat)), ("limits_overridden", toJson false),
    ("fresh_imports", toJson (imports.map fun i => i.module.toString)),
    ("fresh_base_excludes_Holder", toJson true),
    ("all_targets_absent_before_replay", toJson true),
    ("replayed_primitive_names", toJson (primitiveNames.map toString)),
    ("replayed_projection_names", toJson (projectionNames.map toString)),
    ("kernel_inductive_declarations_submitted", toJson (2 : Nat)),
    ("kernel_projection_declarations_submitted", toJson (6 : Nat)),
    ("expression_comparison", toJson "Expr.equal, including binder names and annotations"),
    ("source_inventory_bound", toJson "202011050392864695e86cddae11380a38c4dcacf8ddc2bcc337275fbfef0ca1"),
    ("declarations", Json.arr rows)]
  liftIO <| IO.FS.writeFile "evidence/Structural_Replay_Result.json" (result.pretty ++ "\n")
  logInfo "STRUCTURAL_REPLAY_PASS: two exact nonrecursive families, six primitive declarations, six checked projections"

end PortfolioStructuralAudit
