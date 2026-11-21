import Revision
import Lean
open Lean Elab Command

/- Mathematical declaration audit on the checked kernel environment. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 0

run_cmd do
  let env ← getEnv
  let targets : Array Name := #[`PaperI.CommonNullAssignment.RevisedPieceReadout,
    `PaperI.CommonNullAssignment.RevisedAssignmentReadout,
    `PaperI.CommonNullAssignment.revised_common_null_assignment,
    `PaperI.CollarRevision.exact_tag,
    `PaperI.CollarRevision.measurable_exact_short_family,
    `PaperI.CollarRevision.pad,
    `PaperI.CollarRevision.capLeft,
    `PaperI.CollarRevision.capRight,
    `PaperI.CollarRevision.cap_length,
    `PaperI.CollarRevision.cap_geometry,
    `PaperI.CollarRevision.projection_bounded,
    `PaperI.CollarRevision.exact_seed_reaches,
    `PaperI.CommonNullAssignment.exact_cap_kernel,
    `PaperI.CollarRevision.cap_projection_derivative,
    `PaperI.CommonNullAssignment.exact_phase_literal_cap_route,
    `PaperI.CommonNullAssignment.exact_phase_centered_cap_with_budget,
    `PaperI.CommonNullAssignment.revised_centered_flux,
    `PaperI.CollarRevision.centered_first_jet,
    `PaperI.CommonNullAssignment.revised_phase_flux_route,
    `PaperI.CollarRevision.assemble_inner_cap,
    `PaperI.CommonNullAssignment.prepare_collar_with_polynomial_bridge,
    `PaperI.CommonNullAssignment.revised_assignment_from_rq,
    `PaperI.CollarRevision.comparable_good,
    `PaperI.CollarRevision.positive_fraction_endpoint,
    `PaperI.CollarRevision.horizontalForm,
    `PaperI.CollarRevision.projection_derivative,
    `PaperI.CollarRevision.exact_geometric_cap,
    `PaperI.CollarRevision.signed_width_inputs,
    `PaperI.CommonNullAssignment.revised_signed_kernel,
    `PaperI.CollarRevision.projected_graph_span,
    `PaperI.CollarVolume.revised_assigned_volume,
    `PaperI.CollarRevision.signed_long_width,
    `PaperI.CollarRevision.horizontal_bridge,
    `PaperI.CollarRevision.short_corridor_span]
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  let mut localNames : NameHashSet := {}
  let mut modules := #[]
  for m in env.header.moduleNames, md in env.header.moduleData do
    if m.getRoot == `Revision then
      modules := modules.push m
      for n in md.constNames do
        localNames := localNames.insert n
  let mut pending := targets
  let mut seen : NameHashSet := {}
  let mut checked := 0
  let mut used := #[]
  let mut rows := #[]
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    if seen.contains n then continue
    seen := seen.insert n
    let some ci := env.checked.get.find? n | throwError "missing declaration {n}"
    if ci.isUnsafe || ci.isPartial then throwError "unsafe or partial mathematical dependency {n}"
    if ci.type.hasSorry || ci.type.hasMVar || ci.type.hasFVar then throwError "unclosed or placeholder type {n}"
    pending := pending ++ ci.type.getUsedConstants
    match ci with
    | .axiomInfo _ =>
      unless allowed.contains n do throwError "unapproved transitive axiom {n}"
      used := used.push n
    | .inductInfo v =>
      pending := pending ++ v.ctors.toArray
    | _ => pure ()
    if let some body := ci.value? true then
      if body.hasSorry || body.hasMVar || body.hasFVar then throwError "unclosed or placeholder body {n}"
      pending := pending ++ body.getUsedConstants
      if localNames.contains n then
        match Kernel.check env {} ci.type with
        | .error _ => throwError "kernel type failure {n}"
        | .ok _ => pure ()
        let actual ← match Kernel.check env {} body with
          | .error _ => throwError "kernel body failure {n}"
          | .ok t => pure t
        unless Kernel.isDefEqGuarded env {} actual ci.type do throwError "kernel type mismatch {n}"
        checked := checked+1
        rows := rows.push s!"{n}\t{ci.type.hash}\t{body.hash}"
    else if localNames.contains n then
      throwError "unexpected bodyless revision declaration {n}"
  for n in targets do
    unless localNames.contains n && seen.contains n do throwError "uncounted public result {n}"
    let ax ← collectAxioms n
    for a in ax do
      unless allowed.contains a do throwError "unapproved axiom {a} in {n}"
    logInfo m!"{n} -> {ax}"
  let resultDir : String := "evidence/"
  liftIO <| IO.FS.createDirAll resultDir
  liftIO <| IO.FS.writeFile (resultDir ++ "kernel-bodies.tsv") (String.intercalate "\n" rows.toList ++ "\n")
  liftIO <| IO.FS.writeFile (resultDir ++ "closure-summary.txt")
    s!"public entries = {targets.size}\nrechecked revision bodies = {checked}\ntransitive declarations scanned = {seen.toList.length}\nallowed axioms encountered = {used}\n"
  let mods := env.header.moduleNames.filter fun n => n.getRoot == `PaperILean || n.getRoot == `Revision
  liftIO <| IO.FS.writeFile (resultDir ++ "loaded-project-modules.txt") (String.intercalate "\n" (mods.toList.map toString) ++ "\n")
  logInfo m!"PASS: {targets.size} public entries, {checked} revision bodies, {seen.toList.length} transitive mathematical declarations, axioms {used}."

#print axioms PaperI.CommonNullAssignment.RevisedPieceReadout
#print axioms PaperI.CommonNullAssignment.RevisedAssignmentReadout
#print axioms PaperI.CommonNullAssignment.revised_common_null_assignment
#print axioms PaperI.CollarRevision.exact_tag
#print axioms PaperI.CollarRevision.measurable_exact_short_family
#print axioms PaperI.CollarRevision.pad
#print axioms PaperI.CollarRevision.capLeft
#print axioms PaperI.CollarRevision.capRight
#print axioms PaperI.CollarRevision.cap_length
#print axioms PaperI.CollarRevision.cap_geometry
#print axioms PaperI.CollarRevision.projection_bounded
#print axioms PaperI.CollarRevision.exact_seed_reaches
#print axioms PaperI.CommonNullAssignment.exact_cap_kernel
#print axioms PaperI.CollarRevision.cap_projection_derivative
#print axioms PaperI.CommonNullAssignment.exact_phase_literal_cap_route
#print axioms PaperI.CommonNullAssignment.exact_phase_centered_cap_with_budget
#print axioms PaperI.CommonNullAssignment.revised_centered_flux
#print axioms PaperI.CollarRevision.centered_first_jet
#print axioms PaperI.CommonNullAssignment.revised_phase_flux_route
#print axioms PaperI.CollarRevision.assemble_inner_cap
#print axioms PaperI.CommonNullAssignment.prepare_collar_with_polynomial_bridge
#print axioms PaperI.CommonNullAssignment.revised_assignment_from_rq
#print axioms PaperI.CollarRevision.comparable_good
#print axioms PaperI.CollarRevision.positive_fraction_endpoint
#print axioms PaperI.CollarRevision.horizontalForm
#print axioms PaperI.CollarRevision.projection_derivative
#print axioms PaperI.CollarRevision.exact_geometric_cap
#print axioms PaperI.CollarRevision.signed_width_inputs
#print axioms PaperI.CommonNullAssignment.revised_signed_kernel
#print axioms PaperI.CollarRevision.projected_graph_span
#print axioms PaperI.CollarVolume.revised_assigned_volume
#print axioms PaperI.CollarRevision.signed_long_width
#print axioms PaperI.CollarRevision.horizontal_bridge
#print axioms PaperI.CollarRevision.short_corridor_span
