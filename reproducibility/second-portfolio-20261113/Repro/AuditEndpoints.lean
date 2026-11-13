import Repro.Endpoints
import Lean

open Lean Elab Command Meta

/- This audit adds no mathematical assumptions or proofs. Published theorem
   inputs remain parameters of the original endpoint declarations. -/
run_cmd do
  let env ← getEnv
  for n in #[`PaperI.ParabolicCollar.parabolic_collars_local_boxes,
      `PaperI.GoodStrips.derivative_good_points_rectangle,
      `PaperI.derivative_good_points_curved_strips,
      `PaperI.AffineArea.algebraic_surface_packing_cutoff] do
    let some ci := env.find? n | throwError "missing endpoint {n}"
    unless ci matches .thmInfo _ do throwError "endpoint is not a theorem: {n}"
    if ci.isUnsafe || ci.isPartial then throwError "unsafe/partial endpoint: {n}"
    if ci.type.hasSorry || ci.type.hasMVar || ci.type.hasFVar then
      throwError "nonclosed or sorry type: {n}"
    let some body := ci.value? true | throwError "missing proof body: {n}"
    if body.hasSorry || body.hasMVar || body.hasFVar then
      throwError "nonclosed or sorry proof: {n}"
    match Kernel.check env {} ci.type with
    | .error _ => throwError "kernel type check failed: {n}"
    | .ok _ => pure ()
    let actualType ← match Kernel.check env {} body with
      | .error _ => throwError "kernel body check failed: {n}"
      | .ok t => pure t
    liftTermElabM do
      unless ← isDefEq actualType ci.type do
        throwError "proof/type mismatch: {n}"
    let axioms ← collectAxioms n
    for ax in axioms do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "unapproved transitive axiom {ax} in {n}"
    unless axioms.size == 3 do
      throwError "axiom set differs from the saved three-axiom set: {n}: {axioms}"
    logInfo m!"ENDPOINT_AUDIT_PASS {n}; axioms={axioms}"

set_option pp.explicit true
set_option pp.universes true
#check PaperI.ParabolicCollar.parabolic_collars_local_boxes
#print axioms PaperI.ParabolicCollar.parabolic_collars_local_boxes
#check PaperI.GoodStrips.derivative_good_points_rectangle
#print axioms PaperI.GoodStrips.derivative_good_points_rectangle
#check PaperI.derivative_good_points_curved_strips
#print axioms PaperI.derivative_good_points_curved_strips
#check PaperI.AffineArea.algebraic_surface_packing_cutoff
#print axioms PaperI.AffineArea.algebraic_surface_packing_cutoff
