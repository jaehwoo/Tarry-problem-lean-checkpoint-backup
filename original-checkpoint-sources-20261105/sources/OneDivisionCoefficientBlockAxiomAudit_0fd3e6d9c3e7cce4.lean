import PaperILean.OneDivisionCoefficientBlock

set_option pp.funBinderTypes true
set_option pp.piBinderTypes true
set_option pp.proofs true
set_option pp.deepTerms true
set_option pp.maxSteps 1000000

open Lean Elab Command in
run_cmd do
  let modules : Array String := #["PaperILean.OneDivisionCoefficientBlock"]
  let env ← getEnv
  let owner := fun n : Name =>
    match env.getModuleIdxFor? n with
    | some idx => env.header.moduleNames[idx.toNat]!
    | none => Name.anonymous
  let isNew := fun n : Name => modules.contains (owner n).toString
  let isProject := fun n : Name =>
    n.toString.startsWith "PaperI." ||
    n.toString.startsWith "_private.PaperILean." ||
    (owner n).toString.startsWith "PaperILean."
  let allNames ← env.constants.foldM (init := #[]) fun names n _ => do
    pure (if isNew n then names.push n else names)
  let allNames := allNames.qsort Name.lt
  let mut names : Array Name := #[]
  for name in allNames do
    let ci ← getConstInfo name
    if ci.isUnsafe then
      let kind := match ci with
        | .thmInfo _ => "theorem"
        | .defnInfo _ => "definition"
        | .axiomInfo _ => "axiom"
        | .opaqueInfo _ => "opaque"
        | .ctorInfo _ => "constructor"
        | .recInfo _ => "recursor"
        | .inductInfo _ => "inductive"
        | .quotInfo _ => "quotient"
      logInfo s!"COMPILER_ONLY_ARTIFACT|{name}|{owner name}|{kind}|unsafe"
      logInfo m!"COMPILER_ARTIFACT_TYPE_BEGIN|{name}\n{ci.type}\nCOMPILER_ARTIFACT_TYPE_END|{name}"
    else
      if ci.isPartial then throwError "unexpected partial declaration: {name}"
      names := names.push name
  logInfo s!"ACTUAL_OWNED_DECLARATION_COUNT|{allNames.size}"
  for name in names do
    let ci ← getConstInfo name
    let kind := match ci with
      | .thmInfo _ => "theorem"
      | .defnInfo _ => "definition"
      | .axiomInfo _ => "axiom"
      | .opaqueInfo _ => "opaque"
      | .ctorInfo _ => "constructor"
      | .recInfo _ => "recursor"
      | .inductInfo _ => "inductive"
      | .quotInfo _ => "quotient"
    logInfo s!"ACTUAL_NEW_DECLARATION|{name}|{owner name}|{kind}"
    logInfo m!"TYPE_BEGIN|{name}\n{name} : {ci.type}\nTYPE_END|{name}"
    liftTermElabM do
      Lean.Meta.forallTelescope ci.type fun xs _ => do
        for i in [:xs.size] do
          let d ← xs[i]!.fvarId!.getDecl
          let prop ← Lean.Meta.isProp d.type
          logInfo s!"BINDER_IS_PROP|{name}|{i}|{d.userName}|{prop}"
          logInfo m!"TYPED_BINDER_DOMAIN_BEGIN|{name}|{i}\n{d.type}\nTYPED_BINDER_DOMAIN_END|{name}|{i}"
    let axioms ← collectAxioms name
    if axioms.isEmpty then
      logInfo m!"'{name}' does not depend on any axioms"
    else
      logInfo m!"'{name}' depends on axioms: {axioms.qsort Name.lt |>.toList}"
    if true then
      match ci.value? true with
      | some value => logInfo m!"BODY_BEGIN|{name}\n{value}\nBODY_END|{name}"
      | none => throwError "new definition/private helper has no inspectable body: {name}"
  logInfo s!"ACTUAL_NEW_DECLARATION_COUNT|{names.size}"
  let mut pending := names.toList
  let mut seen : Std.HashSet Name := {}
  while !pending.isEmpty do
    let name := pending.head!
    pending := pending.tail!
    if !seen.contains name then
      seen := seen.insert name
      let ci ← getConstInfo name
      if ci.isUnsafe || ci.isPartial then
        throwError "unsafe/compiler/partial constant reachable from mathematical proof/type/body: {name}"
      let refs := ci.type.getUsedConstants ++ ((ci.value? true).map Expr.getUsedConstants).getD #[]
      let deps := (refs.toList.filter isProject).eraseDups
      let libs := (refs.toList.filter (fun n => !isProject n)).eraseDups
      let typeRefs := (ci.type.getUsedConstants.toList.filter isProject).eraseDups
      logInfo s!"EXPLICIT_PROJECT_TYPE_REFERENCES|{name}|{String.intercalate ";" (typeRefs.map Name.toString)}"
      logInfo s!"DEPENDENCIES|{name}|{String.intercalate ";" (deps.map Name.toString)}"
      logInfo s!"LIBRARY_REFERENCES|{name}|{String.intercalate ";" (libs.map Name.toString)}"
      logInfo s!"DECLARATION_MODULE|{name}|{owner name}"
      match ci with
      | .axiomInfo _ => logInfo s!"PROJECT_AXIOM|{name}"
      | _ => pure ()
      let closureAxioms ← collectAxioms name
      logInfo s!"CLOSURE_AXIOMS|{name}|{String.intercalate ";" (closureAxioms.toList.map Name.toString)}"
      if !isNew name then
        logInfo m!"INHERITED_PROJECT_TYPE_BEGIN|{name}\n{ci.type}\nINHERITED_PROJECT_TYPE_END|{name}"
        logInfo s!"INHERITED_BODY_REUSED|{name}"
      pending := deps ++ pending
  logInfo s!"FRESH_COMPLETE_PROJECT_CLOSURE|{seen.size}"

open PaperI
open PaperI.OneDivisionCoefficientBlock
open PaperI.QuadraticGridRestriction
open PaperI.QuadraticMonomialSpan
open MvPolynomial
open scoped BigOperators
open Lean Meta Elab Command in
run_cmd Command.liftTermElabM do
  let entry := ``PaperI.OneDivisionCoefficientBlock.one_division_coefficient_stage
  let ci ← getConstInfo entry
  let expected ← Elab.Term.elabTerm (← `(∀ (k : ℕ) (A B C : ℝ),
    (∀ e : Fin 3 → ℕ, exponentDegree e ≤ k →
      (sourceMonomial e ∉ monomialSpan k ↔
        0 < e 0 ∧ exponentDegree e + 1 ≤ k)) ∧
    LinearIndependent ℝ (fun e : LowerIndex k => sourceMonomial e.val) ∧
    Submodule.span ℝ (Set.range (fun e : LowerIndex k => sourceMonomial e.val)) =
      GraphRestrictionKernel.lowerDegreeSpace k ∧
    Function.Bijective (shiftEquiv k) ∧
    (∀ e : LowerIndex k,
      X 0 * sourceMonomial e.val = sourceMonomial ((shiftEquiv k e).val)) ∧
    (∀ (e : LowerIndex k) (v : Fin 3 → ℕ),
      coeff (sourceExponent v) (quadratic A B C * sourceMonomial e.val) ≠ 0 →
      v 0 = e.val 0 ∧ exponentDegree v = exponentDegree (xShift e.val) + 1) ∧
    (∀ (e : LowerIndex k) (v : Fin 3 → ℕ), v 0 = 0 →
      coeff (sourceExponent v) (quadratic A B C * sourceMonomial e.val) ≠ 0 →
      sourceMonomial v ∈ monomialSpan k) ∧
    (remainingMatrix k A B C)ᵀ.BlockTriangular (gradeIndex k) ∧
    (∀ a : Fin (k + 1),
      (remainingMatrix k A B C)ᵀ.toSquareBlock (gradeIndex k) a = 1) ∧
    (remainingMatrix k A B C).det = 1)) none
  unless (← isDefEq ci.type expected) do
    throwError "actual entry type differs from the fixed complete coefficient-stage signature"
  forallTelescope ci.type fun xs target => do
    unless xs.size == 4 do
      throwError "entry must have exactly k,A,B,C and no proposition premise"
    let types ← xs.mapM inferType
    unless (← isDefEq types[0]! (mkConst ``Nat)) do
      throwError "first data binder is not Nat"
    for i in [1:4] do
      unless (← isDefEq types[i]! (mkConst ``Real)) do
        throwError "coefficient data binder is not Real"
    for i in [:4] do
      if ← isProp types[i]! then
        throwError "unexpected proposition premise"
    let conclusion ← whnf target
    unless conclusion.getAppFn.constName? == some ``And do
      throwError "entry conclusion must be the full coefficient-stage conjunction"
    logInfo s!"ENTRY_BINDER_COUNT|{xs.size}"
    for i in [:xs.size] do
      let decl ← getFVarLocalDecl xs[i]!
      logInfo s!"ENTRY_BINDER|{i}|data|{decl.userName}|{reprStr decl.binderInfo}"
      logInfo m!"ENTRY_BINDER_TYPE_BEGIN|{i}\n{types[i]!}\nENTRY_BINDER_TYPE_END|{i}"
    logInfo m!"ENTRY_CONCLUSION_TYPE_BEGIN|{entry}\n{target}\nENTRY_CONCLUSION_TYPE_END|{entry}"
    logInfo s!"ENTRY_CONCLUSION_CONSTANTS|{String.intercalate ";" (target.getUsedConstants.toList.map Name.toString)}"
    logInfo "ENTRY_AST_BINDERS_VERIFIED|true"
    logInfo "ENTRY_AST_NO_PROPOSITION_PREMISES|true"
    logInfo "ENTRY_AST_CONCLUSION_IS_COMPLETE_COEFFICIENT_STAGE|true"
