"""Collect only executed211 gates, actual types/bodies/axioms and kernel links."""
from pathlib import Path
import hashlib,json,re
from checkpoint100_make_audit import strip_comments
P=Path(__file__).resolve().parents[1]
read=lambda f:json.loads((P/f).read_text())
def write(f,x):(P/f).write_text(json.dumps(x,indent=2,ensure_ascii=False)+'\n')
def sha(p):
 with p.open('rb') as f:return hashlib.file_digest(f,'sha256').hexdigest()
ds=lambda x:x.split(';') if isinstance(x,str) and x else list(x or [])
scope=read('tools/checkpoint211_scope.json');names={r['name'] for r in scope['declarations']}
history=read('evidence/checkpoint_211_command_history.json')['commands']
gates={n:[r for r in history if r['name']==n][-1] for n in ['final_units','final_axiom_audit','root_integration','pinned_environment']}
for n,r in gates.items():
 assert r['exit_code']==0 and r['sources_unchanged_during_execution'],n
 assert all(sha(P/f)==h for f,h in r['lean_source_sha256'].items()),n
log=(P/gates['final_axiom_audit']['log']).read_text()
ax={n:[s.strip() for s in a.split(',') if s.strip()] for n,a in re.findall(r"^'([^']+)' depends on axioms: \[([^\]]*)\]",log,re.M)}
ax.update({n:[] for n in re.findall(r"^'([^']+)' does not depend on any axioms",log,re.M)})
types={n:t.strip() for n,t,e in re.findall(r'^TYPE_BEGIN\|([^\n]+)\n(.*?)^TYPE_END\|([^\n]+)$',log,re.M|re.S) if n==e}
bodies={n:t.strip() for n,t,e in re.findall(r'^BODY_BEGIN\|([^\n]+)\n(.*?)^BODY_END\|([^\n]+)$',log,re.M|re.S) if n==e}
assert set(ax)==set(types)==names and set(bodies)==set(scope['body_query_roots'])
assert all(set(a)<={'propext','Classical.choice','Quot.sound'} for a in ax.values())
deps=dict(re.findall(r'^DEPENDENCIES\|([^|]+)\|([^\n]*)',log,re.M))
libs=dict(re.findall(r'^LIBRARY_REFERENCES\|([^|]+)\|([^\n]*)',log,re.M))
external={}
for n,c in re.findall(r'^EXPLICIT_PUBLISHED_INPUT\|([^|]+)\|([^\n]+)',log,re.M): external.setdefault(n,[]).append(c)
expected={}
assert {n:set(v) for n,v in external.items()}=={n:set(v) for n,v in expected.items()},external
assert scope['new_external_contracts']==[]
for f,h in read('evidence/checkpoint_211_baseline.json').items():
 if f!='PaperILean.lean':assert sha(P/f)==h,f
for r in scope['declarations']:
 p=P/'PaperILean'/f"{r['module']}.lean"
 assert sha(p)==r['source_sha256']
 assert not re.search(r'\b(sorry|admit|axiom|native_decide|native_eval|unsafe|ofReduceBool)\b',strip_comments(p.read_text()))
assert sha(P/scope['baseline_dependency_file'])==scope['baseline_dependency_sha256']
assert scope['baseline_dependency_file']=='reports/Checkpoint210_KernelProjectDependencies.json'
kernel=read(scope['baseline_dependency_file']);old={r['declaration'] for r in kernel}
for r in kernel:
 if r['declaration'] in deps:assert set(ds(r['direct_project_dependencies']))==set(ds(deps[r['declaration']])),r['declaration']
kernel += [dict(declaration=n,direct_project_dependencies=ds(d),library_references=ds(libs.get(n,'')),origin='checkpoint211') for n,d in deps.items() if n not in old]
by={r['declaration']:r for r in kernel};seen=set();todo=list(names);unknown=[]
while todo:
 n=todo.pop()
 if n in seen:continue
 seen.add(n)
 if n not in by:unknown.append(n);continue
 todo+=ds(by[n]['direct_project_dependencies'])
assert not unknown,unknown
for n in seen:
 assert not any(re.search(r'sorryAx|native_decide|native_eval|ofReduceBool',v) for v in ds(by[n].get('library_references'))),n
application_scope=read('tools/checkpoint211_application_scope.json')
required=application_scope['required_kernel_dependencies']
assert required,'Record the reviewed dependency targets before final collection.'
assert set(required)<=seen,set(required)-seen
locations=application_scope['module_locations']
completed=[]
for r in scope['declarations']:
 n=r['name'];completed.append(dict(declaration=n,declaration_kind=r['kind'],module='PaperILean/'+r['module']+'.lean',
  declaration_line=r['line'],source_sha256=r['source_sha256'],origin=r['origin'],formal_statement=types[n],
  definition_body=bodies.get(n),axioms=ax[n],accepted_published_inputs=external.get(n,[]),conditional_proof=bool(external.get(n)),
 manuscript_application_conditional=n in application_scope['conditional_application_declarations'],external_contract=False,
 unformalized_application_inputs=(application_scope['coupled_application_inputs'] if n in application_scope['conditional_application_declarations'] else []),
  proof_scope=application_scope['resolved'],
  direct_project_dependencies=ds(by[n]['direct_project_dependencies']),library_references=ds(by[n].get('library_references')),
  source_lines=locations[r['module']],status='Final pinned unit/root builds and transitive axiom audit passed; actual compiled-statement review recorded separately.'))
write('reports/Checkpoint211_CompletedDeclarations.json',completed)
write('reports/Checkpoint211_KernelProjectDependencies.json',kernel)
write('reports/Checkpoint211_CompletedDependencyClosure.json',dict(roots=sorted(names),reachable_declarations=sorted(seen),unexpanded_nodes=unknown,complete=True))
(P/'evidence/checkpoint_211_final_print_axioms.txt').write_text('\n'.join(m.group(0) for m in re.finditer(r"^'PaperI\.[^']+' (?:depends on axioms: \[[^\]]*\]|does not depend on any axioms)",log,re.M))+'\n')
s=dict(pure_quintic_boundary_excluded=True,through_quintic_coefficients_zero_proved=True,checkpoint=211,declarations_audited=len(completed),theorem_proofs=sum(r['declaration_kind'] in ['theorem','lemma'] for r in completed),
 definitions=sum(r['declaration_kind'] in ['def','abbrev'] for r in completed),structures=0,modules=len(scope['units']),
 new_external_contracts=0,explicit_published_input_theorems=len(external),definition_bodies_review_required=len(bodies),
 completed_scope_kernel_closure_nodes=len(seen),completed_scope_kernel_unexpanded=0,kernel_dependency_records=len(kernel),
 all_axioms_standard=True,axioms=ax,gates=gates,original_route_retained=True,new_manuscript_error_found=False,
 rank_entry_minimum_graph_proved=True,rank_entry_tail_proved=True,uniform_spectral_threshold_proved=False,bounded_window_input_proved=False,
 right_local_rank_entry_bound_proved=True,norm_slack_model_approximation_proved=True,scalar_saturation_obstruction_proved=True,bounded_failure_left_boundary_reduction_proved=True,
 strict_translation_slack_exclusion_proved=True,nonzero_physical_offset_exclusion_proved=True,
 translation_minimum_attainment_proved=True,simultaneous_saturation_critical_boundary_reduction_proved=True,
 simultaneous_saturation_critical_boundary_excluded=False,
 exact_model_root_normalization_proved=True,full_phase_coefficient_transport_proved=True,perturbed_sheet_application_proved=False,complete_augmented_transport_proved=True,
 classification_converse_proved=True,classification_part_i_proved=True,
 normalized_kernel_continuity_proved=True,normalized_kernel_bounded_total_window_bounds_proved=True,
 normalized_kernel_graph_definable=True,normalized_kernel_graph_semialgebraic_relative_to_published_inputs=True,
 normalized_kernel_polynomial_bounds_proved=True,quantitative_parameter_bounds_proved=True,canonical_profile_coefficient_upper_bounds_proved=True,nonlinear_profile_norm_lower_bound_proved=True,full_classification_iii_verified=True,verification_complete=False,verification_complete_relative_to_published_inputs=False)
write('evidence/checkpoint_211_final_verification_summary.json',s)
print(json.dumps({k:v for k,v in s.items() if k not in ['axioms','gates']},indent=2))
