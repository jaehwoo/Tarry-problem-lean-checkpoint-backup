import csv, gzip, hashlib, json, shutil
from pathlib import Path

root=Path(__file__).resolve().parent
out=root/'new-import'
coverage=json.loads((out/'coverage.json').read_text())
sources=json.loads((out/'sources.json').read_text())
projects={o['archive_sha256'] for v in coverage['checkpoint_archives'].values() for o in v}
for s in sources:
    if s['sha256'] in projects:
        s['kind']='completed_project_package'
    assert s['kind']!='project_candidate'
(out/'sources.json').write_text(json.dumps(sources,ensure_ascii=False,indent=2)+'\n')
provenance=json.loads((out/'source_provenance.json').read_text())
by_hash={s['sha256']:s for s in sources}
for s in provenance:
    s.pop('local_path',None)
    s['kind']=by_hash[s['sha256']]['kind']
(out/'source_provenance.json').write_text(json.dumps(provenance,ensure_ascii=False,indent=2)+'\n')
with (out/'SOURCES.csv').open('w',newline='') as f:
    cols=['path','kind','bytes','sha256','library_file_id','file_id','version_id','modified_at','release_asset','member']
    w=csv.DictWriter(f,fieldnames=cols); w.writeheader()
    for s in sources:
        row={k:s.get(k) for k in cols}; row.update(release_asset=s['restore_from']['asset'],member=s['restore_from']['member']);w.writerow(row)
by_path={s['path']:s for s in sources}
with (out/'CHECKPOINTS.csv').open('w',newline='') as f:
    w=csv.writer(f);w.writerow(['checkpoint','archive_name','sha256','ancestor_library_file_id','ancestor_file_id','ancestor_version_id','nested_route'])
    for n,opts in sorted(coverage['checkpoint_archives'].items(),key=lambda p:int(p[0])):
        for o in opts:
            ancestor=by_path[o['route'][0]]
            w.writerow([n,o['archive_name'],o['archive_sha256'],ancestor['library_file_id'],ancestor['file_id'],ancestor['version_id'],json.dumps(o['route'])])
shutil.copyfile(root/'evidence/local_packaging_verify.json',out/'LOCAL_PACKAGING_VERIFICATION.json')
scope={'source_inventory':'Library recursive ZIP inventory modified since 2026-10-13T00:00:00Z, 77 results, no next page; broad title search (100 results) cross-checked newer archive identities; focused 109/116/117 completed-project filename search returned no matches.', 'selected_sources':69,'materialized_sources':69,'failed_materializations':[], 'selected_source_access_failures':[], 'latest_completed_package':115, 'unrecovered_historical_numbers':[72,73,74,75], 'no_completed_109':'Two progress archive hashes were found; neither is relabeled as a completed checkpoint.', 'historical_versions':'Latest returned file IDs are pinned. Numeric Library version IDs are retained where provided; null means not exposed, not an inferred version 0. Nested originals retain their exact byte hashes and routes to the pinned ancestor. Unlisted prior Library versions were not enumerated.', 'historical_109_progress':{'file_id':'file_00000000c28081f5ad0e4197cd5bf9ea','library_file_id':'libfile_6d1c24aee4b081919e0507591d5224ae','recorded_version_id':None,'sha256':'267aa00f8b08c901fbdb603a744f8cad28adc31d9a7337c671f73c98be424bce','recovery':'Exact bytes found as nested original; no claim of direct old-version Library access.'},'versions_not_reconstructed':True}
(out/'LOOKUP_SCOPE.json').write_text(json.dumps(scope,ensure_ascii=False,indent=2)+'\n')
print(json.dumps({'sources':len(sources),'complete_project_packages':len(projects),'complete_checkpoint_numbers':len(coverage['checkpoint_archives'])}))
