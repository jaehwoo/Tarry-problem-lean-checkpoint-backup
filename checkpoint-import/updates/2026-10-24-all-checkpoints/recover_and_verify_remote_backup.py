#!/usr/bin/env python3
"""Reconstruct and verify the saved checkpoint inventory entirely from GitHub.

Run by the single-purpose GitHub recovery workflow. No manuscript, Lean source,
original checkpoint asset, repository visibility, or release publication state
is changed. The final Git commit is prepared but its branch ref is not moved.
"""
from concurrent.futures import ThreadPoolExecutor
from collections import Counter
import csv
import hashlib
import io
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile
import zipfile

import upload_all_checkpoints as transfer
import strict_github_transport as transport
from restore_original_checkpoint_files import checkpoint_number

ROOT = Path(__file__).resolve().parent
PREFIX = 'checkpoint-import/updates/2026-10-24-all-checkpoints/'
REPO = transfer.REPO
RELEASE = transfer.RELEASE_ID
transfer.GH = Path(shutil.which('gh'))
transfer.AUTH_DIR = None


def checked_json(asset):
    out = io.BytesIO()
    transfer.api(f"repos/{REPO}/releases/assets/{asset['id']}",
                 '-H', 'Accept: application/octet-stream', output=out)
    raw = out.getvalue()
    if len(raw) != asset['size'] or 'sha256:' + hashlib.sha256(raw).hexdigest() != asset['digest']:
        raise RuntimeError('Remote receipt or inventory bytes differ from the asset digest')
    return raw, json.loads(raw)


def write_json(name, value):
    transfer.save(ROOT / name, value)


def post(endpoint, value, method='POST'):
    with tempfile.NamedTemporaryFile(mode='w', suffix='.json') as body:
        json.dump(value, body)
        body.flush()
        return transfer.api(endpoint, '--method', method, '--input', body.name)


def verify_uploaded(asset, path):
    with tempfile.TemporaryFile() as output:
        transfer.api(f"repos/{REPO}/releases/assets/{asset['id']}",
                     '-H', 'Accept: application/octet-stream', output=output)
        output.seek(0)
        digest = hashlib.file_digest(output, 'sha256').hexdigest()
        if digest != transfer.sha256(path) or output.tell() != path.stat().st_size:
            raise RuntimeError('Published report/catalog readback differs')
    return {'asset_id': asset['id'], 'name': asset['name'], 'size_bytes': asset['size'],
            'sha256': digest, 'fresh_remote_download_matched': True,
            'url': asset['browser_download_url']}


def run():
    repo = transfer.api(f'repos/{REPO}')
    if repo['id'] != 1417233863 or not repo['private']:
        raise RuntimeError('Backup repository identity or visibility changed')
    releases, assets = transfer.releases_and_assets()
    release = next(r for r in releases if r['id'] == RELEASE)
    if not release['draft']:
        raise RuntimeError('Expected the preserved draft release')
    by_asset = {a['id']: a for a in assets}
    baseline = json.loads((ROOT / 'ALL_CHECKPOINTS_BASELINE_ASSETS.json').read_text())
    if any(transfer.clean_asset(by_asset.get(a['id'], {})) != a for a in baseline):
        raise RuntimeError('A preexisting asset changed')
    inventory_asset = next(a for a in assets if a['name'] == 'Paper_I_All_Checkpoints_20261024_Source_Inventory.json')
    if inventory_asset['digest'] != 'sha256:e4fa8de7aa107db2c43b40d956c66cd1eff3cdbdd85356f4d06cf9010105cf84':
        raise RuntimeError('The previously verified source inventory digest changed')
    raw, inventory = checked_json(inventory_asset)
    (ROOT / 'ALL_CHECKPOINTS_SOURCE_INVENTORY.json').write_bytes(raw)
    entries = inventory['entries']
    if len(entries) != 1087 or sum(e['size_bytes'] for e in entries) != 50541139865:
        raise RuntimeError('Recovered inventory differs from the previously saved scope')
    batch_assets = sorted([a for a in assets if re.fullmatch(r'Paper_I_All_Checkpoints_20261024_Batch_[0-9]{3}_Receipt.json', a['name'])], key=lambda a:a['name'])
    if len(batch_assets) != 94:
        raise RuntimeError('Expected 94 saved batch receipts')
    state = {'schema_version': 1, 'repository': REPO, 'release_id': RELEASE,
             'status': 'RECOVERED_CATALOG_AUDIT_IN_PROGRESS', 'files': {}, 'batches': [],
             'reconstructed_from_remote_receipts': True, 'reconstructed_at': transfer.now()}
    receipts = ROOT / 'batch_receipts'
    receipts.mkdir(exist_ok=True)
    with ThreadPoolExecutor(max_workers=8) as pool:
        for index, (asset, result) in enumerate(zip(batch_assets, pool.map(checked_json, batch_assets)), 1):
            raw, receipt = result
            if receipt['batch'] != index:
                raise RuntimeError('Batch sequence differs')
            (receipts / asset['name']).write_bytes(raw)
            state['batches'].append({**{k:v for k,v in receipt.items() if k != 'files'},
                                     'receipt_asset': transfer.clean_asset(asset)})
            for record in receipt['files']:
                key = record['library_file_id']
                if key in state['files']:
                    raise RuntimeError('A source occurs in more than one saved receipt')
                state['files'][key] = record
    original = {e['library_file_id']:e for e in entries}
    if len(original) != len(entries) or original.keys() != state['files'].keys():
        raise RuntimeError('Remote receipts do not cover the original inventory exactly')
    aliases = {}
    for key, record in state['files'].items():
        source = original[key]
        if (record['library_path'], record['original_name'], record['size_bytes']) != (source['path'], source['name'], source['size_bytes']):
            raise RuntimeError('Source identity differs from saved inventory')
        if not re.fullmatch('[0-9a-f]{64}', record['sha256']):
            raise RuntimeError('Invalid original hash')
        loc = record['restore_from']
        asset = by_asset[loc['asset_id']]
        if (asset['state'] != 'uploaded' or asset['name'] != loc['asset'] or
                asset['release_id'] != loc['release_id'] or asset['digest'] != 'sha256:' + loc['asset_sha256']):
            raise RuntimeError('A recorded remote restore asset changed')
        if loc['member'] is None and (record['size_bytes'] != asset['size'] or record['sha256'] != loc['asset_sha256']):
            raise RuntimeError('A direct asset differs from its original source')
        if record.get('checkpoint') is None:
            if record['original_name'].startswith('Paper_I_Lean_Iteration_124_'):
                aliases[key] = 124
            elif record['original_name'].startswith('Paper_I_Lean_Pilot_') and '20261009' in record['original_name']:
                aliases[key] = 1
    state['checkpoint_aliases'] = aliases
    state['status'] = 'ALL_INVENTORIED_ORIGINAL_BYTES_BACKED_UP'
    state['inventory_file_count'] = len(entries)
    state['preexisting_assets_unchanged'] = True
    state['manuscript_verification'] = 'INCOMPLETE; backup is not proof verification'
    write_json('ALL_CHECKPOINTS_STATE.json', state)
    write_json('CHECKPOINT_NAME_ALIASES.json', aliases)
    print(json.dumps({'remote_inventory_audit':'PASSED','files':len(entries),'batches':len(batch_assets)}),flush=True)
    with tempfile.TemporaryDirectory(prefix='checkpoint210-restore-') as temporary:
        base = Path(temporary)
        command = [sys.executable, str(ROOT/'restore_original_checkpoint_files.py'),
                   '--catalog', str(ROOT/'ALL_CHECKPOINTS_STATE.json'), '--checkpoint', '210',
                   '--assets', str(base/'assets'), '--destination', str(base/'restored'),
                   '--download', '--gh', str(transfer.GH)]
        with (ROOT/'restore210_execution.log').open('w') as log:
            log.write('Command: ' + ' '.join(command) + '\n')
            log.flush()
            result = subprocess.run(command, stdout=log, stderr=subprocess.STDOUT)
            log.write(f'Exit code: {result.returncode}\n')
        if result.returncode:
            raise RuntimeError('Checkpoint 210 recovery test failed; see the saved execution log')
        shutil.copyfile(base/'restored/RESTORE_RECEIPT.json', ROOT/'RESTORE_CHECKPOINT210_RECEIPT.json')
    for number in (149,152,210):
        receipt = json.loads((ROOT/f'RESTORE_CHECKPOINT{number}_RECEIPT.json').read_text())
        expected = {k for k,r in state['files'].items() if checkpoint_number(r,state)==number}
        if expected != {f['library_file_id'] for f in receipt['files']}:
            raise RuntimeError('Recovery receipt does not cover its selected originals')
        for f in receipt['files']:
            original = state['files'][f['library_file_id']]
            if not f['disk_readback_matched'] or (f['sha256'],f['size_bytes']) != (original['sha256'],original['size_bytes']):
                raise RuntimeError('Recovery receipt differs from the catalog')
    variants = []
    for record in state['files'].values():
        for old in baseline:
            if old['name']==record['original_name'] and old['digest']!='sha256:'+record['sha256']:
                # Verify the separately preserved, same-name variant again.
                with tempfile.TemporaryFile() as output:
                    transfer.api(f"repos/{REPO}/releases/assets/{old['id']}",'-H','Accept: application/octet-stream',output=output)
                    output.seek(0)
                    if 'sha256:'+hashlib.file_digest(output,'sha256').hexdigest()!=old['digest'] or output.tell()!=old['size']:
                        raise RuntimeError('A preserved same-name variant failed readback')
                variants.append({'name':record['original_name'],'inventoried_sha256':record['sha256'],
                                 'inventoried_size':record['size_bytes'],'inventoried_restore':record['restore_from'],
                                 'preserved_variant':old,'fresh_variant_readback_matched':True})
    write_json('PRESERVED_SAME_NAME_VARIANTS.json',variants)
    rows = [{'checkpoint':checkpoint_number(r,state),'original_name':r['original_name'],
             'original_path':r['library_path'],'library_file_id':r['library_file_id'],
             'size_bytes':r['size_bytes'],'sha256':r['sha256'],'status':r['status'],**r['restore_from']}
            for r in state['files'].values()]
    fieldnames = list(dict.fromkeys(k for row in rows for k in row))
    with (ROOT/'ALL_CHECKPOINTS_ORIGINALS.csv').open('w',newline='') as out:
        writer=csv.DictWriter(out,fieldnames=fieldnames);writer.writeheader();writer.writerows(rows)
    coverage=[]
    for number in range(1,211):
        selected=[r for r in rows if r['checkpoint']==number]
        coverage.append({'checkpoint':number,'inventoried_files':len(selected),
                         'inventoried_bytes':sum(r['size_bytes'] for r in selected),
                         'historical_note':('Unconfirmed' if 72<=number<=75 else 'Progress-only material' if number==109 else
                                            'Initial Pilot convention' if number==1 else
                                            'Earlier preserved archive/catalog' if number<=115 else ''),
                         'proof_status':'Not reassessed by this backup'})
    with (ROOT/'CHECKPOINT_COVERAGE.csv').open('w',newline='') as out:
        writer=csv.DictWriter(out,fieldnames=coverage[0]);writer.writeheader();writer.writerows(coverage)
    audit={'status':'ALL_INVENTORIED_ORIGINALS_REMOTE_CATALOG_AUDITED', 'checked_at':transfer.now(),
           'files':len(entries),'original_bytes':inventory['total_original_bytes'],'batches':94,
           'all_94_receipts_freshly_downloaded_and_SHA256_matched':True,
           'inventory_freshly_downloaded_and_SHA256_matched':True,'source_coverage_exactly_once':True,
           'all_restore_asset_digests_match':True,'preexisting_assets_unchanged':len(baseline),
           'restore_tests':[149,152,210],'new_restore_test':210,'same_name_variants':variants,
           'historical_unconfirmed_checkpoints':[72,73,74,75],'progress_only_checkpoint':109,
           'manuscript_or_Lean_modified':False,'new_Lean_build_or_axiom_audit':False,
           'mathematical_verification':'INCOMPLETE','execution_url':f'https://github.com/{REPO}/actions/runs/'+os.environ.get('GITHUB_RUN_ID',''),
           'local_state_loss':'Original workspace regular files became unavailable after uploader exited with code 0; cause not established. Final ledger was reconstructed from preserved GitHub receipt bytes, not recreated console logs.',
           'byte_verification_scope':'Saved batch receipts record original SHA256 checks and fresh download/member verification for new containers. This final audit checks every receipt and remote restore digest, and freshly restores checkpoint 210. Earlier successful restore receipts for 149/152 are preserved.'}
    write_json('ALL_CHECKPOINTS_FINAL_REMOTE_AUDIT.json',audit)
    report=f'''# All available Lean checkpoints: GitHub backup

**All 1,087 inventoried original files are backed up in the private repository.**
The inventory totals 50,541,139,865 bytes before deduplication/compression. All 94 batch
receipts and every recorded remote restore location passed the final catalog audit.
The 44 earlier release assets remain unchanged.

Files: [full original-file index](ALL_CHECKPOINTS_ORIGINALS.csv),
[restore catalog](ALL_CHECKPOINTS_STATE.json), [audit evidence](ALL_CHECKPOINTS_FINAL_REMOTE_AUDIT.json),
[numbered coverage](CHECKPOINT_COVERAGE.csv), and [saved reports and source files](.).

Each new container was downloaded and its original members checked before its batch
receipt was saved. The final audit freshly downloaded all 94 receipts and the original
inventory, checked SHA-256 hashes, exact inventory coverage, and remote asset digests.
Checkpoint 210 was freshly restored from GitHub and every original checked again from disk.
Earlier successful recovery tests for checkpoints 149 and 152 are preserved and matched
against this catalog. Both byte-distinct checkpoint-210 PDF versions remain preserved;
the earlier version also passed a fresh readback during this audit.

Checkpoints **72–75 remain unconfirmed** in the available history. Checkpoint **109 has
progress-only material**. The initial Pilot is counted as checkpoint 1; explicit iteration-124
filenames have an annotated alias. An original artifact is not necessarily a standalone
Lean project; use its own instructions to assemble incremental checkpoints.

**The manuscript and Lean source were not changed. No new Lean compilation or axiom audit
was performed. Mathematical verification remains incomplete.** The backup preserves the
existing correspondence reports, checklists, build evidence, and proof-status limitations.

The local working files became unavailable after the uploader exited. The final catalog
was reconstructed from the saved GitHub receipts. Original console logs that were not
already committed are unavailable; they have not been fabricated. The new recovery execution
is recorded at {audit['execution_url']}. The earlier prepared `finalize_backup_catalog.py`
and `prepare_backup_publication.py` were not executed to completion; this report was produced
by `recover_and_verify_remote_backup.py` instead.

The earlier destination rejection and the tested stricter transfer route are documented
in `ENDPOINT_REVIEW_AND_SAFER_TRANSPORT.json`. Continuation permits only the designated
GitHub API/upload endpoints and credential-free redirects to the repository's GitHub
release-download CDN. Authentication files and credentials are excluded.

To restore original checkpoint-210 artifacts, install `zstandard==0.25.0`, authenticate
GitHub CLI to this private repository, and keep the restore script and strict transport together:

```sh
python3 restore_original_checkpoint_files.py --catalog ALL_CHECKPOINTS_STATE.json \\
  --checkpoint 210 --assets downloaded-assets --destination restored-checkpoint-210 --download
```

Use `--all` instead of `--checkpoint 210` for all inventoried files; the destination must
not exist. Allow space for downloaded containers and the original bytes. This restores
original artifact files, not an automatically assembled or newly verified Lean project.
'''
    (ROOT/'BACKUP_STATUS.md').write_text(report)
    (ROOT/'README.md').write_text(report)
    manifest={}
    allow=[p for p in ROOT.iterdir() if p.is_file() and p.suffix in ('.json','.py','.log','.csv','.md')]
    allow+=sorted(receipts.glob('*.json'))
    for path in allow:
        manifest[str(path.relative_to(ROOT))]={'bytes':path.stat().st_size,'sha256':transfer.sha256(path)}
    archive=ROOT/'Paper_I_All_Checkpoints_GitHub_Backup_Report_20261024.zip'
    with zipfile.ZipFile(archive,'w',zipfile.ZIP_DEFLATED,compresslevel=9) as out:
        out.writestr('REPORT_FILE_HASHES.json',json.dumps(manifest,indent=2)+'\n')
        for path in allow:out.write(path,str(path.relative_to(ROOT)))
    catalog=ROOT/'Paper_I_All_Checkpoints_20261024_Catalog.json'
    shutil.copyfile(ROOT/'ALL_CHECKPOINTS_STATE.json',catalog)
    transfer.UPLOAD_CONTEXT={'release':release,'assets':[a for a in assets if a['release_id']==RELEASE]}
    uploaded=[]
    for path in (catalog,archive):
        uploaded.append(verify_uploaded(transfer.upload_exact(path),path))
    write_json('FINAL_REPORT_ASSET_RECEIPT.json',{'files':uploaded,'checked_at':transfer.now(),'originals':1087})
    parent=transfer.api(f'repos/{REPO}/git/ref/heads/main')['object']['sha']
    if parent!=os.environ['GITHUB_SHA']:
        raise RuntimeError('Main changed while the recovery job ran; publication requires a reviewed new parent')
    base=transfer.api(f'repos/{REPO}/git/commits/{parent}')['tree']['sha']
    text_files=[p for p in ROOT.iterdir() if p.is_file() and p.suffix in ('.json','.py','.log','.csv','.md')]
    text_files+=sorted(receipts.glob('*.json'))
    elements=[{'path':PREFIX+str(p.relative_to(ROOT)),'mode':'100644','type':'blob','content':p.read_text()} for p in text_files]
    root_readme=Path(os.environ['GITHUB_WORKSPACE'])/'README.md'
    original_readme=root_readme.read_text()
    banner=f'> **Complete checkpoint backup:** All 1,087 inventoried originals are saved. [Verified catalog and recovery report]({PREFIX}BACKUP_STATUS.md). Historical checkpoints 72–75 remain unconfirmed.\n\n'
    elements.append({'path':'README.md','mode':'100644','type':'blob','content':banner+original_readme})
    tree=post(f'repos/{REPO}/git/trees',{'base_tree':base,'tree':elements})
    remote=transfer.api(f"repos/{REPO}/git/trees/{tree['sha']}?recursive=1")
    if remote.get('truncated'):raise RuntimeError('Publication tree readback truncated')
    paths={x['path']:x for x in remote['tree']}
    for item in elements:
        data=item['content'].encode()
        digest=hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()
        if paths[item['path']]['sha']!=digest or paths[item['path']]['size']!=len(data):
            raise RuntimeError('A publication blob differs from its intended bytes')
    commit=post(f'repos/{REPO}/git/commits',{'message':'Complete all-checkpoint backup catalog and fresh checkpoint-210 recovery verification','tree':tree['sha'],'parents':[parent]})
    candidate={'status':'VERIFIED_PUBLICATION_COMMIT_READY','parent_sha':parent,'commit_sha':commit['sha'],
               'tree_sha':tree['sha'],'files':1087,'batches':94,'report_assets':uploaded,
               'branch_ref_updated':False,'workflow_run_id':os.environ['GITHUB_RUN_ID']}
    write_json('PUBLICATION_CANDIDATE.json',candidate)
    transfer.upload_exact(ROOT/'PUBLICATION_CANDIDATE.json')
    body=f'All **1,087 inventoried original files** ({inventory["total_original_bytes"]:,} source bytes) are backed up in 94 verified batches.\n\n[Complete catalog and recovery report](https://github.com/{REPO}/blob/{commit["sha"]}/{PREFIX}BACKUP_STATUS.md).\n\nFresh checkpoint-210 recovery passed. Earlier assets remain unchanged. Historical checkpoints 72–75 remain unconfirmed; 109 is progress-only. No manuscript or Lean edits; mathematical verification remains incomplete.'
    post(f'repos/{REPO}/releases/{RELEASE}',{'name':'All inventoried Lean checkpoints through 210 — verified private backup','body':body},'PATCH')
    print('PUBLICATION_CANDIDATE='+json.dumps(candidate),flush=True)


if __name__=='__main__':
    run()
