#!/usr/bin/env python3
"""Read-only GitHub Release download, hash verification, and isolated restore."""
import hashlib, importlib.util, json, os, platform, shutil, sys, tempfile, time
import urllib.error, urllib.parse, urllib.request
from datetime import datetime, timezone
from pathlib import Path

REPO='jaehwoo/lean-checkpoint-backup'
REPO_ID=1417233863
RELEASE_ID=413227169
CATALOG=Path(__file__).resolve().parent
TOKEN=os.environ['GH_TOKEN']

class NoRedirect(urllib.request.HTTPRedirectHandler):
    def redirect_request(self,req,fp,code,msg,headers,newurl):
        return None

def now():
    return datetime.now(timezone.utc).isoformat()

def api(path,accept='application/vnd.github+json'):
    url='https://api.github.com/repos/'+REPO+('/'+path if path else '')
    request=urllib.request.Request(url,headers={'Authorization':'Bearer '+TOKEN,'Accept':accept,'X-GitHub-Api-Version':'2022-11-28','User-Agent':'Paper-I-private-backup-integrity'})
    return urllib.request.build_opener(NoRedirect()).open(request,timeout=120)

def get(path):
    with api(path) as r:
        return json.load(r)

def check_private():
    d=get('')
    assert d['id']==REPO_ID and d['full_name']==REPO and d['private'] is True and d['visibility']=='private'
    return {'observed_at_utc':now(),'id':d['id'],'full_name':d['full_name'],'private':d['private'],'visibility':d['visibility']}

def download_asset(asset,path):
    # Authentication goes only to api.github.com; it is never forwarded on redirect.
    try:
        response=api('releases/assets/'+str(asset['id']),'application/octet-stream')
    except urllib.error.HTTPError as e:
        if e.code not in (301,302,303,307,308):
            raise
        location=e.headers['Location']
        parts=urllib.parse.urlsplit(location)
        assert parts.scheme=='https' and not parts.username and not parts.password
        assert parts.hostname=='github.com' or parts.hostname.endswith('.githubusercontent.com') or parts.hostname.endswith('.amazonaws.com')
        response=urllib.request.urlopen(urllib.request.Request(location,headers={'User-Agent':'Paper-I-private-backup-integrity'}),timeout=120)
    h=hashlib.sha256();size=0
    with response as r,path.open('xb') as f:
        while chunk:=r.read(1024*1024):
            h.update(chunk);size+=len(chunk);f.write(chunk)
    return size,h.hexdigest()

def digest(path):
    with path.open('rb') as f:
        return hashlib.file_digest(f,'sha256').hexdigest()

def main():
    started=now()
    before=check_private()
    specs=json.loads((CATALOG/'assets.json').read_text())
    sources=json.loads((CATALOG/'sources.json').read_text())
    coverage=json.loads((CATALOG/'coverage.json').read_text())
    release=get('releases/'+str(RELEASE_ID))
    assert release['draft'] is True
    remote={a['name']:a for a in release['assets']}
    assert len(remote)==len(release['assets'])
    assert set(remote)=={s['name'] for s in specs}, 'Unexpected or incomplete asset inventory'
    root=Path(tempfile.mkdtemp(prefix='paper-i-remote-verify-'))
    assets=root/'assets';assets.mkdir()
    verified=[]
    for spec in specs:
        a=remote[spec['name']]
        assert a['state']=='uploaded' and a['size']==spec['bytes']
        if a.get('digest'):
            assert a['digest']=='sha256:'+spec['sha256']
        print('DOWNLOADING',spec['name'],spec['bytes'],flush=True)
        size,h=download_asset(a,assets/spec['name'])
        assert size==spec['bytes'] and h==spec['sha256'], 'Remote bytes mismatch'
        assert digest(assets/spec['name'])==h, 'Downloaded disk readback mismatch'
        record={'id':a['id'],'name':spec['name'],'bytes':size,'sha256':h,'expected_sha256':spec['sha256'],'github_digest':a.get('digest'),'status':'DOWNLOADED_AND_HASH_VERIFIED'}
        verified.append(record);print('VERIFIED',spec['name'],h,flush=True)
    module_spec=importlib.util.spec_from_file_location('original_restorer',CATALOG/'restore.py')
    restorer=importlib.util.module_from_spec(module_spec);module_spec.loader.exec_module(restorer)
    asset_receipt=restorer.verify(assets,sources,specs)
    audit_spec=next(s for s in specs if s['kind']=='archive_member_audit')
    restore_receipt=restorer.restore(assets,sources,coverage,115,root/'restored-115',audit_spec)
    manuscripts=[]
    for p in sorted((root/'restored-115/PaperILean/manuscript').glob('*.tex')):
        manuscripts.append({'name':p.name,'bytes':p.stat().st_size,'sha256':digest(p)})
    assert {m['sha256'] for m in manuscripts}=={'91c19e28f6e6a0733505ce066d6a42be9bfb6df1c8c31185849bc4b34b0ab914','31b5340997aac383d037029596d1c52c88679cab366263b25ecda7d594aef312'}
    package=json.loads((root/'restored-115/PaperILean/checkpoint115_package_manifest.json').read_text())
    manifest_files=0
    for m in package['files']:
        p=root/'restored-115/PaperILean'/m['path']
        assert p.stat().st_size==m['size_bytes'] and digest(p)==m['sha256'], 'Original package manifest mismatch'
        manifest_files+=1
    after=check_private()
    receipt={'status':'REMOTE_DOWNLOAD_HASH_AND_RESTORE_VERIFIED','started_at_utc':started,'finished_at_utc':now(),'verification_environment':'GitHub-hosted Actions runner; actual API downloads, not local staging files or browser metadata','python':platform.python_version(),'repository_before':before,'repository_after':after,'release_id':RELEASE_ID,'release_draft':True,'release_url':release['html_url'],'assets':verified,'asset_and_original_verification':asset_receipt,'restoration':restore_receipt,'restored_original_package_manifest_files':manifest_files,'restored_manuscripts':manuscripts,'source_file_count':len(sources),'source_bytes':sum(s['bytes'] for s in sources),'checkpoint':115,'github_run_id':os.environ.get('GITHUB_RUN_ID'),'github_run_attempt':os.environ.get('GITHUB_RUN_ATTEMPT'),'github_commit':os.environ.get('GITHUB_SHA'),'restore_tool_sha256':digest(CATALOG/'restore.py'),'verification_scope':'Archive bytes and isolated restoration; no Lean recompilation or mathematical verification.'}
    print('REMOTE_VERIFICATION_RECEIPT_START',flush=True)
    print(json.dumps(receipt,sort_keys=True),flush=True)
    print('REMOTE_VERIFICATION_RECEIPT_END',flush=True)
    summary=os.environ.get('GITHUB_STEP_SUMMARY')
    if summary:
        Path(summary).write_text('# Paper I remote backup verified\n\nFive Release assets and 69 original archives passed downloaded-byte verification. Checkpoint 115 restored successfully with '+str(restore_receipt['files'])+' files. Repository remained private. No Lean recompilation was performed.\n')

if __name__=='__main__':
    main()
