import hashlib, importlib.util, json, os, tempfile, zipfile
from pathlib import Path

spec=importlib.util.spec_from_file_location('backup_api',Path(__file__).with_name('base_verifier.py'))
base=importlib.util.module_from_spec(spec);spec.loader.exec_module(base)
source=json.loads(Path(__file__).with_name('source.json').read_text())
before=base.check_private()
release=base.get('releases/413240377')
assert release['draft'] is True and len(release['assets'])==1
asset=release['assets'][0]
assert asset['id']==641880174 and asset['name']==source['source']['name'] and asset['size']==source['bytes']
dest=Path(tempfile.mkdtemp(prefix='paper-i-116-remote-'))/asset['name']
size,h=base.download_asset(asset,dest)
assert size==source['bytes'] and h==source['sha256'] and base.digest(dest)==h
with zipfile.ZipFile(dest) as z:
    assert z.testzip() is None
    members=len(z.namelist())
after=base.check_private()
receipt={'status':'REMOTE_PROGRESS_BYTES_VERIFIED','checkpoint':116,'classification':'progress_only','complete_checkpoint':False,'latest_complete_checkpoint':115,'bytes':size,'sha256':h,'zip_members':members,'release_id':release['id'],'asset_id':asset['id'],'repository_before':before,'repository_after':after,'source':source['source'],'run_id':os.environ['GITHUB_RUN_ID'],'commit':os.environ['GITHUB_SHA'],'verification_environment':'GitHub-hosted runner; authenticated remote byte download, disk hash readback and ZIP CRC check','verified_at_utc':base.now()}
print('ADDENDUM_RECEIPT_START')
print(json.dumps(receipt,sort_keys=True))
print('ADDENDUM_RECEIPT_END')
