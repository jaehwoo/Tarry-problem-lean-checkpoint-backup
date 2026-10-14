#!/usr/bin/env python3
"""Resolve the four TAR containers encountered by the initial ZIP/XZ scan."""
import hashlib,json,lzma,re,tarfile,tempfile,zipfile
from pathlib import Path
ROOT=Path(__file__).resolve().parent
OUT=ROOT/'investigation'
d=json.loads((OUT/'archive_scan.json').read_text())
pattern=re.compile(r'(?:check\s*points?|batch)[ _-]*0?(72|73|74|75)(?!\d)',re.I)
roots={r['sha256']:ROOT/r['path'] for r in d['roots']}
def sha(p):
    with p.open('rb') as f:return hashlib.file_digest(f,'sha256').hexdigest()
def copy(f,p):
    h=hashlib.sha256();size=0
    with p.open('wb') as o:
        while b:=f.read(1024*1024):h.update(b);size+=len(b);o.write(b)
    return h.hexdigest(),size
resolved=[]
for error in d['errors']:
    h=error.get('sha256');r=d['archives'].get(h,{})
    if not r.get('name','').endswith('.tar'):continue
    with tempfile.TemporaryDirectory(dir=ROOT/'archive-cache',prefix='tar-followup-') as td:
        chain=r['first_chain'];current=roots[chain[0]['archive_sha256']]
        for j,step in enumerate(chain):
            assert sha(current)==step['archive_sha256']
            target=Path(td)/f'{j}.archive'
            if step['member']=='<xz-decoded-stream>':
                with lzma.open(current,'rb') as f:ch,size=copy(f,target)
            else:
                with zipfile.ZipFile(current) as z,z.open(step['member']) as f:ch,size=copy(f,target)
            expected=next(x['child_sha256'] for x in d['edges'] if x['parent_sha256']==step['archive_sha256'] and x['member']==step['member'])
            assert ch==expected
            if current.parent==Path(td):current.unlink()
            current=target
        assert sha(current)==h
        r['format']='tar';r['members']=[]
        with tarfile.open(current,'r:') as t:
            seen=set()
            for m in t:
                if m.isdir():continue
                if not m.isfile():raise ValueError('Non-file TAR entry')
                if m.name in seen:raise ValueError('Duplicate TAR member')
                seen.add(m.name)
                with t.extractfile(m) as f:
                    data=f.read()
                assert len(data)==m.size
                mh=hashlib.sha256(data).hexdigest()
                r['members'].append({'path':m.name,'bytes':m.size,'sha256':mh})
                if pattern.search(m.name):d['target_name_or_text_hits'].append({'kind':'member_name','archive_sha256':h,'path':m.name})
                if m.name.lower().endswith(('.zip','.xz','.gz','.tar','.tgz','.bz2','.7z')):raise ValueError('Additional nested archive requires handling: '+m.name)
                if m.size<20*1024**2 and m.name.endswith(('.json','.md','.txt','.log','.py','.tex','.lean')):
                    try:text=data.decode('utf-8')
                    except UnicodeDecodeError:continue
                    hits=[{'line':ln,'text':line[:1800]} for ln,line in enumerate(text.splitlines(),1) if pattern.search(line)]
                    if hits:d['target_name_or_text_hits'].append({'kind':'text','archive_sha256':h,'path':m.name,'sha256':mh,'matches':hits})
        r['status']='ALL_TAR_FILE_MEMBERS_HASHED';resolved.append(h)
        print(r['name'],len(r['members']),flush=True)
d['resolved_initial_errors']=d['errors'];d['errors']=[e for e in d['errors'] if e.get('sha256') not in resolved]
(OUT/'archive_scan.json').write_text(json.dumps(d,ensure_ascii=False,indent=2)+'\n')
print('unresolved errors',d['errors'])
