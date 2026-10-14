#!/usr/bin/env python3
"""Read-only provenance scan; no archive code is executed."""
import hashlib, json, lzma, os, re, shutil, stat, sys, tempfile, zipfile
from pathlib import Path, PurePosixPath

ROOT = Path(__file__).resolve().parent
OUT = ROOT / 'investigation'
OUT.mkdir(exist_ok=True)
CACHE = ROOT / 'archive-cache'
CACHE.mkdir(exist_ok=True)
coverage = json.loads((ROOT/'baseline/coverage.json').read_text())
known = {x['archive_sha256']: int(n) for n, xs in coverage['checkpoint_archives'].items() for x in xs}
targets = {n: coverage['checkpoint_archives'][str(n)][0]['archive_sha256'] for n in (71,76)}
pattern = re.compile(r'(?:check\s*point|batch)[ _-]*0?(72|73|74|75)(?!\d)', re.I)
archives, edges, hits, roots, errors = {}, [], [], [], []
texts_seen = set()
if '--resume' in sys.argv:
    previous=json.loads((OUT/'archive_scan.json').read_text())
    archives=previous['archives'];edges=previous['edges'];hits=previous['target_name_or_text_hits'];roots=previous['roots'];errors=previous['errors']
    texts_seen={m['sha256'] for r in archives.values() for m in r.get('members',[]) if 'sha256' in m}

def digest(path):
    with path.open('rb') as f:
        return hashlib.file_digest(f, 'sha256').hexdigest()

def copy_hash(reader, out):
    h=hashlib.sha256(); size=0
    while b:=reader.read(1024*1024):
        h.update(b); size+=len(b)
        if out is not None: out.write(b)
    return h.hexdigest(),size

def checkpoint():
    data={'schema':1,'roots':roots,'archives':archives,'edges':edges,'target_name_or_text_hits':hits,'errors':errors,'scope':'Container bytes, member inventories, and textual provenance; no Lean compilation.'}
    tmp=OUT/'archive_scan.json.tmp';tmp.write_text(json.dumps(data,ensure_ascii=False,indent=2)+'\n');tmp.replace(OUT/'archive_scan.json')

def scan(path, name, chain, expected=None):
    h=digest(path)
    if expected and h!=expected: raise ValueError('Nested archive hash mismatch')
    if h in archives: return h
    if len(archives)>1000: raise ValueError('Container limit exceeded')
    rec={'sha256':h,'name':name,'bytes':path.stat().st_size,'first_chain':chain,'baseline_checkpoint':known.get(h)}
    archives[h]=rec
    # Reuse the earlier verified catalog below the interval being investigated.
    if h in known and known[h]<=70:
        rec['status']='REUSED_BASELINE_CATALOG'; checkpoint();return h
    print('SCAN',name,h[:12],flush=True)
    children=[]
    if zipfile.is_zipfile(path):
        rec['format']='zip';rec['members']=[]
        with zipfile.ZipFile(path) as z:
            names=[i.filename for i in z.infolist() if not i.is_dir()]
            if len(names)!=len(set(names)): raise ValueError('Duplicate member names')
            for i in z.infolist():
                if i.is_dir(): continue
                if i.file_size>2*1024**3: raise ValueError('Member limit exceeded')
                m={'path':i.filename,'bytes':i.file_size,'crc32':f'{i.CRC:08x}'}
                rec['members'].append(m)
                if pattern.search(i.filename):hits.append({'kind':'member_name','archive_sha256':h,'path':i.filename})
                nested=i.filename.lower().endswith(('.zip','.xz','.gz','.tar','.tgz','.bz2','.7z'))
                if nested:
                    fd, tmpname=tempfile.mkstemp(prefix='nested-',dir=CACHE);os.close(fd);tmp=Path(tmpname)
                    with z.open(i) as f,tmp.open('wb') as o: mh,size=copy_hash(f,o)
                    m['sha256']=mh
                    if size!=i.file_size:raise ValueError('Size mismatch')
                    edges.append({'parent_sha256':h,'member':i.filename,'child_sha256':mh,'bytes':size})
                    children.append((tmp,i.filename,chain+[{'archive_sha256':h,'member':i.filename}],mh))
                else:
                    with z.open(i) as f: mh,size=copy_hash(f,None)
                    m['sha256']=mh
                    if size!=i.file_size:raise ValueError('Size mismatch')
                    if mh not in texts_seen and i.file_size<20*1024**2 and i.filename.endswith(('.json','.md','.txt','.log','.py','.tex','.lean')):
                        texts_seen.add(mh)
                        try: text=z.read(i).decode('utf-8')
                        except UnicodeDecodeError: continue
                        matches=[]
                        for ln,line in enumerate(text.splitlines(),1):
                            if pattern.search(line):matches.append({'line':ln,'text':line[:1800]})
                        if matches:hits.append({'kind':'text','archive_sha256':h,'path':i.filename,'sha256':mh,'matches':matches})
        rec['status']='ALL_MEMBERS_HASHED_AND_ZIP_CRC_READ'
    elif path.read_bytes()[:6]==b'\xfd7zXZ\x00':
        rec['format']='xz'
        fd,tmpname=tempfile.mkstemp(prefix='xz-',dir=CACHE);os.close(fd);tmp=Path(tmpname)
        with lzma.open(path,'rb') as f,tmp.open('wb') as o:mh,size=copy_hash(f,o)
        m={'path':'<xz-decoded-stream>','sha256':mh,'bytes':size};rec['members']=[m]
        edges.append({'parent_sha256':h,'member':m['path'],'child_sha256':mh,'bytes':size})
        children.append((tmp,name.removesuffix('.xz'),chain+[{'archive_sha256':h,'member':m['path']}],mh))
        rec['status']='DECOMPRESSED_AND_HASHED'
    else:
        rec['status']='UNSUPPORTED_CONTAINER';errors.append({'sha256':h,'name':name,'reason':'unsupported format'})
    for n,th in targets.items():
        if h==th:
            destination=OUT/f'original_checkpoint_{n}.zip'
            if not destination.exists():shutil.copyfile(path,destination)
            if digest(destination)!=h:raise ValueError('Target copy hash mismatch')
            rec['retained_as']=destination.name
    checkpoint()
    for tmp,cn,cc,mh in children:
        try:scan(tmp,cn,cc,mh)
        finally:tmp.unlink(missing_ok=True)
    checkpoint()
    return h

paths=list((ROOT/'candidates').rglob('*.zip'))
paths.sort(key=lambda p:(0 if 'Through_82' in p.name else 1 if 'Through_93' in p.name else 2 if 'History_Checkpoint_104' in p.name else 3,str(p)))
for p in paths:
    if any(r['path']==str(p.relative_to(ROOT)) for r in roots):continue
    h=digest(p);roots.append({'path':str(p.relative_to(ROOT)),'sha256':h,'bytes':p.stat().st_size})
    try:scan(p,p.name,[] ,h)
    except Exception as e:
        errors.append({'root':str(p),'error':repr(e)});checkpoint();raise
checkpoint()
print(json.dumps({'roots':len(roots),'containers':len(archives),'edges':len(edges),'hits':len(hits),'errors':errors}),flush=True)
