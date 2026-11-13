#!/usr/bin/env python3
"""Validate saved bytes, local import closure, and fixed dependency revisions."""
from pathlib import Path
import hashlib, json, re, subprocess, sys

ROOT = Path(__file__).resolve().parents[1]
MATHLIB = 'c44e0c8ee63ca166450922a373c7409c5d26b00b'
TOOLCHAIN = 'leanprover/lean4:v4.19.0'

def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def code_only(text):
    # Lean supports nested block comments. Retain newlines for diagnostics.
    out=[]; i=0; depth=0; string=False
    while i<len(text):
        if depth:
            if text.startswith('/-',i): depth+=1;out.extend('  ');i+=2
            elif text.startswith('-/',i): depth-=1;out.extend('  ');i+=2
            else:out.append('\n' if text[i]=='\n' else ' ');i+=1
        elif string:
            if text[i]=='\\':out.extend('  ');i+=2
            elif text[i]=='"':string=False;out.append(' ');i+=1
            else:out.append('\n' if text[i]=='\n' else ' ');i+=1
        elif text.startswith('/-',i):depth=1;out.extend('  ');i+=2
        elif text.startswith('--',i):
            end=text.find('\n',i)
            if end<0:end=len(text)
            out.extend(' '*(end-i));i=end
        elif text[i]=='"':string=True;out.append(' ');i+=1
        else:out.append(text[i]);i+=1
    if depth or string:raise ValueError('unterminated comment/string')
    return ''.join(out)

def verify(root=ROOT):
    m=json.loads((root/'provenance/source-manifest.json').read_text())
    original=json.loads((root/'provenance/original-verification-summary.json').read_text())
    errors=[]; overrides=[]
    if (root/'lean-toolchain').read_text().strip()!=TOOLCHAIN:errors.append('Lean toolchain mismatch')
    lock=json.loads((root/'lake-manifest.json').read_text())
    pins=json.loads((root/'provenance/dependency-pins.json').read_text())
    if {p['name']:p['rev'] for p in lock['packages']}!=pins['revisions']:
        errors.append('lake-manifest.json revisions differ from frozen pins')
    if pins['revisions'].get('mathlib')!=MATHLIB:errors.append('Mathlib pin mismatch')
    expected=set(m['sources'])
    actual={str(p.relative_to(root)).removesuffix('.lean').replace('/','.') for p in (root/'PaperILean').rglob('*.lean')}
    if actual!=expected:errors.append(f'Source inventory differs: missing={sorted(expected-actual)}, extra={sorted(actual-expected)}')
    for mod,rec in m['sources'].items():
        path=root/rec['path']
        if not path.is_file():errors.append(f'Missing source: {mod}');continue
        if path.is_symlink():errors.append(f'Symlink source forbidden: {mod}');continue
        if digest(path)!=rec['sha256']:errors.append(f'SHA-256 mismatch: {mod}')
        text=code_only(path.read_text())
        forbidden=re.search(r'\b(sorry|admit|axiom)\b',text)
        if forbidden:errors.append(f'Forbidden proof token {forbidden[0]}: {mod}:{text[:forbidden.start()].count(chr(10))+1}')
        imports=[]
        for line in text.splitlines():
            if line.startswith('import '):imports.extend(line[7:].split())
        if imports!=m['imports'][mod]:errors.append(f'Import list mismatch: {mod}')
        for dep in imports:
            if dep.startswith('PaperILean.') and dep not in expected:errors.append(f'Missing dependency: {mod} -> {dep}')
        for hit in re.finditer(r'\bset_option\s+(maxHeartbeats|maxRecDepth)\s+(\d+)',text):
            overrides.append({'module':mod,'option':hit[1],'value':int(hit[2]),'line':text[:hit.start()].count('\n')+1})
    for path,h in original['source_sha256'].items():
        if not (root/path).is_file() or digest(root/path)!=h:errors.append(f'Original checkpoint checksum mismatch: {path}')
    if original['mathlib_commit']!=MATHLIB or original['lean_version']!='4.19.0':errors.append('Original checkpoint pin mismatch')
    order=m['topological_order']
    if len(order)!=len(expected) or set(order)!=expected:errors.append('Incomplete topological order')
    else:
        positions={n:i for i,n in enumerate(order)}
        for n in order:
            for dep in m['imports'][n]:
                if dep in positions and positions[dep]>=positions[n]:errors.append(f'Non-topological dependency: {n} -> {dep}')
    result={'status':'FAIL' if errors else 'PASS','source_count':len(expected),'checkpoint_sources':len(original['source_sha256']),
            'missing_dependencies':m['missing'],'source_option_overrides':overrides,'errors':errors}
    if errors:raise ValueError(json.dumps(result,indent=2))
    return result

def verify_installed_pins(root=ROOT):
    expected=json.loads((root/'provenance/dependency-pins.json').read_text())['revisions']
    records={}
    for name,rev in expected.items():
        d=root/'.lake/packages'/name
        got=subprocess.check_output(['git','-C',str(d),'rev-parse','HEAD'],text=True).strip()
        dirty=subprocess.check_output(['git','-C',str(d),'status','--porcelain','--untracked-files=no'],text=True).strip()
        if got!=rev or dirty:raise ValueError(f'Pinned dependency differs: {name}, expected={rev}, actual={got}, tracked_changes={dirty}')
        records[name]=got
    return records

if __name__=='__main__':
    try:
        result=verify()
        if '--installed' in sys.argv:result['installed_revisions']=verify_installed_pins()
        print(json.dumps(result,indent=2))
    except (ValueError,OSError,subprocess.CalledProcessError) as e:
        print(str(e),file=sys.stderr);sys.exit(1)
