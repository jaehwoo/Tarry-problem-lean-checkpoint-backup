#!/usr/bin/env python3
"""Compare regenerated checkpoint products to historical reference checksums.
A mismatch is reported, not treated as a mathematical error.
"""
from pathlib import Path
import hashlib, json, sys
ROOT=Path(__file__).resolve().parents[1]
ref=json.loads((ROOT/'provenance/original-verification-summary.json').read_text())
rows=[]
for relative,expected in ref['product_sha256'].items():
    p=ROOT/'.lake/build/lib/lean'/relative
    actual=hashlib.sha256(p.read_bytes()).hexdigest() if p.is_file() else None
    rows.append({'product':relative,'historical_sha256':expected,'fresh_sha256':actual,
                 'status':'MISSING' if actual is None else ('MATCH' if actual==expected else 'DIFFERENT')})
result={'scope':'Byte comparison only; see build and endpoint-audit records for verification status.',
        'matched':sum(r['status']=='MATCH' for r in rows),
        'different':sum(r['status']=='DIFFERENT' for r in rows),
        'missing':sum(r['status']=='MISSING' for r in rows),'products':rows}
text=json.dumps(result,indent=2)+'\n'
if len(sys.argv)==2:Path(sys.argv[1]).write_text(text)
else:print(text,end='')
