"""Exact pure-quintic tests before choosing or writing any new Lean proof."""
from fractions import Fraction as Q
from math import factorial
from pathlib import Path
import itertools,json
P=Path(__file__).resolve().parents[1]
def mul(a,b):
 c={}
 for i,x in a.items():
  for j,y in b.items():
   k=tuple(u+v for u,v in zip(i,j));c[k]=c.get(k,0)+x*y
 return {k:v for k,v in c.items() if v}
def deriv(a,j):return {tuple(x-(i==j) for i,x in enumerate(k)):v*k[j] for k,v in a.items() if k[j]}
def inner(a,b):return sum(v*b.get(k,0) for k,v in a.items())
def np(n):return {(i,j,0):(factorial(n)//(factorial(i)*factorial(j)*factorial(n-i-j)))**2 for i in range(n+1) for j in range(n+1-i)}
def val(p,s,g):return sum(c*s**(2*i)*g**(2*j) for (i,j,_),c in p.items())
Ruv=np(5);Duv=np(4)
def R(s,g):return val(Ruv,s,g)
def X(s,g):return 25*val(Duv,s,g)
def E(s,g):return min(1,s*s)*X(s,g)
def qpow(n,s,g):
 q={(1,0,0):Q(1),(0,1,1):-s,(0,0,3):g};p={(0,0,0):Q(1)}
 for _ in range(n):p=mul(p,q)
 return p
values=list(map(Q,['0','1/100','1/2','1','2','10','-1/100','-1/2','-1','-2','-10']))
grams=gsteps=ssteps=scalar_checks=0
for s,g in itertools.product(values,repeat=2):
 p=qpow(5,s,g);ds=[deriv(p,j) for j in range(3)];energies=[inner(d,d) for d in ds]
 assert inner(p,p)==R(s,g) and energies[0]==X(s,g) and energies[1]==s*s*X(s,g)
 assert energies[2]>=energies[1]
 assert all(inner(ds[i],ds[j])==0 for i in range(3) for j in range(3) if i!=j)
 assert min(energies)==E(s,g);grams+=1
 for t in [Q(1,100),Q(1,2),Q(99,100)]:
  if s and g:
   assert R(s,t*g)*E(s,g)<R(s,g)*E(s,t*g);gsteps+=1
  if s and g==0 and abs(s)!=1:
   b=(1-t)*s+t*(1 if s>0 else -1)
   assert R(b,0)*E(s,0)<R(s,0)*E(b,0);ssteps+=1
 assert (E(s,g)==0)==(s==0)
 if s:assert max(sum(k) for k,v in p.items() if v)==(10 if g==0 else 15)
 for c in [Q(0),Q(2),Q(-2)]:
  cp={k:c*v for k,v in p.items()};cd=[deriv(cp,j) for j in range(3)]
  assert inner(cp,cp)==c*c*R(s,g) and min(inner(d,d) for d in cd)==c*c*E(s,g);scalar_checks+=1
assert R(1,0)==252 and E(1,0)==1750 and R(1,0)<2**4*E(1,0)
assert all(R(s,0)==R(s,Q(0)/2) for s in values)
def sub(a,b):return {k:a.get(k,0)-b.get(k,0) for k in set(a)|set(b) if a.get(k,0)!=b.get(k,0)}
def shift(p,j):return {tuple(v+(i==j) for i,v in enumerate(k)):c for k,c in p.items()}
def permute(p,order):return {tuple(k[i] for i in order):v for k,v in p.items()}
def quotient(p,i,j):
 r=dict(p);q={}
 while r and max(k[i] for k in r)>0:
  k=max(r,key=lambda k:k[i]);c=r[k];e=list(k);e[i]-=1;e=tuple(e)
  t={e:c};q[e]=q.get(e,0)+c;r=sub(r,sub(shift(t,i),shift(t,j)))
 assert not r
 return {k:v for k,v in q.items() if v}
def expression(p,vs):
 terms=[]
 for k,c in sorted(p.items()):
  fs=[str(c)]
  for name,n in zip(vs,k):
   if n:fs.append(name if n==1 else name+'^'+str(n))
  terms.append('*'.join(fs))
 return '+'.join(terms)
gf=quotient(sub(mul(Ruv,permute(Duv,(0,2,1))),mul(permute(Ruv,(0,2,1)),Duv)),1,2)
R0={(i,0):c for (i,j,_),c in Ruv.items() if j==0};X0={(i,0):25*c for (i,j,_),c in Duv.items() if j==0};Y0=shift(X0,0)
yf=quotient(sub(mul(R0,permute(Y0,(1,0))),mul(permute(R0,(1,0)),Y0)),1,0)
xf=quotient(sub(mul(R0,permute(X0,(1,0))),mul(permute(R0,(1,0)),X0)),0,1)
for poly in [gf,yf,xf]:assert all(c>0 for c in poly.values()) and poly[(0,)*len(next(iter(poly)))]>0
# Recheck the rejected general contraction using the actual full Gram matrix.
def mixed_ratio(s,g):
 p=qpow(2,s,g)
 for k,c in qpow(8,s,g).items():p[k]=p.get(k,0)+c
 ds=[deriv(p,j) for j in range(3)]
 assert all(inner(ds[i],ds[j])==0 for i in range(3) for j in range(3) if i!=j)
 return inner(p,p)/min(inner(d,d) for d in ds)
s=g=Q(1,100);t=Q(99,100);assert mixed_ratio(s,t*g)>mixed_ratio(s,g)
record=dict(checkpoint=211,full_gram_cases=grams,strict_nonzero_g_contractions=gsteps,strict_zero_g_s_moves=ssteps,scalar_norm_energy_checks=scalar_checks,
 exact_rational=True,passed=True,proof_input=False,stdlib_only=True,
 g_cross_factor=expression(gf,['u','v','w']),zero_g_y_factor=expression(yf,['u','v']),zero_g_x_factor=expression(xf,['u','v']),
 factor_term_counts=[len(gf),len(yf),len(xf)],factor_constants=[gf[(0,0,0)],yf[(0,0)],xf[(0,0)]],
 mixed_profile_counterexample_retained=True,
 new_lean_sources_exist=any((P/'PaperILean'/f'{u}.lean').exists() for u in ['OriginalCubicQuinticRatio','OriginalCubicQuinticState','OriginalCubicQuinticBoundary']),
 obstructions_reviewed=['195 scalar simultaneous saturation','197 affine-centering','198 complete energy order','202 zero-linear attenuation','203 automatic single-power balance and refuted mixed-profile g contraction','204 distinct elliptic invariant','207 pure cube exclusion','210 active-quintic reduction leaves pure quintic and degree>=6 branches'],
 conclusions=['Pure quintics have diagonal complete translation Gram; least energy is25*N4*min(1,s^2).','Contracting nonzero g strictly improves R/E for s!=0; at g=0 it does nothing and needs a separate s curve.','For g=0 move |s| toward1; at |s|=1,R/E=18/125, incompatible with A^4>=16 saturation.','s=0 or scalar c=0 has zero minimum energy and cannot satisfy the positive original stop.','Both deformations preserve the exact degree split10 or15. The universal mixed-profile contraction remains false.'])
assert not record['new_lean_sources_exist']
# At simultaneous norm/translation saturation, scalar shrinking cannot improve both.
for t in [Q(1,100),Q(1,2),Q(99,100)]:
 assert t*t<1 and 1/(t*t)>1
record['simultaneous_saturation_scalar_checks']=3
(P/'evidence/checkpoint_211_pre_strategy.json').write_text(json.dumps(record,indent=2)+'\n');print(json.dumps(record,indent=2))
