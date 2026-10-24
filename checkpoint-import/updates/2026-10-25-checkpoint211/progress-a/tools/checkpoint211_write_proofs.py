"""Generate pure-quintic proofs after exact obstruction diagnostics; --check is read-only."""
from pathlib import Path
from math import factorial
import json,re,sys
P=Path(__file__).resolve().parents[1]
test=json.loads((P/'evidence/checkpoint_211_pre_strategy.json').read_text())
assert test['passed'] and not test['new_lean_sources_exist']
def emit(p,s):
 if '--check' in sys.argv:assert p.read_text()==s,str(p)
 else:p.write_text(s)
def term(c,es,vs):
 fs=[] if c==1 and any(es) else [str(c)]
 fs += [v if n==1 else v+'^'+str(n) for v,n in zip(vs,es) if n]
 return '*'.join(fs)
def norm(n):return '+'.join(term((factorial(n)//(factorial(i)*factorial(j)*factorial(n-i-j)))**2,(2*i,2*j),('s','g')) for i in range(n+1) for j in range(n+1-i))
def factor(raw,variables):
 terms=[]
 for t in raw.split('+'):
  fs=[]
  for a in t.split('*'):
   m=re.fullmatch(r'([uvw])(?:\^(\d+))?',a)
   fs.append((variables[m[1]]+'^'+str(2*int(m[2] or 1))) if m else a)
  terms.append('*'.join(fs))
 return '+'.join(terms)
s=(P/'PaperILean/OriginalCubicQuarticRatio.lean').read_text()
yold=re.search(r'\(b\^2-a\^2\)\*\((.*?)\) := by',s)[1]
xold=re.search(r'\(a\^2-b\^2\)\*\((.*?)\) := by',s)[1]
gold=re.search(r'min 1 \(s\^2\)\*16\*\(g\^2-h\^2\)\*\s*\((.*?)\) := by',s,re.S)[1]
s=s.replace(yold,factor(test['zero_g_y_factor'],{'u':'a','v':'b'})).replace(xold,factor(test['zero_g_x_factor'],{'u':'a','v':'b'})).replace(gold,factor(test['g_cross_factor'],{'u':'s','v':'g','w':'h'}))
s=s.replace('Quartic','Quintic').replace('quartic','quintic').replace('OriginalCubicFourthProfile','OriginalCubicFifthProfile')
s=s.replace('1+16*a^2+36*a^4+16*a^6+a^8','1+25*a^2+100*a^4+100*a^6+25*a^8+a^10').replace('16*a^2+144*a^4+144*a^6+16*a^8','25*a^2+400*a^4+900*a^6+400*a^8+25*a^10').replace('16+144*a^2+144*a^4+16*a^6','25+400*a^2+900*a^4+400*a^6+25*a^8')
s=s.replace('XEnergy 0 = 16','XEnergy 0 = 25').replace('NormSq 1 = 70','NormSq 1 = 252').replace('Energy 1 = 320','Energy 1 = 1750')
s=re.sub(r'def originalCubicQuinticNormSq \(s g : ℝ\) : ℝ :=\n  .*?\n',lambda m:'def originalCubicQuinticNormSq (s g : ℝ) : ℝ :=\n  '+norm(5)+'\n',s)
s=re.sub(r'def originalCubicQuinticMinEnergy \(s g : ℝ\) : ℝ :=\n  .*?\n',lambda m:'def originalCubicQuinticMinEnergy (s g : ℝ) : ℝ :=\n  min 1 (s^2) * (25*('+norm(4)+'))\n',s)
s=s.replace('min 1 (s^2)*16*','min 1 (s^2)*25*').replace('noncomputable section','set_option maxRecDepth 8192\nnoncomputable section')
emit(P/'PaperILean/OriginalCubicQuinticRatio.lean',s)
s=(P/'PaperILean/OriginalCubicQuarticState.lean').read_text().replace('Quartic','Quintic').replace('quartic','quintic')
s=s.replace(')*4',')*5').replace('ℝ)^4','ℝ)^5').replace('s g^4','s g^5').replace('(g t)^4','(g t)^5')
s=s.replace('original_centered_cubic_fourth_norm','original_centered_cubic_fifth_norm')
s=s.replace('16*('+norm(3)+')','25*('+norm(4)+')')
s=s.replace('norm_num [original_centered_cubic_cube_norm]','norm_num [original_centered_cubic_fourth_norm]')
a=s.index('theorem original_centered_quintic_expansion');b=s.index('theorem originalCubicQuinticState_continuous',a)
terms=[]
for i in range(6):
 for j in range(6-i):
  x=5-i-j;c=factorial(5)//(factorial(x)*factorial(i)*factorial(j))
  coeff=term(c,(i,j),('s','g'));mono='*'.join('X '+str(k)+(('^'+str(e)) if e!=1 else '') for k,e in enumerate([x,i,i+3*j]) if e)
  body=('C ('+coeff+')*('+mono+')') if (i or j) else mono
  terms.append(('-' if i%2 else '+',body))
expansion=terms[0][1]+''.join(' '+sign+'\n      '+body for sign,body in terms[1:])
s=s[:a]+'''theorem original_centered_quintic_expansion (s g : ℝ) :
    originalCenteredCubicInvariant s g^5 =
      '''+expansion+''' := by
  simp only [originalCenteredCubicInvariant,map_mul,map_pow,map_ofNat]
  ring

'''+s[b:]
emit(P/'PaperILean/OriginalCubicQuinticState.lean',s)
s=(P/'PaperILean/OriginalCubicQuarticBoundary.lean').read_text().replace('Quartic','Quintic').replace('quartic','quintic').replace(')*4',')*5').replace('s g^4','s g^5')
a=s.index('theorem original_centered_far_closure_quintic_zero')
s=s[:a]+'''theorem original_centered_far_closure_quintic_zero {k N : ℕ}
    (F : CoefficientSpace k) {s : ℝ} (hs : s ≠ 0) (g : ℝ) (f : Polynomial ℝ)
    (hf : 2 ≤ f.natDegree) (hcap : (if g = 0 then 2 else 3)*f.natDegree ≤ k)
    (hF : coefficientPolynomial F = f.eval₂ C (originalCenteredCubicInvariant s g)-C (f.coeff 0))
    {A B : ℝ} (hA : 2 ≤ A) (ht : AugmentedTranslationStopped A (F,0))
    (hcl : (A,(F,0)) ∈ closure (originalFarBoundedFamily k N B)) : f.coeff 5 = 0 := by
  by_contra ha
  have hphase := original_centered_far_closure_fifth_phase F hs g f hf hcap hF hA ht hcl ha
  have hd : 5 ≤ f.natDegree := Polynomial.le_natDegree_of_ne_zero ha
  have hk : (if g = 0 then 2 else 3)*5 ≤ k := (Nat.mul_le_mul_left _ hd).trans hcap
  exact original_centered_quintic_not_mem_far_closure F hs g (f.coeff 5) ha hk hphase hA ht hcl

theorem original_centered_far_closure_through_quintic_zero {k N : ℕ}
    (F : CoefficientSpace k) {s : ℝ} (hs : s ≠ 0) (g : ℝ) (f : Polynomial ℝ)
    (hf : 2 ≤ f.natDegree) (hcap : (if g = 0 then 2 else 3)*f.natDegree ≤ k)
    (hF : coefficientPolynomial F = f.eval₂ C (originalCenteredCubicInvariant s g)-C (f.coeff 0))
    {A B : ℝ} (hA : 2 ≤ A) (ht : AugmentedTranslationStopped A (F,0))
    (hcl : (A,(F,0)) ∈ closure (originalFarBoundedFamily k N B)) :
    f.coeff 1 = 0 ∧ f.coeff 2 = 0 ∧ f.coeff 3 = 0 ∧ f.coeff 4 = 0 ∧ f.coeff 5 = 0 ∧ 6 ≤ f.natDegree := by
  obtain ⟨ha1,ha2,ha3,ha4,hf5⟩ := original_centered_far_closure_through_quartic_zero F hs g f hf hcap hF hA ht hcl
  have ha5 := original_centered_far_closure_quintic_zero F hs g f hf hcap hF hA ht hcl
  refine ⟨ha1,ha2,ha3,ha4,ha5,?_⟩
  by_contra! hd
  have hd4 : f.natDegree ≤ 4 := by
    apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
    intro n hn
    by_cases hn5 : n = 5
    · simpa only [hn5] using ha5
    · exact Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
  omega

end PaperI
'''
emit(P/'PaperILean/OriginalCubicQuinticBoundary.lean',s)
print('Source generator matches.' if '--check' in sys.argv else 'Generated three unexecuted modules; compilation and audits required.')
