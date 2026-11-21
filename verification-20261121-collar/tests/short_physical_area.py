"""Exact identities for the local transverse-collar test in I.1062–1073."""

from fractions import Fraction
from sympy import Matrix, Rational, diff, simplify, symbols

x, y, z, gamma, s, t, f = symbols("x y z gamma s t f", real=True)
c = y*z - gamma*z**3/3
phase = (x - c)**2
d = gamma*z
assert simplify(diff(c,y,2)*d**2 + 2*diff(c,y,z)*d + diff(c,z,2)) == 0
assert diff(c,y,z) == 1 and diff(phase, x, 2) == 2
assert diff(d,y) == 0 and simplify(diff(d,z) + d*diff(d,y)) == gamma
midpoint = 2*z + gamma*z**2/2
assert simplify(diff(midpoint,z)-d) == 2
b = s/2
a = midpoint.subs(z,b)
F = b+t
Y = a + d.subs(z,b)*t + gamma*t**2/2
assert simplify(Y - (s+gamma*F**2/2)) == 0
assert simplify(Y - gamma*F*F - (s-gamma*F**2/2)) == 0
assert simplify(Matrix([Y,F]).jacobian([s,t]).det()) == 1
assert Matrix([s-gamma*f**2/2,f]).jacobian([s,f]).det() == 1

# Common-candidate bound in the note, for a fixed example good fraction and T.
T = Fraction(1)
good_fraction = Fraction(1, 2)
h = good_fraction*T/2
candidate_lower = good_fraction*T*h**2/2
print("Exact identities: null slope, pivot, residual, collar map and Jacobians pass.")
for k in (4, 8, 16, 32):
    ell = Fraction(1,2**k)
    print(f"ell=2^-{k}, raw area={2*T*ell}, "
          f"candidate/whole-raw-area >= {candidate_lower/(2*T*ell)}")
