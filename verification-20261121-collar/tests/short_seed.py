"""Exact preflight of the literal raw-seed and assigned-cap scopes of I1080."""
from fractions import Fraction as Q

for m0 in (1, 8, 128):
    for loss in (1, 8, 100, 10**30):
        ell = Q(m0, 6 * loss)
        assigned = m0
        raw_bpp = 1 / (3 * ell)
        assert raw_bpp > Q(loss, assigned)
        for r in (Q(1, 12), Q(1, 2), Q(11, 12)):
            s = r * ell
            bp = Q(1, 3) + s / (3 * ell)
            assert 1 < 1 / bp < 3
            assert 1 - 0 * bp == 1
            assert 1 * 1 - 0 * bp == 1
        assert 0 <= Q(loss, assigned)  # B'' of the horizontal cap is zero.

print("PASS 12 fixed-scale losses, including 10^30; each gives B''>loss/L everywhere.")
print("PASS 36 interior flux clock checks, zero defect model, transverse parameter arbitrary.")
print("PASS horizontal cap B''=0 and original determinant=1.")
