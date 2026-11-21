"""Exact rational interval and signed-cutoff boundary examples."""
from fractions import Fraction as Q

m = Q(8)
for lo, hi in [(Q(-2), Q(-2)), (Q(1), Q(4)), (Q(-3), Q(5)), (Q(-11), Q(7))]:
    span = hi - lo
    padding = (max(m, span) - span) / 2
    a, b = lo - padding, hi + padding
    assert a <= lo <= hi <= b
    assert b - a == max(m, span)
    assert lo - m / 2 <= a and b <= hi + m / 2
    if span >= m:
        assert a == lo and b == hi
print("PASS closed-endpoint coverage for singleton, shorter, equal and longer spans.")

tau = Q(4)
for height in [Q(0), tau - Q(1, 10**12), tau, tau + Q(1, 10**12)]:
    for residual in [-10**12, -2, 2, 10**12]:
        flux = abs(residual) * height
        if height < tau:
            assert max(m, flux) >= flux
        else:
            assert height <= flux and max(m, flux) <= m / tau * flux
print("PASS both signs immediately below, at and above the height cutoff.")
