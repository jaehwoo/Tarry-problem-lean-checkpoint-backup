# Paper II Lean verification report

Five whole manuscript statements passed fresh Lean 4.19.0 builds, independent review against the manuscript, and the full scoped declaration audit. The main theorem of Paper II remains unverified.

## Block-triangular degree lift

Statement lines 1567–1569. Proof lines 1570–1576.

The signed determinant of the actual combined sampling minor equals the product of the old-degree determinant and the homogeneous leading determinant in the specified block order.

Fixed affine sample states and the original two distinct-row selections, using the same sample states. The actual coefficient basis discards the constant. Singular minors and an empty old block are covered.

Use the inherited affine substitution and coefficient quotient. Prove degree lowering of the affine-minus-linear leading substitution, derive the four blocks, and take the block-triangular determinant.

Lean endpoints

- `PaperII.DegreeLift.block_triangular_degree_lift`

No published theorem inputs are retained.

## A band interval in the coefficient map

Statement lines 4342–4348. Proof lines 4349–4351.

Replacing the ordinary cubic graph row by the actual null rate preserves corresponding fibers and their common bound, multiplies the inverse density by 2|B|, and bounds the actual band output's Lebesgue length by 2(C₀−c₀)ν.

On a selected regular open branch, the differentiable coefficient atlas retains distinct mixed and ordinary cubic graph rows, and B has a positive uniform lower and finite upper absolute bound. The local graph is C³, the slope is differentiable and zero at the normalized endpoint, and it obeys the actual null equation. The original first-jet vanishings are unnecessary for this calculation.

Differentiate the actual null identity and use its cubic-row relation to construct mutually inverse output changes wherever B is nonzero. Compute the signed determinant by a row operation. Bound the projected band by two signed intervals.

Lean endpoints

- `PaperII.VOutputBand.band_interval_in_coefficient_map`

No published theorem inputs are retained.

## Two quadratic charts cover every first slope

Statement lines 4659–4669. Proof lines 4670–4672.

A single inverse-power threshold gives the weighted-first disjoint cover and both grid estimates for every real slope in the stated conditioned family.

The original upper bounds for r and B, lower bound for |B|, P≥2, and fixed positive grid tolerance. No slope bound is used.

Split at absolute slope one, bound the product AC on the strict weighted complement, and use b²−4AC=B² to bound the mixed pivot and the grid ratio.

Lean endpoints

- `PaperII.TwoQuadraticCharts.two_quadratic_charts`

No published theorem inputs are retained.

## An externally conditioned curved seed

Statement lines 4355–4369. Proof lines 4370–4376.

The actual seed pullback gives both displayed graph-row identities. In the same atlas the ordinary determinant has signed factor −(2B)⁻¹, and the inverse density factors are 2|B| in ordinary coordinates and |B|/3 in Taylor coordinates.

A fixed local C³ seed through the endpoint, the actual normalized critical graph and null equation, nonzero mixed pivot, and the differentiable square atlas retaining the other displayed ordinary graph rows.

Differentiate the actual seed pullback through order three, freeze the first seed slope at the endpoint, and apply the normalized null-row identity. Vary the retained rows in the determinant calculation and eliminate their derivative contributions by multilinearity.

Lean endpoints

- `PaperII.PreparedCurvedSeed.curved_seed_inverse_densities`

No published theorem inputs are retained.

## Quartic connection identity

Statement lines 2472–2489. Proof lines 2490–2492.

The original row annihilates BA+T_z, evaluates to Δ on D, and has the exact compact model denominator (8/3)aB² with a uniform nearby lower bound. The actual moving quartic satisfies the complete body identity, the rate ratio, and its simplification along the null slice.

An actual quartic coefficient phase, selected smooth critical graph, actual differentiable null characteristic and its selected root identity. For the nearby estimate the compact model coefficients a and B have two-sided absolute bounds and the normalized quartic is sufficiently close in its complete coefficients. The null-slice conclusion assumes that slice along the characteristic.

Extract the literal quartic rows. Differentiate the actual normalized affine coefficient orbit to obtain BA+vD+T_z. Transport the original critical root to the same endpoint frame, then use the actual mixed graph derivative to express Δ in three coefficient rows and bound it uniformly near the compact model.

Lean endpoints

- `PaperII.QuarticConnection.quartic_connection_on_characteristic`
- `PaperII.QuarticConnection.quartic_operator_rows`
- `PaperII.QuarticConnection.nullModel_connectionPivot`
- `PaperII.QuarticConnection.normalizedQuartic_hasDerivAt`
- `PaperII.QuarticConnection.normalizedQuartic_uniform_connectionPivot`

No published theorem inputs are retained.

## Verification scope

All five accepted modules passed direct and fresh offline Lake builds with ten matching new products. The combined import check covered 34 explicitly imported modules and their dependency closure. The audit replayed the types and bodies of 274 mathematical declarations and checked the transitive axiom whitelist. All 112 generated compiler entries were independently reviewed separately. The full historical import union was unavailable for a fresh check. Lean 4.19.0 and all nine dependency revisions match the inherited pins. The Apple Silicon compiler uses the same Lean revision as the earlier Linux checkpoint. All inherited kernel objects used by these proofs matched the saved hashes. The three rebuilt editor metadata files with no saved hash are listed separately in the verification record. The 200,000-heartbeat, recursion-depth 512, one-worker and 180/185-second watchdog limits were retained.
