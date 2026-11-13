# Reproducing the November 13 Paper I checkpoint

The standalone [second-portfolio reproduction package](reproducibility/second-portfolio-20261113/) fixes Lean 4.19.0 and Mathlib `c44e0c8ee63ca166450922a373c7409c5d26b00b`, supplies the unchanged source dependency closure for the three statements, and records fresh compilation and endpoint audit commands.

The package preserves the distinction between retained published theorem inputs and the `#print axioms` results. Consult its recorded execution results and limits; neither this package nor the original checkpoint verifies the complete Tarry convergence theorem or constitutes human verification.

The [dedicated workflow](.github/workflows/reproduce-second-portfolio.yml) can be run manually and checks pull requests that change this package. It publishes build/audit logs as workflow artifacts, including failure logs. The historical checkpoint, manuscript sources, reports, and compiled archives are unchanged.
