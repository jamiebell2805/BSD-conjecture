# Formalising BSD

A first-year project at LSGNT, supervised by Kevin Buzzard.

## Aim of the project

The aim of this project was to use Lean formalise some of the definitions around elliptic curves, specifically in order to state the BSD Conjecture.

## What did we achieve?

The result for curves over the rationals is a lean file which, if the sorrys were filled in with proofs, would be a full proof of BSD.
In the number field case, in the file elliptic_curve_nf.lean, there are more definitions needed to give the analytic rank.
Along the way, it was necessary to define infinite products and prove that a quotient of a finitely-generated group is finitely generated. These are in separate files called tprod.lean and fg_quotient.lean.

More details and explanation about the project are in the directory pdf.

## Installation

If you have Lean 3 installed, you can get this code by opening a command line, navigating to the correct directory, and typing

    leanproject get jamiebell2805/BSD-conjecture
    code BSD-conjecture

If you do not have Lean installed, instructions to do so are aavailable at the [leanprover community](https://leanprover-community.github.io/get_started.html)
