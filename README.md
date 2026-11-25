# Sharp molecularity bounds for balanced mass-action realizations

Research manuscript; AI-assisted, not peer reviewed, human authorship pending. This package concerns a prescribed two-species conservation simplex for deterministic ordinary mass action. It does not claim to solve the unrestricted epidemic open problems in Entropy 26 (2024), 936. See the manuscript and `PRIOR_ART.md` for exact scope and limitations.

## Reproduce

The tested toolchain is Lean 4.28.0 with Mathlib v4.28.0 at commit `8f9d9cff6bd728b17a24e163c9402775d9e6a365`. From a Mathlib checkout of this exact revision, run:

```sh
lake env lean /absolute/path/to/lean/FixedPopulation.lean
lake env lean /absolute/path/to/lean/HomogeneousCuts_v04.lean
lake env lean /absolute/path/to/lean/EpidemicApplications.lean
```

The files are standalone; `EpidemicApplications.lean` includes the original FixedPopulation lemmas to keep the application proof independently compilable. Compile each file separately, rather than importing both duplicate namespaces in one module. The accompanying `.lean.log` files are the captured actual runs, with source hashes and exit codes. Audited principal results list only the standard Lean axioms `propext`, `Classical.choice`, and `Quot.sound`. A text check for admitted proof/axiom commands was also performed. The 51-theorem homogeneous-cut development and 39-theorem epidemic development contain 90 distinct theorem declarations. The older source `FixedPopulation.lean` is preserved unmodified.

```sh
python -m pip install numpy scipy sympy
python verify.py
pdflatex manuscript.tex
pdflatex manuscript.tex
```

The independent Python checks have a fixed seed. Rational and symbolic calculations are exact; the separate linear-program solver uses floating-point feasibility and is not a proof. The LaTeX/PDF manuscript contains the mathematical proofs and the mapping from finite networks to the coefficient representation.

No data requiring access credentials are included. No license or formal human authorship has been assigned.
