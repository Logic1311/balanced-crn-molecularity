# Status of research candidate 01 — v0.4

Date: 2026-11-26 (JST).

This version narrows the original epidemic-realization exploration to a self-contained research manuscript, *Sharp molecularity bounds for balanced mass-action realizations on a two-species conservation class*. The original v0.1 draft and v0.2 checkpoint remain separate. The central results are the exact molecularity-cap characterization on a prescribed simplex, the sharp cubic parity thresholds, and the unbounded degree gap. The global-versus-fixed-class and classical epidemic results are supporting applications, with known geometric overlap clearly identified.

- **Mathematical proof:** complete for the explicitly scoped manuscript. The main criterion is for same-species ordinary mass action with integer complexes, nonnegative rates (zero meaning absent), and edge-wise total conservation. It is not a theorem about arbitrary chemistry or stochastic equivalence.
- **Lean:** 51 theorems in `HomogeneousCuts_v04.lean`, 39 in `EpidemicApplications.lean`. The original 31 theorems appear again in the latter and are not counted twice. All three files separately compiled with exit code 0; hashes and logs checked against the actual source bytes. No `sorry`, `admit`, extra axiom commands or `sorryAx` dependency in the audited outputs. Auxiliary analytic-only statements are identified in Section 7.
- **Independent checks:** 2,400 exact rational network identities, 700 full directed-flow LP comparisons, 297 exact threshold checks, 11 symbolic identities; all passed. These are implementation checks, not substitutes for proof.
- **Novelty:** no identical focused fixed-class cap theorem and cubic molecularity bound located in inspected sources. Closest prior work concerns global collinear/flux realization, so priority claims are explicitly limited. Direct Google Scholar access was unavailable; expert review remains outstanding. See `PRIOR_ART.md`.
- **Research integrity:** AI contributed substantially. Not peer reviewed. Human authorship, accountability and journal submission require confirmation. No definitive priority, citation impact or journal acceptance is asserted.
- **Not completed:** unrestricted Entropy Open Problems 2/5, general WR/WR0 classification, and minimum number of reactions in general. These are not advertised as established or counted as additional papers.
