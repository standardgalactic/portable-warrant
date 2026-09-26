# The Portable Warrant: Evidence at the Boundary

Publication source distribution for the SCC warrant-preservation paper. The paper is explanatory; the normative software interface lives in the versioned `spec/` directory of `scc-reference`.

## Build

Run `make` with a LaTeX installation containing `pdflatex` and BibTeX. `make verify` checks the distribution manifest after it has been generated.

## Reproducibility snapshot

This release is bound to `scc-reference` 0.4.2 (Portable Kernel). The captured Python suite reports 34 passing tests. BASIC and Forth sources are portability profiles; native execution is not claimed by this snapshot.

## Scope

The software does not establish that a system is universally safe. It provides mechanisms for refusing classes of warrant transfer when preservation evidence is absent under declared transformations, domains, and trusted-computing-base assumptions.


## Expanded theoretical core

The current monograph adds a warrant algebra (attenuation, widening, sequential composition, joins, and explicit non-laws), a dedicated temporal-warrant treatment, a complete neuro-formal counterexample, and a distinction among authentic, sound, complete evidence and truth. Appendices E and F provide a compact algebraic reference and a machine-readable finite counterexample.
