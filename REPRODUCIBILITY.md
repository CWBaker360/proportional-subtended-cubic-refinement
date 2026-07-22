# Reproducibility

## Paper compilation

The authoritative source is:

```text
Paper/local_cubic_refinement_proportional_subtended.tex
```

Compile from the `Paper` directory using:

```bash
pdflatex local_cubic_refinement_proportional_subtended.tex
pdflatex local_cubic_refinement_proportional_subtended.tex
```

The second pass resolves references and page numbers.

## Symbolic verification

Appendix A of the paper records a SymPy recipe for verifying the seed, residual, and two-sample coefficients.

Suggested environment:

```text
Python 3.10 or later
SymPy 1.12 or later
```

The symbolic computation is a reproducibility aid. The proofs in the manuscript are formal series derivations and do not depend on numerical fitting.

## Numerical checks

The numerical tables are consistency checks only. They do not prove the local theorems, establish global convergence, or enlarge the finite Euclidean realization claim.

## Integrity

Run a SHA-256 verification against `SHA256SUMS.txt` after extracting the archive.
