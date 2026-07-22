# A Local Cubic Refinement Law for Proportional-Subtended Angle Division

**Author:** Wayne Baker  
**Date:** July 2, 2026  
**Status:** Preprint / source archive

This repository contains the LaTeX source and compiled PDF for:

> **A Local Cubic Refinement Law for Proportional-Subtended Angle Division**

## Read the paper

## Read the paper

- [Read the paper (PDF)](Paper/local_cubic_refinement_proportional_subtended.pdf)
- [LaTeX source](Paper/local_cubic_refinement_proportional_subtended.tex)

## Main result

For positive integers \(a\) and \(b\), define the proportional-subtended seed operator

\[
D_{a,b}(\theta)
=
2\arcsin\!\left(
\frac{a}{b}\sin\frac{\theta}{2a}
\right).
\]

On the local principal branch,

\[
D_{a,b}(\theta)-\frac{\theta}{b}
=
\frac{a^2-b^2}{24a^2b^3}\theta^3
+
O(\theta^5).
\]

For a signed error \(e\), define

\[
\Phi_{a,b}(x)
=
2\arcsin\!\left(
\frac{a}{b}\sin\frac{x}{2}
\right),
\qquad
\mathcal R_{a,b}(e)
=
e-\Phi_{a,b}\!\left(\frac{b}{a}e\right).
\]

For every nonidentity branch \(a\ne b\),

\[
\mathcal R_{a,b}(e)
=
-\frac{a^2-b^2}{24a^2}e^3
+
O(e^5).
\]

The scale factor \(b/a\) is the unique constant scaling that cancels the linear term in the one-transfer correction class. Repeated residual correction therefore produces the local order sequence

\[
3,\;9,\;27,\;81,\ldots
\]

## Scope

The theorem is local and asymptotic. It is not a global angle-division theorem.

A direct finite straightedge-and-compass realization is proved for the repeated-bisection subclass \(a=2^m\). The paper also gives a two-sample chord calculation whose residual begins at fifth order.

## Historical note

The motivating \(4:3\) branch is Wayne Baker's approximate-trisection construction. Rouben Rostamian analyzed that special case, including its cubic seed error and the ninth-order error produced by one residual improvement. The present paper develops the general \((a,b)\) law and the associated uniqueness and sharpness results.

## Companion paper

The specific constructible \(4:3\) trisection branch is developed in:

> **A Constructible Cubic Error Cascade for Approximate Angle Trisection**

Repository:

`https://github.com/CWBaker360/constructible-cubic-trisection`

## Repository structure

```text
.
├── README.md
├── CITATION.cff
├── REPRODUCIBILITY.md
├── LICENSE_NOTICE.md
├── CHANGELOG.md
├── SHA256SUMS.txt
├── .gitignore
├── paper/
│   ├── local_cubic_refinement_proportional_subtended.tex
│   ├── local_cubic_refinement_proportional_subtended.pdf
│   └── README.md
├── docs/
│   ├── abstract.md
│   ├── repository_description.md
│   ├── github_upload_checklist.md
│   └── first_repository_readme_patch.md
├── figures/
│   └── .gitkeep
└── scripts/
    └── .gitkeep
```

## Compilation

From the `paper` directory:

```bash
pdflatex local_cubic_refinement_proportional_subtended.tex
pdflatex local_cubic_refinement_proportional_subtended.tex
```

## Rights

Copyright © 2026 Wayne Baker. All rights reserved unless otherwise stated.
