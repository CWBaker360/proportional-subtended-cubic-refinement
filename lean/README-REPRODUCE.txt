Baker proportional-chord cubic-limit source release (packaging revision)
=======================================================================

This folder contains 46 recursively imported Lean modules and the
standalone definition audit (47 Lean files in total), pinned Lean/Mathlib
metadata, and a SHA-256 manifest.

The main theorem is:
  lim_(theta -> 0) (D_(a,b)(theta) - theta/b)/theta^3
    = (a^2 - b^2)/(24*a^2*b^3), for a != 0 and b != 0,
  D_(a,b)(theta) = 2*arcsin((a/b)*sin(theta/(2*a))).

REPRODUCTION -- unpack in a NEW DIRECTORY, then from that directory:
  lake exe cache get
  lake build
  lake env lean BakerProportionalReleaseDefinitionAudit_v1.lean

In PowerShell, run each command separately, then print its exit code:
  Write-Host "Exit code: $LASTEXITCODE"

Expected axiom audit: [propext, Classical.choice, Quot.sound]
No sorryAx should appear. The definition audit prints the actual
proportionalChordResidual and proportionalChord definitions.

The original export had an invalid default target ('BakerTrisection')
whose placeholder source modules were not shipped. This packaging
revision sets the default target to BakerProportionalCubicReleaseAudit_v1
and removes the absent BakerTrisection lean_lib declaration. All 47
Lean source files and pinned dependency metadata remain byte-identical
to the original export. The internal SHA256SUMS.txt has been regenerated.

STATUS: The source chain previously passed Lake compilation in the
user's original project. This CORRECTED ZIP has not yet been built
from a fresh extraction. A successful fresh build remains required.

Notes:
- Fetching the cache requires network access and may be unnecessary
  if dependencies are already available. If cache fetching fails,
  diagnose it separately from Lean source errors.
- SHA256SUMS.txt covers every file except itself.
- This release contains source, not compiled .olean artifacts.
