# Verification

Use Python 3.12 or newer. Run commands from the repository root, without `-O`.

```sh
python verify.py
python verify.py --level check --case n10
```

Both commands use only the Python standard library. The default audit checks the SHA-256 manifest, exact values, coefficient bindings, saved certificate status, and cover-count consistency. It also recomputes the small-integer ten-point witness. The explicit n10 check also verifies the 1999 coordinates. It does **not** regenerate a complete cover, re-prove an external classification, or turn a saved `true` into an independent new proof.

For computational checks install the pinned dependencies:

```sh
python -m pip install -r requirements.txt
python verify.py --level check --case n6
python verify.py --level check --case n7
python verify.py --level check --case n8
python verify.py --level check --case n9
python verify.py --level check --case ratio
```

| Manuscript section and case | What `check` recomputes | Remaining premise |
|---|---|---|
| §2, n2–n5 | The default audit directs readers to the exposition | The n4/n5 global theorems are cited; checking regular-polygon attainment does not prove their upper bounds |
| §3, n6 | The sextic resultant and four necessary coefficient equations, then exact field identities, root comparisons and exceptional branches | Saved independent rational CAS completeness evidence; original Singular/Magma input and output are supplied |
| §3, n7 | Ten certified classes plus two exact classes, and their separated objective values | The published complete seven-vortex classification is cited |
| §4, n8 | Exact domain identities, kernel reconstruction, positive definiteness and contact neighborhoods | Saved complete domain-cover certificate |
| §4, n9 | Exact identities and domain bounds, kernel reconstruction, positive definiteness and contact neighborhoods | Saved complete domain-cover certificate |
| §5, n10 | Both ten-point witnesses, including the coordinates of Gueron and Shafrir. Each requires 45 positive squared distances and a strict product comparison | The uniform explicit construction for every $n\ge10$ is checked separately in [Lean](../formalization/chalk_ge10/Chalk.lean); see the [proof](../proofs/n10/README.md) |
| §6 and Appendix C, ratio | All pair distances of the three integer sets, their extrema and three rigorous comparisons with the centered polygons | The constructions for eight points and all $n\ge12$ are analytic. See the [proof](../proofs/ratio/README.md) |

To rerun a complete cover explicitly:

```sh
python verify.py --level replay --case n8
python verify.py --level replay --case n9
```

`replay` for n6 and n7 runs their listed exact checks; it does not silently invoke remote CAS services or regenerate the cited classification. Full n8/n9 covers must finish with zero unresolved boxes (193458 terminal boxes for n8 and 15807 for n9). A timeout, missing input, hash mismatch or failed mathematical check exits nonzero. Checks run in separate copies under ignored `build/verification/`; frozen evidence is not overwritten.

The n9 public runner checks the core global theorem. The original proof's additional website-configuration appendix is not a premise of that theorem; its website snapshots are not redistributed or required by the public runner. Original input hashes are recorded in `source-map.json`. The case manifests bind the distributed proof inputs, and the publication manifest records all distributed files.

The resultant bridge and historical ten-point checker are taken from the manuscript supplements S6 and S10. The ratio checker uses the three sets in Appendix C.

## Source-preserving changes

`source-map.json` records source-relative locations, original hashes and the few adaptations:

- The n6 runtime metadata has its personal installation path removed; package checksums and mathematical inputs are unchanged.
- The n7 verifier's optional local-PDF checksum I/O is adapted to avoid redistributing a paper. If the PDF is supplied at the original relative location its checksum is checked; otherwise the output explicitly records that no local PDF was checked. The complete-classification theorem remains an external premise in both cases. The original program is retained in `n7/original/`.
- The core n8/n9 mathematical inputs and computational kernels are byte-identical to the source material. Their mathematical summation and equality arguments must be read together with the computational certificates.

This page describes the Python verification suite. The Lean formalizations and their reproduction commands are documented [separately](../formalization/REPRODUCE.md).

## Maintaining the publication manifest

Git line-ending conversion is disabled for these files so that a checkout preserves the bytes recorded in the manifest.

After reviewing intended changes, explicitly rebuild and audit the file manifest:

```sh
python tools/update_manifest.py
python verify.py
python -m unittest discover -s tests -v
```

Rebuilding a manifest is a distribution operation, not a replacement for mathematical verification.
