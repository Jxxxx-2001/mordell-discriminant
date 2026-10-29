# Verification

Use Python 3.12 or newer. Run commands from the repository root, without `-O`.

```sh
python verify.py
python verify.py --level check --case n10
```

Both commands use only the Python standard library. The default audit checks the SHA-256 manifest, exact values, coefficient bindings, saved certificate status, and cover-count consistency. It also recomputes the ten-point integer witness. It does **not** regenerate a complete cover, re-prove an external classification, or turn a saved `true` into an independent new proof.

For computational checks install the pinned dependencies:

```sh
python -m pip install -r requirements.txt
python verify.py --level check --case n6
python verify.py --level check --case n7
python verify.py --level check --case n8
python verify.py --level check --case n9
```

| Case | What `check` recomputes | Remaining premise |
|---|---|---|
| n2–n5 | The default audit directs readers to the exposition | The n4/n5 global theorems are cited; checking regular-polygon attainment does not prove their upper bounds |
| n6 | Exact field identities, root comparisons and exceptional branches | Saved independent rational CAS completeness evidence; original Singular/Magma input and output are supplied |
| n7 | Ten certified classes plus two exact classes, and their separated objective values | The published complete seven-vortex classification is cited |
| n8 | Exact domain identities, kernel reconstruction, positive definiteness and contact neighborhoods | Saved complete domain-cover certificate |
| n9 | Exact identities and domain bounds, kernel reconstruction, positive definiteness and contact neighborhoods | Saved complete domain-cover certificate |
| n10 | All 45 integer squared distances, their product, normalization and strict comparison | None beyond the explicit integer arithmetic and the elementary scaling argument |

To rerun a complete cover explicitly:

```sh
python verify.py --level replay --case n8
python verify.py --level replay --case n9
```

`replay` for n6 and n7 runs their listed exact checks; it does not silently invoke remote CAS services or regenerate the cited classification. Full n8/n9 covers must finish with zero unresolved boxes. A timeout, missing input, hash mismatch or failed mathematical check exits nonzero. Checks run in separate copies under ignored `build/verification/`; frozen evidence is not overwritten.

The n9 public runner checks the core global theorem. The original proof's additional website-configuration appendix is not a premise of that theorem; its website snapshots are not redistributed or required by the public runner. The original source manifest is retained for provenance, and the publication manifest identifies the selected distributed files.

## Source-preserving changes

`source-map.json` records source-relative locations, original hashes and the few adaptations:

- The n6 runtime metadata has its personal installation path removed; package checksums and mathematical inputs are unchanged.
- The n7 verifier's optional local-PDF checksum I/O is adapted to avoid redistributing a paper. If the PDF is supplied at the original relative location its checksum is checked; otherwise the output explicitly records that no local PDF was checked. The complete-classification theorem remains an external premise in both cases. The original program is retained in `n7/original/`.
- The core n8/n9 mathematical inputs and computational kernels are byte-identical to the source material. Their mathematical summation and equality arguments must be read together with the computational certificates.

No proof-assistant formalization or external peer-review certification is claimed for these six-to-nine-point proofs.

## Maintaining the publication manifest

Git line-ending conversion is disabled for these files so that a checkout preserves the bytes recorded in the manifest.

After reviewing intended changes, explicitly rebuild and audit the file manifest:

```sh
python tools/update_manifest.py
python verify.py
python -m unittest discover -s tests -v
```

Rebuilding a manifest is a distribution operation, not a replacement for mathematical verification.
