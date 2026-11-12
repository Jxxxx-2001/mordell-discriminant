# Reproducing the Lean proofs

Use Python 3.11 or later and install Lean through Elan. Each project fixes Lean `v4.30.0`, mathlib commit `c5ea00351c28e24afc9f0f84379aa41082b1188f`, and its transitive dependencies. Run the commands from `formalization/`.

| Project | Final declaration entry |
| --- | --- |
| `chalk_ge10` | [Chalk.lean](chalk_ge10/Chalk.lean) |
| `n6` | [N6/SharpTheorem.lean](n6/N6/SharpTheorem.lean) |
| `n7` | [Upper bound and equality classification](n7/N7/Kernel/Final.lean#L9-L19); [attainment](n7/N7/Witness.lean#L42-L44) |
| `n8` | [Upper bound, equality classification and `complete_8`](n8/Eight/Final.lean#L8-L17); [attainment](n8/Eight/Witness.lean#L116-L117) |
| `n9` | [Upper bound, attainment and equality classification](n9/NineFinal.lean#L7-L21) |

The nine-point link opens an [exact reading copy](n9/README.md) of the final theorem file from the source archive. The build entry remains `Pilot/NineFinal.lean` after extraction.

The final theorems passed the main-project Lean checks and axiom audits. Source integrity is checked against the manifests. The distributed `chalk_ge10` sources also passed an independent rebuild.

The six-point project includes its complete local source closure. See [third-party attribution](n6/THIRD_PARTY.md) for the inherited `Mordell/Interval.lean` file and its unverified redistribution-license status.

For nine points, download both `mordell-n9-lean-sources-part*.zip` assets from the matching [release](https://github.com/Jxxxx-2001/mordell-discriminant/releases/tag/v0.2.0) and place them in one directory. Extract them before running `verify n9` or `build n9`. Extraction verifies archive and member SHA-256 digests.

```sh
python check.py extract n9 --assets /path/to/downloads
```

For each project, replace `chalk_ge10` below with the case to check. `lake exe cache get` obtains the locked third-party dependency cache. Leave the pinned revisions in place.

```sh
python check.py verify chalk_ge10
cd chalk_ge10
lake exe cache get
cd ..
python check.py build chalk_ge10
```

An existing dependency cache can be reused with `python check.py build chalk_ge10 --dependency-cache /path/to/.lake/packages`. The script checks every dependency's pinned Git revision and tracked working-tree state. It still rebuilds every project module in a fresh temporary directory; it does not rebuild mathlib itself.

The build compiles the exact project import closure into a fresh temporary directory and checks the final declarations with `#check` and `#print axioms`. The accepted axioms are `propext`, `Classical.choice`, and `Quot.sound`. `verify` checks input hashes. The seven-, eight- and nine-point proofs use generated Lean certificate modules checked during compilation. The nine-point project sources alone occupy about 3.62 GB uncompressed. Allow additional room for the build and dependency cache.
