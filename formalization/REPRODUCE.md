# Reproducing the Lean proofs

Use Python 3.11 or later and install Lean through Elan. Each project fixes Lean `v4.30.0`, mathlib commit `c5ea00351c28e24afc9f0f84379aa41082b1188f`, and its transitive dependencies. Run the commands from `formalization/`.

| Project | Final declaration entry | Existing verification |
| --- | --- | --- |
| `chalk_ge10` | [Chalk.lean](chalk_ge10/Chalk.lean) | Main project and historical independent build passed. This release candidate passed a fresh build of all three project modules and the final axiom audit on 2026-11-12 (120.63 seconds, pinned dependency cache reused). |
| `n6` | [N6/SharpTheorem.lean](n6/N6/SharpTheorem.lean) | Historical main-project audit passed. All 729 source files match the audited release manifest. Independent release rebuild pending. |
| `n7` | [N7/Kernel/Final.lean](n7/N7/Kernel/Final.lean) and [N7/Witness.lean](n7/N7/Witness.lean) | Main project passed on 2026-11-10 and was revalidated on 2026-11-11. Independent release rebuild pending. |
| `n8` | [Eight/Final.lean](n8/Eight/Final.lean) and [Eight/Witness.lean](n8/Eight/Witness.lean) | Main project passed on 2026-11-03. An independent rebuild was interrupted. |
| `n9` | `Pilot/NineFinal.lean` after extraction | Main project passed on 2026-11-03. An independent rebuild was paused at 1,034 of 3,659 project modules. |

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

An existing dependency cache can be reused with `python check.py build chalk_ge10 --dependency-cache /path/to/.lake/packages`. The script checks every dependency's pinned Git revision and tracked working-tree state. It still rebuilds every project module in a fresh temporary directory; it does not rebuild mathlib itself. This option was used for the local release-candidate check.

The build compiles the exact project import closure into a fresh temporary directory and checks the final declarations with `#check` and `#print axioms`. The accepted axioms are `propext`, `Classical.choice`, and `Quot.sound`. `verify` checks input hashes. The seven-, eight- and nine-point proofs use generated Lean certificate modules checked during compilation. The nine-point project sources alone occupy about 3.62 GB uncompressed. Allow additional room for the build and dependency cache.
