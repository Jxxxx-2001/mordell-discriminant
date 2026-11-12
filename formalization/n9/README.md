# Nine-point final theorems

[Read the final theorems](NineFinal.lean#L7-L21):

- `MordellNine.mordell9_upper`: the global upper bound under the original energy constraint.
- `MordellNine.mordell9_attainment`: the centered regular octagon attains the bound.
- `MordellNine.mordell9_equality_iff`: all equality cases, up to rotation and relabeling.

`NineFinal.lean` is a byte-for-byte reading copy of `Pilot/NineFinal.lean` in the Release source archive. Its SHA-256 is `2e68ecf92cbadb163e7825357343a9272fc54862512cfe2269b5ad8d31e2c15a`, as recorded for `Pilot/NineFinal.lean` in [SOURCE_MANIFEST.json](SOURCE_MANIFEST.json).

To compile the proof, follow the [reproduction guide](../REPRODUCE.md) and extract both source archives. The build uses `Pilot/NineFinal.lean` and its complete dependency closure; this reading copy does not change the extraction or build commands.
