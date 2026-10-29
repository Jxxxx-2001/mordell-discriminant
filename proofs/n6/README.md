# 6 points: the centered regular pentagon

[中文](README.zh-CN.md) · [Home](../../README.md)

## Theorem

For $`\sum|z_i|^2=6`$,

```math
M_6=C_6=6^{15}/5^{10}.
```

Equality holds exactly for

```math
\{0\}\cup\left\{\sqrt{\frac{6}{5}}e^{i\theta+2\pi i k/5}:k=0,\ldots,4\right\},
```

up to rotation and relabeling. There is no additional translation freedom.

## Proof

The full proof reduces arbitrary maximizers to stationary polynomial branches without assuming symmetry. A resultant identity gives the coefficient equations. The generic saturated ideal has quotient dimension 35; exact substitution into 35 graph solutions and an independently computed rational CAS dimension establish both ideal inclusions. Exact real-root isolation excludes the competing branches. The exceptional, centrally symmetric and threefold-symmetric branches are handled separately; only the centered pentagon attains the maximum.

The saved Singular and Magma inputs, outputs and exact comparison data are included. `check` redoes the post-CAS identities, real-root comparisons and exceptional cases; it uses the saved CAS completeness evidence rather than recomputing that CAS step. Reproducing the original independent dimension calculation requires Singular/Magma and the documented input files.

[Complete proof in Chinese](../../verification/n6/GLOBAL_PROOF.txt) · [Final certificate](../../verification/n6/global_verification.json)

```sh
python verify.py --case n6
python verify.py --level check --case n6
```
