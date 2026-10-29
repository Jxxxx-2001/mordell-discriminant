# Ten points: a strict improvement over the centered nonagon

[中文](README.zh-CN.md) · [Home](../../README.md)

This section proves only $`M_{10}>C_{10}`$, where $`C_{10}=10^{45}/9^{36}`$. It does not determine $`M_{10}`$.

Take

```math
W=\{\pm7,\ \pm21\pm9i,\ \pm8\pm20i\},
```

with independent signs in the two four-point groups. These are ten distinct Gaussian integers, with zero centroid and

```math
\sum_{w\in W}|w|^2=2\cdot49+4(21^2+9^2)+4(8^2+20^2)=4042.
```

Then $`Z=\sqrt{5/2021}\,W`$ satisfies $`\sum|z_i|^2=10`$. Define the positive integer

```math
P=\prod_{i\lt j}|w_i-w_j|^2.
```

Scaling gives

```math
\frac{\Delta(Z)}{C_{10}}=\frac{P\,9^{36}}{4042^{45}}.
```

Exact integer calculation gives $`5P\,9^{36}-6\cdot4042^{45}>0`$. Consequently

```math
M_{10}\ge\Delta(Z)>\frac65 C_{10}>C_{10}.
```

The [certificate](../../verification/n10/exact_counterexample_certificate.json) records the complete integers and coordinates. Recompute all 45 squared distances and the strict comparison using only Python's standard library:

```sh
python verify.py --level check --case n10
```

## Comparison benchmark

Chalk's 1960 counterexample to the original $`n^n`$ conjecture is a regular $`(n-1)`$-gon with its center; it supplies the attainable value $`C_n`$. [Paper](https://doi.org/10.4153/CMB-1960-002-x)
