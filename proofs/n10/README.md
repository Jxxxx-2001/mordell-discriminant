# Why Chalk’s configuration fails for ten or more points

[中文](README.zh-CN.md) · [Home](../../README.md)

## Ten points

Here $C_{10}=10^{45}/9^{36}$. Figure 1 of [Gueron and Shafrir (1999)](https://doi.org/10.1137/S0036139997315258) gives two rectangular orbits and two axial points. Treat the printed decimals as exact rational coordinates. Clearing the denominator gives

$$W=\{(\pm11183,0),(\pm32765,\pm14669),(\pm12323,\pm31572)\}.$$

The signs within each rectangle are independent. Put $q=\sum_{w\in W}|w|^2=9999608174$ and $z=\sqrt{10/q}\,W$. Then $Q(z)=10$. For $P$ the product of the 45 squared distances in $W$, exact integer arithmetic gives $9^{36}P>q^{45}$, hence $\Delta(z)>C_{10}$. [Historical coordinate check](../../verification/n10/verify_counterexample.py)

### A second witness with smaller integers

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

## Eleven or more points

Set $N=n(n-1)/2$ and $w=z/\sqrt n$. On the unit sphere the energy used by Gueron and Shafrir is

$$F(w)=-\sum_{i<j}\log|w_i-w_j|=\tfrac12(N\log n-\log\Delta(z)).$$

Their Theorem 1(2) proves that the centered polygon is unstable for every $n\ge11$. Arbitrarily close feasible configurations have strictly lower energy, hence strictly larger distance product after scaling back. Combining this with the ten-point witness proves $M_n>C_n$ for every $n\ge10$. Thus among the $n\ge6$ of Chalk’s comparison, $S_n$ is globally optimal exactly for $6\le n\le9$. [Gueron–Shafrir](https://doi.org/10.1137/S0036139997315258) · [Chalk](https://doi.org/10.4153/CMB-1960-002-x)
