# 十点及以上为何排除 Chalk 构型

[English](README.md) · [返回首页](../../README.zh-CN.md)

## 所有 $n\ge10$ 的统一显式构造

令 $p=n-2\ge8$、$N=n(n-1)/2$。取两个实点 $\pm1$ 和半径 $\sqrt{p+3}$ 的旋转正 $p$ 边形：

```math
W=\{-1,1\}\cup\left\{\sqrt{p+3}\exp\!\left(i\left(\frac{\pi}{2p}+\frac{2\pi j}{p}\right)\right):j=0,\ldots,p-1\right\}.
```

令 $Z=W/\sqrt{p+1}$。由于 $\sum_{w\in W}|w|^2=2+p(p+3)=(p+1)(p+2)$，有 $\sum_{z\in Z}|z|^2=n$。正多边形内部及其与两个实点的距离乘积给出

```math
\Delta(W)\ge4p^p(p+3)^{N-1}>(p+1)^{p+1}(p+2)^N.
```

后一严格整数不等式对每个 $p\ge8$ 成立，见 [Lean 整数比较](../../formalization/chalk_ge10/Chalk/Integer.lean)。缩放后得到

```math
\Delta(Z)=\frac{\Delta(W)}{(p+1)^N}
>\frac{(p+2)^N}{(p+1)^{N-p-1}}=C_n.
```

因此每个 $n\ge10$ 都有 $M_n>C_n$。[Lean 最终定理 `Chalk.exists_above_chalk`](../../formalization/chalk_ge10/Chalk.lean)核验了这一统一构造。它排除了中心正多边形的最优性，尚未给出真正的锐值和全部最优构型。下面保留十点的其他显式构型及十一点起的历史失稳论证。

## 十点的显式比较

此时 $C_{10}=10^{45}/9^{36}$。[Gueron 与 Shafrir（1999）](https://doi.org/10.1137/S0036139997315258) 的图 1 给出两个矩形的顶点及横轴上的两点。将刊出的小数坐标视为精确有理数，清除公分母后得到

$$W=\{(\pm11183,0),(\pm32765,\pm14669),(\pm12323,\pm31572)\}.$$

每个矩形的正负号独立选取。令 $q=\sum_{w\in W}|w|^2=9999608174$，取 $z=\sqrt{10/q}\,W$，便有 $Q(z)=10$。记 $P$ 为 $W$ 的 45 个平方点距之积。整数计算给出 $9^{36}P>q^{45}$，因此 $\Delta(z)>C_{10}$。[历史坐标核验](../../verification/n10/verify_counterexample.py)

### 另一组小整数坐标

取整数坐标点集

```math
W=\{\pm7,\ \pm21\pm9i,\ \pm8\pm20i\}.
```

两个四点组的符号独立，因此恰有10个互异点，质心为0，且

```math
\sum_{w\in W}|w|^2=2\cdot49+4(21^2+9^2)+4(8^2+20^2)=4042.
```

令 $`Z=\sqrt{5/2021}\,W`$，便有 $`\sum|z_i|^2=10`$。记整数

```math
P=\prod_{i\lt j}|w_i-w_j|^2.
```

所有45个因子均为正整数。缩放给出

```math
\frac{\Delta(Z)}{C_{10}}=\frac{P\,9^{36}}{4042^{45}}.
```

精确整数运算得到

```math
5P\,9^{36}-6\cdot4042^{45}>0.
```

因此 $`\Delta(Z)>(6/5)C_{10}>C_{10}`$，从而 $`M_{10}>C_{10}`$。完整整数及坐标保存在[证书](../../verification/n10/exact_counterexample_certificate.json)中。

可用Python标准库独立复核：

```sh
python verify.py --level check --case n10
```

程序重新从坐标计算全部距离平方及其乘积，并核对证书中的精确整数；不依赖浮点优化。

## 十一点及以上的失稳性

令 $N=n(n-1)/2$、$w=z/\sqrt n$。在单位球面上，Gueron 与 Shafrir 采用的能量为

$$F(w)=-\sum_{i<j}\log|w_i-w_j|=\tfrac12(N\log n-\log\Delta(z)).$$

他们的定理 1 第 (2) 项证明了对所有 $n\ge11$ 中心多边形均失稳。在约束面上，任意接近该构型处均有能量更低的构型，缩放回去就得到严格更大的距离乘积。结合十点的显式比较，对每个 $n\ge10$ 均有 $M_n>C_n$。因此在 Chalk 比较的 $n\ge6$ 范围内，$S_n$ 恰在六至九点时达到全局最优。[Gueron–Shafrir 原文](https://doi.org/10.1137/S0036139997315258) · [Chalk 原文](https://doi.org/10.4153/CMB-1960-002-x)
