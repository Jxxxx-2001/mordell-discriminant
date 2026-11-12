# 七点的连续点对域证明

[English](PAIR_BOUND.md) · [arXiv v1 的平衡构型分类证明](README.zh-CN.md)

锐值仍为 $7^{21}/6^{15}$。以下证明通过连续点对不等式得出全局上界，所用精确矩阵和全域证书均由 Lean 核验。

## 从最大点导出必要域

能量壳的紧致性保证最大点存在，正值见证保证最大点无碰撞。中心化及一、二阶变分给出驻点与二阶必要条件。令 $w=\sqrt{6/7}\,z$，则 $\sum_i|w_i|^2=6$。对不同点 $i,j$，记 $u=|w_i|^2,\ v=|w_j|^2,\ t=\operatorname{Re}(w_i\overline w_j)$，则
```math
0\le u,v\le9/5,\qquad t^2\le uv,\qquad u+v-2t\ge1/3.
```
距离界来自二阶变分。为证明半径界，在原尺度记 $m_j=\sum_i|z_i|^{2j}$，有 $m_2\le28/3$ 和 $72m_3-198m_2+847\le0$。对平方半径 $s\ge2$，其余六点的 Cauchy–Schwarz 不等式给出 $(m_2-s^2)^2\le(7-s)(m_3-s^3)$。消去矩量得到 $504s^3-1344s^2+1001s-735\le0$。该多项式在 $s\ge2$ 时递增且在 $21/10$ 处为正，缩放后即得半径界。 [必要域源码](../../formalization/n7/N7/Kernel/Domain.lean)

## 点对上界与全局求和

取 $F_0(u)=(u-6/7,u(u-1),u^2(u-1),u^3(u-1))$，对 $1\le k\le5$ 取 $F_k(u)=(1,u-1,(u-1)^2,(u-1)^3)$。定义 $H_0=1,\ H_1=t,\ H_k=2tH_{k-1}-uvH_{k-2}$，实际点对上 $H_k=\operatorname{Re}((w_i\overline w_j)^k)$。用六个精确正定矩阵 $Q_k$ 构造
```math
K(u,v,t)=\sum_{k=0}^5 H_k F_k(u)^{\mathsf T}Q_k F_k(v),\qquad
h(u,v,t)=\frac{7}{12}(u+v)-1+\frac27\log6-K(u,v,t)-\frac{K(u,u,u)+K(v,v,v)}{12}.
```
[矩阵数据](../../formalization/n7/N7/Kernel/MatrixData.lean)给出系数，[正定性证明](../../formalization/n7/N7/Kernel/MatrixPositive.lean)核验矩阵，[连续域证书](../../formalization/n7/N7/Kernel/Cover/Verified.lean)证明整个必要域上 $\log(u+v-2t)\le h(u,v,t)$。证书用闭盒细分保证覆盖。每个叶盒由 Bernstein 下界、接触点邻域估计或域外排除处理。

对 21 个无序点对求和。单点项利用能量条件消去，得到 $6\log6$ 减去核双重和的一半。令 $V_k=\sum_i w_i^k F_k(u_i)$，核双重和等于 $\sum_k V_k^*Q_k V_k\ge0$。因此 $\Delta(w)\le6^6$。缩放回能量 7 即得 $\Delta(z)\le7^{21}/6^{15}$。这一估计适用于任意全局最大点，故给出全局上界。 [求和恒等式](../../formalization/n7/N7/Kernel/Sum.lean)

## 等号

取等迫使每个 $V_k=0$。$V_0=0$ 给出的两个径向矩等式相减后，得到 $\sum_i u_i(u_i-1)^2=0$。于是平方半径只能是 0 或 1，且能量条件迫使恰有一个原点。其余矩条件给出 $\sum_i w_i^k=0$（$1\le k\le5$）。Newton 恒等式表明六个外点的根多项式为 $X^6-c$，故外点构成旋转后的正六边形。显式见证达到锐值，整体旋转和重标号保持等号。 [等号归约](../../formalization/n7/N7/Kernel/EqualityReduction.lean) · [Lean 最终声明](../../formalization/n7/N7/Kernel/Final.lean)
