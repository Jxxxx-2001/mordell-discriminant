# Seven points via a certified pair inequality

[中文](PAIR_BOUND.zh-CN.md) · [Equilibrium-classification proof from arXiv v1](README.md)

The sharp value remains $7^{21}/6^{15}$. The normalized maximizing configuration consists of the origin and the sixth roots of unity. The proof below uses a continuous pair inequality, whose matrix and domain certificates are checked in Lean.

## Necessary domain

Let $z$ be a global maximizer under $\sum_i|z_i|^2=7$. Compactness gives existence. A positive witness rules out collisions. Centering and first and second variations give the stationary and second-order inequalities. Put $w=\sqrt{6/7}\,z$, so $\sum_i |w_i|^2=6$. For a distinct pair let $u=|w_i|^2,\ v=|w_j|^2,\ t=\operatorname{Re}(w_i\overline w_j)$. Then
```math
0\le u,v\le9/5,\qquad t^2\le uv,\qquad u+v-2t\ge1/3.
```
The second variation gives the distance bound. For the radius bound in the original scale, put $m_j=\sum_i|z_i|^{2j}$. The moment estimates give $m_2\le28/3$ and $72m_3-198m_2+847\le0$. For a squared radius $s\ge2$, Cauchy–Schwarz on the other six points gives $(m_2-s^2)^2\le(7-s)(m_3-s^3)$. Eliminating the moments gives $504s^3-1344s^2+1001s-735\le0$. The polynomial increases for $s\ge2$ and is positive at $21/10$, giving the bound after scaling. [Domain and moment bounds](../../formalization/n7/N7/Kernel/Domain.lean)

## Pair inequality and summation

Write $F_0(u)=(u-6/7,u(u-1),u^2(u-1),u^3(u-1))$ and $F_k(u)=(1,u-1,(u-1)^2,(u-1)^3)$ for $1\le k\le5$. Let $H_0=1,\ H_1=t,\ H_k=2tH_{k-1}-uvH_{k-2}$. On actual pairs $H_k=\operatorname{Re}((w_i\overline w_j)^k)$. For the six exact positive-definite matrices $Q_k$, put
```math
K(u,v,t)=\sum_{k=0}^5 H_kF_k(u)^{\mathsf T}Q_kF_k(v),\qquad
h(u,v,t)=\frac{7}{12}(u+v)-1+\frac27\log6-K(u,v,t)-\frac{K(u,u,u)+K(v,v,v)}{12}.
```
The [matrix data](../../formalization/n7/N7/Kernel/MatrixData.lean) and [positive-definiteness proof](../../formalization/n7/N7/Kernel/MatrixPositive.lean) fix these constants exactly. The [domain certificate](../../formalization/n7/N7/Kernel/Cover/Verified.lean) proves $\log(u+v-2t)\le h(u,v,t)$ throughout the necessary domain. Closed-box subdivision proves coverage. Its leaves certify either a Bernstein lower bound for the gap, a contact-neighborhood estimate, or exclusion from the necessary domain.

Summing over the 21 pairs and using $\sum u_i=6$ gives $6\log6$ minus half the double kernel sum. With $V_k=\sum_i w_i^kF_k(u_i)$, that double sum is $\sum_k V_k^*Q_k V_k\ge0$. Thus $\Delta(w)\le6^6$, and undoing the scaling gives $\Delta(z)\le7^{21}/6^{15}$. Since the bound holds at an arbitrary global maximum, it holds over the full energy shell. [Summation identity](../../formalization/n7/N7/Kernel/Sum.lean)

## Equality

Equality forces every $V_k=0$. The two radial identities from $V_0=0$ imply $\sum_i u_i(u_i-1)^2=0$, so each $u_i$ is 0 or 1. The energy forces exactly one zero. The other moments give $\sum_i w_i^k=0$ for $1\le k\le5$. Newton's identities give a polynomial of the form $X^6-c$ for the six outer points, so they form a rotated regular hexagon. The explicit witness attains the bound, and rotation and relabeling preserve it. [Equality proof](../../formalization/n7/N7/Kernel/EqualityReduction.lean) · [Final Lean declarations](../../formalization/n7/N7/Kernel/Final.lean)
