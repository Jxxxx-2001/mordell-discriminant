# Mordell 问题的最优构型

[English](README.md) · [中文](README.zh-CN.md)

Xiang Ji、Tiancheng Xu、Wensheng Yu，[*Optimal Configurations for Mordell’s Problem*](https://arxiv.org/abs/2611.03088v1)。

项目单位：北京邮电大学 智能信息处理实验室。

**首次公开：2026-10-29 · [v0.1.0](https://github.com/Jxxxx-2001/mordell-discriminant/releases/tag/v0.1.0)。**

**内容更新：2026-11-12。**

## 问题

对满足

```math
\sum_{i=1}^{n}|z_i|^2=n
```

的复数 $`z_1,\ldots,z_n`$，求距离平方乘积

```math
\Delta(z)=\prod_{1\le i\lt j\le n}|z_i-z_j|^2
```

的最大值 $`M_n`$，以及取得最大值的全部构型。点可以位于整个复平面；约束的是总平方模，不是每个点的半径。

记中心加正 $`(n-1)`$ 边形的值为

```math
C_n=(n-1)^{n-1}\left(\frac{n}{n-1}\right)^{n(n-1)/2}.
```

## 问题由来

- **1958年**，Birch 猜想最大值为 $`n^n`$，由单位正 $`n`$ 边形取得。 [年代出处：林开亮](https://www.math.sinica.edu.tw/media/pdf/d352/35205.pdf)
- **1960年**，Mordell 证明 $`n=3`$ 时猜想成立，最大值为 $`27`$，等号对应单位正三角形。 [Mordell 原文](https://doi.org/10.4153/CJM-1960-063-5)
- **同年**，Chalk 取原点加半径 $`\sqrt{n/(n-1)}`$ 的正 $`(n-1)`$ 边形，给出所有 $`n\ge6`$ 的反例：$`C_n>n^n`$。真正最大值与最大构型的确定由此成为进一步的问题。 [Chalk 原文](https://doi.org/10.4153/CMB-1960-002-x)
- **1999 年**，Gueron 与 Shafrir 将六至九点的中心多边形列为数值优化得到的候选，给出十点的改进坐标，并证明对每个 $n\ge11$ 该构型失稳。[原文定理 1 与图 1](https://doi.org/10.1137/S0036139997315258)
- **2011年**，林开亮证明 $`n=4`$ 时最大值为 $`256`$，等号对应单位正方形。 [《Mordell 的一個問題》](https://www.math.sinica.edu.tw/media/pdf/d352/35205.pdf)
- **2026年**，五点情形出现预印本证明，得到 $`M_5=3125`$，等号对应单位正五边形。Jie Wang 于9月提交证明；Tiancheng Xu、Guowei Dou、Wensheng Yu 于10月提交利用前者代数成果的证明。 [Wang 预印本](https://arxiv.org/abs/2610.00358) · [Xu、Dou 与 Yu 预印本](https://arxiv.org/abs/2610.12504)

## 主要结果

记 $S_n$ 为原点加上半径 $\sqrt{n/(n-1)}$ 的正 $(n-1)$ 边形顶点构成的点集，$C_n=\Delta(S_n)$。

| 点数 | 结果 | 最优构型或排除结论 | 证明 | Lean 形式化 |
|---:|---|---|---|---|
| 2 | $M_2=4=2^2$ | 单位圆上的一对对径点 | [证明](proofs/n2-n5/README.zh-CN.md) | — |
| 3 | $M_3=27=3^3$ | 单位圆上的正三角形 | [证明](proofs/n2-n5/README.zh-CN.md) | — |
| 4 | $M_4=256=4^4$ | 单位圆上的正方形 | [证明](proofs/n2-n5/README.zh-CN.md) | — |
| 5 | $M_5=3125=5^5$ | 单位圆上的正五边形 | [证明](proofs/n2-n5/README.zh-CN.md) | [Lean](https://github.com/dgjszy/mordell-five/blob/4329977fbe3f1286e089f6f655f990f47f134eba/Mordell/Original.lean) |
| 6 | $M_6=C_6=\frac{6^{15}}{5^{10}}$ | 原点与正五边形 | [证明](proofs/n6/README.zh-CN.md) | [Lean](formalization/n6/N6/SharpTheorem.lean) |
| 7 | $M_7=C_7=\frac{7^{21}}{6^{15}}$ | 原点与正六边形 | [证明](proofs/n7/PAIR_BOUND.zh-CN.md) | [Lean](formalization/n7/N7/Kernel/Final.lean#L9-L19) |
| 8 | $M_8=C_8=\frac{8^{28}}{7^{21}}$ | 原点与正七边形 | [证明](proofs/n8/README.zh-CN.md) | [Lean](formalization/n8/Eight/Final.lean#L8-L17) |
| 9 | $M_9=C_9=\frac{9^{36}}{8^{28}}$ | 原点与正八边形 | [证明](proofs/n9/README.zh-CN.md) | [Lean](formalization/n9/NineFinal.lean#L7-L21) |
| 10 | $M_{10}>C_{10}=\frac{10^{45}}{9^{36}}$ | 原点与正九边形已被排除，十点锐值尚未由此确定 | [证明](proofs/n10/README.zh-CN.md) | [Lean](formalization/chalk_ge10/Chalk.lean) |

二至九点的取等构型均在整体旋转和重标号意义下唯一。对所有 $n\ge10$，统一的显式构造给出距离平方乘积严格大于 $C_n$ 的构型，从而 $M_n>C_n$。这排除了 $S_n$ 的最优性，尚未确定相应的锐值及全部最优构型。[显式构造](proofs/n10/README.zh-CN.md)

<p align="center">
  <a href="assets/mordell-2-9.png"><img src="assets/mordell-2-9.png" alt="上排为二至五点，点在圆上等角间隔排列。下排为六至九点，中心各有一点，外圈构成正多边形。" width="460"></a><br>
  <strong>图 1　Mordell 问题的二至九点最优构型。</strong> <a href="assets/mordell-2-9.pdf">矢量图（PDF）</a>
</p>

五、六点采用共同的代数证明框架：由驻点方程进行代数归约，排除系数分支，并精确比较判别式值。其中五点的 Lean 链接指向外部项目 [mordell-five](https://github.com/dgjszy/mordell-five/tree/4329977fbe3f1286e089f6f655f990f47f134eba)。七至九点的当前证明采用认证点对不等式框架：对全部点对求和得到全局上界，再由取等条件恢复半径及正多边形外圈。七点的新证明见[连续点对域证明](proofs/n7/PAIR_BOUND.zh-CN.md)，[早期分类证明](proofs/n7/README.zh-CN.md)仍保留供查阅。

## 简短验证

Python 3.12 或更新版本：

```sh
python verify.py
python verify.py --level check --case n10
```

第一条检查所收文件和已有证书的一致性，第二条仅使用标准库重新核验十点的两组整数比较。需要复核其余计算时：

```sh
python -m pip install -r requirements.txt
python verify.py --level check --case n7
```

完整覆盖按需运行，说明见 [验证入口](verification/README.md)。默认命令不会启动大规模搜索或完整覆盖。

**Lean 复核。** 工具链、定理入口、证书资产、构建和公理审计见 [Lean 复现说明](formalization/REPRODUCE.md)。

## 与 Erdős 最小直径问题的关系

Bateman 与 Erdős 研究了如下问题：平面上 $n$ 个点的两两距离至少为 1，其直径最小可以是多少？把最短点距缩放为 1 后，直径恰等于原来的最长与最短点距之比。他们证明了七点的最小直径，八点结果由 Bezdek 与 Fodor 确定。[Bateman–Erdős（1951）](https://renyi.hu/~p_erdos/1951-03.pdf) · [Bezdek–Fodor（1999）](https://doi.org/10.1006/jcta.1998.2889)

按相似意义比较，二至八点各有共同最优形状。八点时两问题的全部最优解集已经不同，九点首次没有共同最优形状。对每个 $n\ge10$，两个问题均排除 $S_n$，至于两者真正的最优形状是否重合，还须另行研究。[几何比较与整数构型](proofs/ratio/README.zh-CN.md) · [Friedman 构型目录](https://erich-friedman.github.io/packing/maxmin/)

## 引用

复核 arXiv v1 时请使用[论文指定的固定提交](https://github.com/Jxxxx-2001/mordell-discriminant/tree/31cc934b7dfa0ef2308566a1bce48cbfb2e01559)。引用软件时请注明实际使用的发布版本或提交。[引用信息](CITATION.cff)
