# 二至五点：已有结果的整理

[English](README.md) · [返回首页](../../README.zh-CN.md)

设 $\sum|z_i|^2=n$，$\Delta=\prod_{i<j}|z_i-z_j|^2$。以下等号均允许旋转和重标号，不包括任意平移。

## 二点

$$|z_1-z_2|^2=2(|z_1|^2+|z_2|^2)-|z_1+z_2|^2\le4.$$

等号当且仅当 $z_2=-z_1$；能量约束再给出 $|z_1|=1$。故 $M_2=4$，全部最大构型为 $\{u,-u\}$，$|u|=1$。

## 三点

对任意 $n$ 有

$$\sum_{i<j}|z_i-z_j|^2=n\sum_i|z_i|^2-\left|\sum_i z_i\right|^2.$$

当 $n=3$ 时，右端不超过9。对三条距离平方用算术几何平均不等式，

$$\Delta\le\left(\frac{|z_1-z_2|^2+|z_1-z_3|^2+|z_2-z_3|^2}{3}\right)^3\le27.$$

取等需要质心为0、三条距离相等。因此最大构型恰为单位正三角形，$M_3=27$。

## 四点

林开亮2011年给出的结果为

$$M_4=4^4=256,$$

等号恰为单位正方形。这里整理该定理及等号条件；完整四点上界证明引用其原文，不把单位正方形的可达性计算当作全局上界证明。

## 五点

2026年的预印本证明给出

$$M_5=5^5=3125,$$

等号恰为单位正五边形。Wang通过完整驻点的精确代数分类与比较证明；Xu等利用其代数条件直接比较判别式值，并报告完整Lean形式化。本仓库引用这些结果，不将第三方验证程序或形式化工作列作原创成果。

## 达到这些值

单位正 $n$ 边形是 $p(X)=X^n-1$ 的根。各根处 $|p'(z_i)|=n$，所以

$$\prod_i|p'(z_i)|=\prod_{i<j}|z_i-z_j|^2=n^n.$$

这证明正多边形达到所列值；四、五点的全局上界仍使用上述已有定理。

## 来源

- Mordell, *On a Discriminant Inequality* (1960), [DOI](https://doi.org/10.4153/CJM-1960-063-5)。
- 林开亮，*Mordell的一個問題*，《数学传播》35(2), 51–58 (2011), [原文](https://www.math.sinica.edu.tw/media/pdf/d352/35205.pdf)。1958年Birch提出猜想的历史记载亦见此文。
- Jie Wang, *The Five-Point Case of Mordell's Discriminant Inequality*, [arXiv:2610.00358](https://arxiv.org/abs/2610.00358)。
- Tiancheng Xu, Guowei Dou, Wensheng Yu, *On the Five-Point Case of Mordell's Problem*, [arXiv:2610.12504](https://arxiv.org/abs/2610.12504)。
