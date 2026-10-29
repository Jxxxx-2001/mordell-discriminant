# 7点：中心加正六边形

[English](README.md) · [返回首页](../../README.zh-CN.md)

## 定理

在$\sum|z_i|^2=7$下，

$$M_7=C_7=7^{21}/6^{15}.$$

全部等号构型为

$$\{0\}\cup\left\{\sqrt{\frac{7}{6}}e^{i\theta+2\pi i k/6}:k=0,\ldots,5\right\},$$

允许整体旋转和重标号，没有额外的平移自由度。

## 证明

任意最大点必居中、无碰撞，并满足完整驻点方程。乘以$\sqrt3$后，这些方程恰为七个同强度点涡的相对平衡方程。已发表分类给出模旋转、镜像和重标号共12个物理构型类。所附精确二进制区间程序严格认证其中10类；正七边形与中心加正六边形给出另外两类。12个互不相交的目标区间保证构型彼此不同，并证明中心加正六边形严格最大。

**外部前提：**Faugère–Svartz分类的完整性采用引用，没有在本仓库独立重证。程序独立复核12类的目标比较。发布版只调整了可选PDF来源核对的输入输出，避免分发论文；原程序也予以保留。区间计算未改变。

[完整证明](../../verification/n7/GLOBAL_PROOF.txt) · [最终证书](../../verification/n7/classification_based_certificate.json)

```sh
python verify.py --case n7
python verify.py --level check --case n7
```


来源：Faugère、Svartz，ISSAC 2012，[DOI](https://doi.org/10.1145/2442829.2442856)，§§5.2–5.7及Figure 4。
