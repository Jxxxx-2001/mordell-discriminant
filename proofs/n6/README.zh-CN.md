# 6点：中心加正五边形

[English](README.md) · [返回首页](../../README.zh-CN.md)

## 定理

在$`\sum|z_i|^2=6`$下，

```math
M_6=C_6=6^{15}/5^{10}.
```

全部等号构型为

```math
\{0\}\cup\left\{\sqrt{\frac{6}{5}}e^{i\theta+2\pi i k/5}:k=0,\ldots,4\right\},
```

允许整体旋转和重标号，没有额外的平移自由度。

## 证明

完整证明从任意全局最大点出发，不预设对称性。通过结果式恒等式获得驻点的系数方程。一般饱和理想的商空间维数为35；精确代入验证35个图解，结合独立的有理数CAS维数计算确认完整性。再用精确实根隔离与目标比较排除竞争分支。零系数、中心对称及三重旋转分支分别处理，只有中心加正五边形取到最大值。

目录保留Singular、Magma的数学输入、输出及精确比较数据。`check`重新执行CAS之后的恒等式、实根比较和例外分支检查，使用已保存的CAS完备性证据；它不重新进行这一CAS步骤。独立重算原维数认证需要Singular/Magma及所列输入。

[完整证明](../../verification/n6/GLOBAL_PROOF.txt) · [最终证书](../../verification/n6/global_verification.json)

```sh
python verify.py --case n6
python verify.py --level check --case n6
```
