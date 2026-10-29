# 7 points: the centered regular hexagon

[中文](README.zh-CN.md) · [Home](../../README.md)

## Theorem

For $\sum|z_i|^2=7$,

$$M_7=C_7=7^{21}/6^{15}.$$

Equality holds exactly for

$$\{0\}\cup\left\{\sqrt{\frac{7}{6}}e^{i\theta+2\pi i k/6}:k=0,\ldots,5\right\},$$

up to rotation and relabeling. There is no additional translation freedom.

## Proof

Every maximizer is centered and collision-free and satisfies the full stationary equations. Rescaling by $\sqrt3$ identifies these equations with the equal-strength seven-vortex relative-equilibrium equations. The published classification has exactly twelve physical classes, up to rotation, reflection and relabeling. The included exact dyadic interval argument certifies ten distinct classes; the regular heptagon and centered hexagon give the other two. Disjoint objective intervals show that all twelve are inequivalent and that the centered hexagon is strictly largest.

**External premise:** completeness of the Faugère–Svartz classification is cited, not independently re-proved here. The verification program checks the independent twelve-class comparison. Its optional PDF-provenance I/O has been adapted so that the paper need not be redistributed; the original program is retained. This change does not alter the interval calculations.

[Complete proof in Chinese](../../verification/n7/GLOBAL_PROOF.txt) · [Final certificate](../../verification/n7/classification_based_certificate.json)

```sh
python verify.py --case n7
python verify.py --level check --case n7
```


Source: Faugère and Svartz, ISSAC 2012, [DOI](https://doi.org/10.1145/2442829.2442856), §§5.2–5.7 and Figure 4.
