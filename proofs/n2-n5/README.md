# Two through five points: existing results

[中文](README.zh-CN.md) · [Home](../../README.md)

Let $\sum|z_i|^2=n$ and $\Delta=\prod_{i<j}|z_i-z_j|^2$. Equality descriptions below allow rotation and relabeling, but not arbitrary translation.

## Two points

$$|z_1-z_2|^2=2(|z_1|^2+|z_2|^2)-|z_1+z_2|^2\le4.$$

Equality requires $z_2=-z_1$ and hence $|z_1|=1$. Thus $M_2=4$, with precisely the configurations $\{u,-u\}$, $|u|=1$.

## Three points

The identity

$$\sum_{i<j}|z_i-z_j|^2=n\sum_i|z_i|^2-\left|\sum_i z_i\right|^2$$

and AM–GM give

$$\Delta\le\left(\frac{\sum_{i<j}|z_i-z_j|^2}{3}\right)^3\le27.$$

Equality requires zero centroid and three equal distances. The maximizers are therefore exactly unit equilateral triangles, and $M_3=27$.

## Four points

Kailiang Lin's 2011 result is $M_4=256$, with equality precisely for a unit square. This document records the theorem and equality condition; its full upper-bound proof is cited below.

## Five points

The 2026 preprints prove $M_5=3125$, with equality precisely for a unit regular pentagon. Wang uses exact classification and comparison of stationary configurations. Xu, Dou, and Yu compare discriminant values using Wang's algebraic conditions and report a complete Lean formalization. These are cited results; their third-party verification and formalization are not presented as original work of this repository.

## Attainment

For the roots of $p(X)=X^n-1$, one has $|p'(z_i)|=n$, so

$$\Delta=\prod_i|p'(z_i)|=n^n.$$

This proves attainment by regular polygons. The four- and five-point global upper bounds rely on the cited theorems, not just this calculation.

## Sources

- Mordell, *On a Discriminant Inequality* (1960), [DOI](https://doi.org/10.4153/CJM-1960-063-5).
- Kailiang Lin, *On Mordell's Problem*, Math Media 35(2), 51–58 (2011), in Chinese, [paper](https://www.math.sinica.edu.tw/media/pdf/d352/35205.pdf). This source also dates Birch's conjecture to 1958.
- Jie Wang, [arXiv:2610.00358](https://arxiv.org/abs/2610.00358).
- Tiancheng Xu, Guowei Dou, Wensheng Yu, [arXiv:2610.12504](https://arxiv.org/abs/2610.12504).
