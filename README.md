# Mordell's discriminant problem: a survey and extensions

[English](README.md) · [中文](README.zh-CN.md)

This project organizes the small-point cases of Mordell's discriminant problem, provides computer-assisted proofs for six through nine points, and gives an explicit ten-point configuration that strictly improves on a regular nonagon together with its center.

**First public release: the actual publication time of [v0.1.0](https://github.com/Jxxxx-2001/mordell-discriminant/releases/tag/v0.1.0).**

**Content updated: 2026-10-29 (Asia/Shanghai).**

## The problem

For complex numbers $z_1,\ldots,z_n$ satisfying

$$\sum_{i=1}^{n}|z_i|^2=n,$$

determine the maximum $M_n$ of

$$\Delta(z)=\prod_{1\le i<j\le n}|z_i-z_j|^2$$

and all maximizing configurations. The points range over the whole complex plane: the constraint fixes the total squared radius, not each individual radius.

Write

$$C_n=(n-1)^{n-1}\left(\frac{n}{n-1}\right)^{n(n-1)/2}$$

for the value of a regular $(n-1)$-gon together with its center.

## Origins

- **1958:** Birch conjectured that $M_n=n^n$, attained by a regular $n$-gon on the unit circle.
- **1960:** Mordell proved the three-point case, with $M_3=27$ and equality precisely for a unit equilateral triangle.
- **The same year:** Chalk disproved the conjecture for every $n\ge6$: the origin and a regular $(n-1)$-gon of radius $\sqrt{n/(n-1)}$ give $C_n>n^n$. Determining the actual maximum and its maximizers remains a further problem.
- **2011:** Kailiang Lin proved $M_4=256$, with equality precisely for a unit square.
- **2026:** Preprints proved $M_5=3125$, with equality precisely for a unit regular pentagon. Jie Wang submitted a proof in September; Tiancheng Xu, Guowei Dou, and Wensheng Yu submitted a proof using Wang's algebraic results in October.

## Results for two through ten points

| Points | Result | Maximizer or statement | Proof |
|---|---|---|---|
| 2 | $M_2=4$ | Two antipodal unit points | [Two through five](proofs/n2-n5/README.md) |
| 3 | $M_3=27$ | Unit equilateral triangle | [Two through five](proofs/n2-n5/README.md) |
| 4 | $M_4=256$ | Unit square | [Two through five](proofs/n2-n5/README.md) |
| 5 | $M_5=3125$ | Unit regular pentagon | [Two through five](proofs/n2-n5/README.md) |
| 6 | $M_6=C_6=6^{15}/5^{10}$ | Center and regular pentagon | [Six points](proofs/n6/README.md) |
| 7 | $M_7=C_7=7^{21}/6^{15}$ | Center and regular hexagon | [Seven points](proofs/n7/README.md) |
| 8 | $M_8=C_8=8^{28}/7^{21}$ | Center and regular heptagon | [Eight points](proofs/n8/README.md) |
| 9 | $M_9=C_9=9^{36}/8^{28}$ | Center and regular octagon | [Nine points](proofs/n9/README.md) |
| 10 | **$M_{10}>C_{10}$** | An explicit strict improvement over the centered nonagon | [Ten points](proofs/n10/README.md) |

The two-to-five-point results are existing results collected here. Six through nine points are supported by computer-assisted proofs; the seven-point argument uses a published complete vortex classification, as stated in its proof. For $n=6,7,8,9$, all maximizers are

$$\{0\}\cup\left\{\sqrt{\frac{n}{n-1}}e^{i\theta+2\pi i k/(n-1)}:k=0,\ldots,n-2\right\},$$

up to rotation and relabeling. “Extensions” refers to further point counts and configurations; no claim of literature priority is made.

For ten points this release includes only the explicit construction

$$Z=\sqrt{\frac5{2021}}\{\pm7,\ \pm21\pm9i,\ \pm8\pm20i\}$$

and its strict comparison. The signs in each four-point group are independent. The configuration has total squared radius 10 and satisfies $\Delta(Z)>C_{10}$; this does not determine $M_{10}$.

## Quick verification

Use Python 3.12 or newer:

```sh
python verify.py
python verify.py --level check --case n10
```

The first command audits the distributed files and saved certificates. The second recomputes the ten-point integer comparison using only the standard library. To check other computations:

```sh
python -m pip install -r requirements.txt
python verify.py --level check --case n7
```

Complete covers can be replayed when needed; see [verification](verification/README.md). The default command launches neither searches nor full covers.

## Relation to the distance-ratio problem

[Friedman's distance-ratio problem](https://erich-friedman.github.io/packing/maxmin/) has a different objective: for two through eight points there are common maximizers/minimizers, although the full sets of optimal configurations need not coincide. At nine points a better distance-ratio arrangement is known than the centered octagon, which remains optimal for Mordell's problem; at ten points both objectives admit improvements over the centered nonagon. Exact optimal configurations for general point counts remain challenging, and the linked page lists best-known distance-ratio records from nine points onward.
