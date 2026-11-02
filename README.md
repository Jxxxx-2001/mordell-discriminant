# Optimal Configurations for Mordell’s Problem

[English](README.md) · [中文](README.zh-CN.md)

**First public release: 2026-10-29 · [v0.1.0](https://github.com/Jxxxx-2001/mordell-discriminant/releases/tag/v0.1.0).**

**Content updated: 2026-11-02.**

## The problem

For complex numbers $`z_1,\ldots,z_n`$ satisfying

```math
\sum_{i=1}^{n}|z_i|^2=n,
```

determine the maximum $`M_n`$ of

```math
\Delta(z)=\prod_{1\le i\lt j\le n}|z_i-z_j|^2
```

and all maximizing configurations. The points range over the whole complex plane: the constraint fixes the total squared radius, not each individual radius.

Write

```math
C_n=(n-1)^{n-1}\left(\frac{n}{n-1}\right)^{n(n-1)/2}
```

for the value of a regular $`(n-1)`$-gon together with its center.

## Origins

- **1958:** Birch conjectured that $`M_n=n^n`$, attained by a regular $`n`$-gon on the unit circle. [Historical account by Lin](https://www.math.sinica.edu.tw/media/pdf/d352/35205.pdf)
- **1960:** Mordell proved the three-point case, with $`M_3=27`$ and equality precisely for a unit equilateral triangle. [Mordell’s paper](https://doi.org/10.4153/CJM-1960-063-5)
- **The same year:** Chalk disproved the conjecture for every $`n\ge6`$: the origin and a regular $`(n-1)`$-gon of radius $`\sqrt{n/(n-1)}`$ give $`C_n>n^n`$. Determining the actual maximum and its maximizers remains a further problem. [Chalk’s paper](https://doi.org/10.4153/CMB-1960-002-x)
- **1999:** Gueron and Shafrir reported numerical evidence for the centered polygon at six through nine points, gave ten-point coordinates improving on it, and proved its instability for every $n\ge11$. [Article, Theorem 1 and Figure 1](https://doi.org/10.1137/S0036139997315258)
- **2011:** Kailiang Lin proved $`M_4=256`$, with equality precisely for a unit square. [Lin’s paper](https://www.math.sinica.edu.tw/media/pdf/d352/35205.pdf)
- **2026:** Preprints proved $`M_5=3125`$, with equality precisely for a unit regular pentagon. Jie Wang submitted a proof in September; Tiancheng Xu, Guowei Dou, and Wensheng Yu submitted a proof using Wang's algebraic results in October. [Wang’s preprint](https://arxiv.org/abs/2610.00358) · [Xu, Dou and Yu’s preprint](https://arxiv.org/abs/2610.12504)

## Main results

Let $S_n$ consist of the origin and the vertices of a regular $(n-1)$-gon of radius $\sqrt{n/(n-1)}$, and let $C_n=\Delta(S_n)$.

| Points | Result | Maximizing configuration or exclusion | Proof |
|---:|---|---|---|
| 2 | $M_2=4=2^2$ | Antipodal points on the unit circle | [Proof](proofs/n2-n5/README.md) |
| 3 | $M_3=27=3^3$ | Equilateral triangle on the unit circle | [Proof](proofs/n2-n5/README.md) |
| 4 | $M_4=256=4^4$ | Square on the unit circle | [Proof](proofs/n2-n5/README.md) |
| 5 | $M_5=3125=5^5$ | Regular pentagon on the unit circle | [Proof](proofs/n2-n5/README.md) |
| 6 | $M_6=C_6=\frac{6^{15}}{5^{10}}$ | Origin and a regular pentagon | [Proof](proofs/n6/README.md) |
| 7 | $M_7=C_7=\frac{7^{21}}{6^{15}}$ | Origin and a regular hexagon | [Proof](proofs/n7/README.md) |
| 8 | $M_8=C_8=\frac{8^{28}}{7^{21}}$ | Origin and a regular heptagon | [Proof](proofs/n8/README.md) |
| 9 | $M_9=C_9=\frac{9^{36}}{8^{28}}$ | Origin and a regular octagon | [Proof](proofs/n9/README.md) |
| 10 | $M_{10}>C_{10}=\frac{10^{45}}{9^{36}}$ | The centered nonagon is excluded. The sharp value is undetermined here. | [Proof](proofs/n10/README.md) |

For two through nine points the listed maximizer is unique up to rotation and relabeling. For every $n\ge10$, one has $M_n>C_n$, by an explicit comparison at ten points and an instability theorem for every $n\ge11$. [General conclusion](proofs/n10/README.md)

<p align="center">
  <a href="assets/mordell-2-9.png"><img src="assets/mordell-2-9.png" alt="Two to five equally spaced points on a circle in the top row. For six to nine points, one point lies at the center of the regular outer polygon." width="460"></a><br>
  <strong>Figure 1. Optimal configurations for Mordell’s problem, 2 ≤ n ≤ 9.</strong> <a href="assets/mordell-2-9.pdf">Vector figure (PDF)</a>
</p>

The six-point proof uses algebraic elimination and a recorded exact dimension computation. For seven points we use the complete [Faugère–Svartz classification](https://doi.org/10.1145/2442829.2442856) and compare twelve equilibrium classes. A [related public manuscript](https://github.com/harrykane8816627373-cell/mordell-research/tree/631e0feacf197f5c96f092bafbf17bc8cbd0ef32/earlier-results) also treats six and seven points. For eight and nine points a certified inequality for pairs gives a global bound after summation. The equality conditions recover the radii and the regular outer polygon.

## Quick verification

Use Python 3.12 or newer:

```sh
python verify.py
python verify.py --level check --case n10
```

The first command audits the distributed files and saved certificates. The second recomputes both ten-point integer comparisons using only the standard library. To check other computations:

```sh
python -m pip install -r requirements.txt
python verify.py --level check --case n7
```

Complete covers can be replayed when needed; see [verification](verification/README.md). The default command launches neither searches nor full covers.

## Relation to an Erdős problem on minimum diameter

Bateman and Erdős asked how small the diameter of $n$ planar points can be if every pair is at least one unit apart. Rescaling the shortest distance to one turns the diameter into the ratio of the largest to the smallest pairwise distance. They proved the seven-point minimum, and Bezdek and Fodor determined the eight-point minimum. [Bateman–Erdős (1951)](https://renyi.hu/~p_erdos/1951-03.pdf) · [Bezdek–Fodor (1999)](https://doi.org/10.1006/jcta.1998.2889)

For each $2\le n\le8$ the two problems have a common optimal shape. At eight points the full sets of optimizers differ. Nine is the first point count with no common optimizer. For every $n\ge10$ both problems exclude $S_n$; whether their actual optimizers coincide is a separate question. [Comparisons and integer witnesses](proofs/ratio/README.md) · [Friedman’s illustrated catalogue](https://erich-friedman.github.io/packing/maxmin/)

## Citation

Manuscript: Xiang Ji, Tiancheng Xu and Wensheng Yu, *Optimal Configurations for Mordell’s Problem*. For the software, cite the release or commit used. [Citation metadata](CITATION.cff)
