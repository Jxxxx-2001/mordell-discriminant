# An Erdős problem on minimum diameter

[中文](README.zh-CN.md) · [Home](../../README.md)

Write $R$ for the largest pairwise distance divided by the smallest. Scaling a point set so its shortest distance is one makes its diameter equal to $R$, so minimization is over shapes up to similarity. Bateman and Erdős give the values through six points and prove the seven-point minimum in Theorem 3. Bezdek and Fodor determine the eight-point minimum. These results give a common optimal shape with Mordell’s problem for each of two through eight points. [Bateman–Erdős](https://renyi.hu/~p_erdos/1951-03.pdf) · [Bezdek–Fodor](https://doi.org/10.1006/jcta.1998.2889)

**Eight points.** Move the center point of the heptagon of circumradius one by $1/10$, keeping the seven vertices fixed. Its distances to the vertices are then between $0.9$ and $1.1$. The shortest outer chord is $2\sin(\pi/7)<0.9$, and the longest is $2\cos(\pi/14)>1.1$. Both extreme distances, and hence the optimal ratio, are preserved. The displaced shape no longer maximizes the Mordell product.

**Nine through eleven points.** The integer coordinates in the [checker](../../verification/ratio/check_examples.py) give the following comparisons. The last column is the squared ratio of the regular outer polygon with its center, from its longest and shortest chords.

| Points | Squared ratio of the witness | Squared ratio of the centered polygon |
|---|---|---|
| 9 | $925/136$ | $4+2\sqrt2$ |
| 10 | $733/89$ | $1/(4\sin^2(\pi/18))$ |
| 11 | $289/29$ | $1/\sin^2(\pi/10)$ |

Each witness has strictly smaller ratio. Since the centered octagon is the unique Mordell maximizing shape at nine points, nine is the first cardinality with no common optimum. Run `python verify.py --level check --case ratio` after installing the verification dependencies to enumerate every pair and certify the three strict comparisons.

**All larger point counts.** For $m=n-2\ge10$, take a regular $m$-gon of side one. Add two points on opposite sides of its center, each half a unit away. Both are interior, and the circumradius $1/(2\sin(\pi/m))>3/2$ makes each vertex more than one unit from either added point. The separation is one and the diameter remains the polygon diameter $D_m$. The centered polygon $S_n$, scaled to the same separation, has diameter $D_{m+1}$. For even $j$, $D_j=1/\sin(\pi/j)$, and for odd $j$, $D_j=1/(2\sin(\pi/(2j)))$. Thus

$$D_m\le 1/\sin(\pi/m)<(m+1)/\pi<D_{m+1}.$$

The middle inequality follows from $\sin x\ge x-x^3/6$ and $\pi^2(m+1)<6m^2$ for $m\ge10$. Together with the [Mordell comparison](../n10/README.md), this excludes $S_n$ for both objectives for every $n\ge10$. Whether the two actual optimizing shapes agree there is a separate question.
