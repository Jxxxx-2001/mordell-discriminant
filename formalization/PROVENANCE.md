# Sources and attribution

The mathematical starting point is *Optimal Configurations for Mordell’s Problem* by Xiang Ji, Tiancheng Xu, and Wensheng Yu. The [paper](https://arxiv.org/abs/2611.03088v1) identifies its [fixed computational materials](https://github.com/Jxxxx-2001/mordell-discriminant/tree/31cc934b7dfa0ef2308566a1bce48cbfb2e01559).

- The seven-point formal proof specializes the eight- and nine-point pair-majorant method to seven points. Its import closure includes eight shared six-point analysis modules and two Chalk modules. The exact matrix input is included with the seven-point project.
- The eight- and nine-point Lean sources use the exact kernels and computational proof inputs from the paper. Their generated modules are included in the source manifests.
- The general exclusion uses a uniform explicit configuration and an integer inequality.
- Mathlib and its transitive dependencies are fetched at their pinned revisions and retain their own licenses.
- The six-point import closure includes a verbatim `Mordell/Interval.lean` from [mordell-five](https://github.com/dgjszy/mordell-five/blob/4329977fbe3f1286e089f6f655f990f47f134eba/Mordell/Interval.lean). The six-point local closure is included at the project owner's request. Its redistribution-license status remains unverified; see [the six-point attribution notice](n6/THIRD_PARTY.md). This is not a grant of permission or a relicensing of that file under MIT. That file is absent from the other staged projects.
