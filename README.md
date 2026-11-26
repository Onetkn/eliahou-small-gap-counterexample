# Negative Eliahou numbers with consecutive first generators

**Result: Bacher's Conjecture 2.7 (arXiv:2604.25051v9) is false.**

Author: Zhengyi Liu. The paper and repository omit email and affiliation.

For every integer `M >= 1000000`, define

```text
G = {4M, 4M+1, 5M+10, 5M+100, 5M+1000, 5M+10000, 5M+100000}
S = <G> union {n : n >= 32M}.
```

This is a numerical semigroup with actual conductor `c = 32M`, multiplicity
`m = 4M`, and consecutive first two primitive elements `m, m+1`. Its counts are

```text
left elements                    k = 2024
left primitive elements        ell = 7
threshold decomposable elements  s = 1772
depth                            q = 8
remainder                      rho = 0
Eliahou number                   E = 7 * 2024 - 8 * 1772 = -8.
```

Thus the conjecture's hypothesis `gamma_1 <= m+6` holds, while its conclusion
`E >= 0` fails. This does not refute Wilf's conjecture: the Wilf number of the
same family is `8064M - 3572360 > 0`.

## Paper and proof

- [Complete paper (PDF)](output/pdf/eliahou-small-gap-counterexample.pdf)
- [LaTeX source](paper/main.tex)
- [Lean source](lean/Eliahou/Counterexample/)
- [Reproducible exact example](counterexample.py)
- [Example certificate](results/counterexample.json)
- [Lean build and axiom audit](results/lean-verification.json)

The final Lean declaration is
`Eliahou.Counterexample.not_smallGapConjecture : ¬ genericSmallGapConjecture`.
The companion `counterexample_family` theorem proves the complete family,
including the actual multiplicity, least conductor, first two primitives,
and the ordinary Eliahou value. Both are verified by the Lean kernel.

The proof is uniform in `M`. Below `36M`, each factorization uses at most eight
generators. Writing its value as `M * Q + delta` gives `delta <= 800000 < M`.
The six decimal digits of `delta` recover six coefficients, and `Q` recovers
the seventh. This proves unique short factorization and establishes the
actual conductor. Counting coefficient vectors by the total degree in the
five larger generators then gives the two displayed counts. The paper
provides the complete argument; it does not infer a general conclusion from
a bounded search.

The cited conjecture is in [Bacher, version 9, Conjecture 2.7](https://arxiv.org/html/2604.25051v9#S2.SS2).
No claim of a smallest counterexample, exhaustive literature search, or
journal acceptance is made.

## Reproduce the supplementary calculation

Python 3.12 or newer is sufficient; no third-party packages are needed.

```sh
python counterexample.py --output results/counterexample.json
```

The script generates only the sparse sums below the threshold, independently
checks the positive double sumset, and compares with the combinatorial
counts. It is supplementary to the symbolic proof.

Build the paper from the repository root with a standard LaTeX installation:

```sh
pdflatex -interaction=nonstopmode -halt-on-error -output-directory=output/pdf -jobname=eliahou-small-gap-counterexample paper/main.tex
pdflatex -interaction=nonstopmode -halt-on-error -output-directory=output/pdf -jobname=eliahou-small-gap-counterexample paper/main.tex
```

Lean setup and audit instructions are in [lean/README.md](lean/README.md).

## 中文说明

最终结论是**证否原猜想**：存在首间距为 1、Eliahou 数为 -8 的数值半群，
且上述构造给出一个无限反例族。证明使用唯一编码和组合计数，不依赖有限范围
内的枚举结论。本仓库独立收录最终反例、论文及其形式化。

## AI assistance

OpenAI Codex assisted in the construction, proof development, computational
verification, Lean formalization, and manuscript preparation.
