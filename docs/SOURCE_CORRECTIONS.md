# Source corrections and proof choices

The reference version is [arXiv:2609.35801v1](https://arxiv.org/abs/2609.35801v1),
18 September 2026. Page references below use that PDF's page numbers. The
formalization targets the corrected claims described here; these corrections
do not refute the allocation-existence theorem.

## 1. Guard the two-agent trimmed routine

Section 5.1 (p. 8) gives a singleton split when the maximum-item fraction
`p/T >= 1/3`. Algorithm 2 (p. 10) omits this guard and calls Algorithm 1
unconditionally, although the trimmed routine (p. 9) requires `p/T < 1/3`.

For costs `(1/2, 1/4, 1/4)`, the total is `T = 1`, the maximum and exact
threshold are `p = D = 1/2`, and the interval width is `W = 2D - T = 0`.
Thus the literal call has bucket width `eta = W/(2s) = 0`. The same problem
can arise at a recursive two-agent residual.

`Algorithm.divide` implements the prose's singleton shortcut before the trimmed
call. `divide_spec` proves both returned parts meet the divider's threshold;
`choose_chooser_le_half` proves the actual chooser receives her cheaper part.
The executable regressions include the zero-width example.

## 2. Preserve agent-dependent work before deriving an item-only bound

The final analysis on p. 12 includes sorting and recursion terms that depend on
`n`. Those terms cannot be discarded for arbitrarily many agents. The
source-shaped bound is

```text
O(n m log(m+1) + n^2 log(m+1) + m^3).
```

The implementation explicitly handles `n >= m` by singleton assignment before
any valuation read. The remaining case has `n < m`, which yields an item-cubic
structural bound. This reduction assumes random-access input and an item-owner
vector with implicit empty bundles. Mandatory dense input ingestion and explicit
bundle-container output add their own costs. See [COST_MODEL.md](COST_MODEL.md).

## 3. State the formula domain and universal tail step

Proposition 4.1 requires at least three agents, as stated in its preceding
prose. The two-agent exceptional formula is essential. The formal APIs make
this distinction explicit instead of applying the generic formula at `n = 2`.

Appendix B's `k = 0` construction must apply to every finite tail with the
specified total and maximum before taking the Hill-share supremum. A partition
of one actual tail alone only bounds that tail's minimax share. The formal
numerical bounds are universal in those parameters and are composed with the
proved semantic formula.

## 4. Make the external subset argument precise

The exact formulas rely on the earlier
[Li–Moulin–Sun–Zhou article](https://doi.org/10.1145/3703845). Its exceptional
two-agent argument states an item lower bound too broadly after selecting a
minimal subset. The relevant lower bound is needed only for members of that
subset. The formal finite-subset-gap proof uses that restricted scope, and a
unified three-obstruction argument proves the exceptional upper bound.

The external formula is not assumed: finite upper packing bounds and explicit
finite extremal lower instances prove the actual supremum/formula equalities.

## Equivalent proof and implementation choices

- The upper packing proof uses an allocation minimizing the sum of squared
  loads. A proved exchange-energy identity supplies the required subset-exchange
  obstruction in place of the external lexicographic argument.
- The trimmed recurrence processes the input list right-to-left while retaining
  witness bits in original order. Every item is processed once, and exact
  witness soundness and both one-sided approximation directions are proved.
- Sorting uses ascending ranks internally where convenient; proved reversals
  connect them to the paper's descending order.
- Real-valued existence and rational computation are separate developments.
  The real proof may select an attained exact minimax partition. The executable
  terminal instead uses the proved feasible interval and trimmed subset-sum DP.
- A supplemental insertion-sort/linear-crossing implementation is retained.
  The separate `allocatePaper` pipeline supplies the source-specific merge-sort,
  binary-crossing and moving-pointer estimates.
