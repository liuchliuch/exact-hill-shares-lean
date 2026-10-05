# Paper correspondence and independent review

This map distinguishes mathematical existence, executable correctness and
structural cost bounds. Source corrections are described in
[SOURCE_CORRECTIONS.md](SOURCE_CORRECTIONS.md); the cost and validation
boundaries are in [COST_MODEL.md](COST_MODEL.md) and
[VALIDATION.md](VALIDATION.md).

## References and source identity

1. Bo Li, Hanyu Li and Chenghua Liu, *Exact Hill Shares Are Simultaneous
   Guarantees*, arXiv:2609.35801v1, 18 September 2026.
   [Abstract](https://arxiv.org/abs/2609.35801v1),
   [PDF](https://arxiv.org/pdf/2609.35801v1),
   [HTML](https://arxiv.org/html/2609.35801v1).
2. Bo Li, Hervé Moulin, Ankang Sun and Yu Zhou, *On Hill's Worst-Case Guarantee
   for Indivisible Bads*, ACM Transactions on Economics and Computation 12(4),
   Article 14, 2024.
   [DOI](https://doi.org/10.1145/3703845),
   [institutional PDF](https://eprints.gla.ac.uk/341867/2/341867.pdf).

SHA-256 identifies the source snapshots used for correspondence review:

| Source | SHA-256 |
|---|---|
| Current-paper PDF | `4cbe74ad86dab04a1a27cf16d81723fa87a92e176763bd014101928cb38b89dd` |
| Current-paper HTML | `04c71838c248d40d5796ee20883efee6491ad484cf57f36b4ea07d6f25040338` |
| External-formula PDF | `739a5a977b06ad01ec5d9cf35047f35349084eefc6662609dfe408b636debdb4` |

The manuscripts are not redistributed. These are content identities, not claims
of a publisher-supplied signature. Numbered claims and equations below refer to
the current paper. Page numbers are its printed PDF page numbers.

## Independent contracts and review method

The original manuscript was read before the initial core model, formula and
existence contracts were authored. Implementation statements were then inspected
to build the bridges and review source corrections. The rational interface was
refined to expose failure on normalized inputs; ordered-tail and interval-width
contracts were added during that review. This is a paper-first review, not a
claim that all later contract or bridge work was blind to the implementation.

`Challenge/Definitions.lean` imports Mathlib without any implementation module.
It independently defines a total item-owner function, finite bundle sums, the
infimum of maximum bundle loads, and the exact Hill-share supremum over **all
finite item counts** with nonnegative unit-total rows and an **attained exact
maximum**. Under the contracts' domains the relevant finite extrema are
attained. The exact share is neither fixed to one item count nor conditioned
only on a maximum-item upper bound.

Five semantic endpoints are independent comparison targets, named in the table
below. `Solution/Proofs.lean` proves them using the actual implementation and
independent definitions. The expected fixture's deliberate holes are obligations,
not trusted proof dependencies; see [VALIDATION.md](VALIDATION.md) for isolation
and rejection checks. Comparison covers those five targets and their dependent
definitions, not every intermediate theorem or the interpretation of runtime
counters. Other entries below record direct review of statements, definitions
and discharged hypotheses. Compilation, axiom auditing, kernel replay and this
source review address different risks; their results are recorded separately.

## Numbered claims

Most mathematical names below use namespace `ExactHillShares`; executable names
usually use `ExactHillShares.Algorithm`. `Trimmed` and `PointerLift` identify
nested namespaces. Module names refer to files under `ExactHillShares/`, and
need not be namespace names. Comparison targets use namespace `PaperContract`.

| Paper claim | Lean declarations and modules | Scope | Review / comparison target |
|---|---|---|---|
| Theorem 1.1: existence | `simultaneous_hill_allocation`, `simultaneous_hill_allocation_of_normalized` in `RealAllocation` | Arbitrary finite real-valued, nonnegative normalized rows; actual original-item allocation; genuine supremum-defined `hill`. The main API has `n >= 2`; `Consequences` covers `n = 1`. | Independent `simultaneous_guarantee` |
| Theorem 1.1: algorithm | `Algorithm.allocatePaper`, `allocatePaper_hill_safe` in `PaperAlgorithm` | Exact-rational input and original-item owner output. No sorting, crossing, feasibility, successful-run or terminal-oracle premise at the public guarantee. Includes the terminal guard correction. | Independent `rational_allocator_correct` |
| Theorem 1.1: runtime | `allocatePaper_hill_and_runtime`, `allocatePaper_hill_and_cubic`, `allocatePaperOps_bound`, `allocatePaperOps_cubic`, `allocatePaperOps_cubic_nonempty` in `PaperRuntime` | Source-shaped arithmetic bound and corrected item-cubic estimate, using explicit singleton preprocessing and the documented input/output model. | Direct review; no independent runtime contract |
| Lemma 3.1 | Mathematical lifting in `OrderedReduction`; `PointerLift.lemma3_1`, `lemma3_1_cached`, `lemma3_1_after_sorting`, `lemma3_1_with_sorting` in `PointerLiftSorting` | Sorting permutations preserve costs and maxima. The executable cheapest-remaining moving-pointer lift is separately implemented and bounded after sorting. | Direct review |
| Proposition 4.1 | `hill_eq_multiFormula`, `hillBound_eq_multiFormula` in `ExactFormula` | For `n >= 3`, derives the exact formula from finite upper packing bounds and finite extremal lower constructions. Positive maximum/total and maximum-at-most-total hypotheses are explicit. | Independent `exact_share_formula`; direct review of scaling |
| Proposition 4.2 | `hill_eq_twoFormula` in `ExactFormula`; `two_agent_endpoint_values` in `Consequences` | All exceptional two-agent cases and their shared endpoints. The external formula equality is proved, not assumed. | Independent `exact_share_formula` |
| Lemma 4.3 | `multiFormula_tail_domination`, `numericalBound_tail_scaled`, `ordered_numerical_tail`, `hillBound_tail_domination`, `RealAllocation.bound_tail` | Numerical tail domination is composed with actual sorted-prefix facts and the semantic formula. Strict crossing supplies the required removed mass. | Independent `ordered_tail_domination`; direct prefix-mass review |
| Lemma 4.4 | `twoFormula_tail_domination` and the same ordered/semantic compositions; `greedySplit_discrepancy`, `greedySplit_max_bound` in `GreedyBalance` | Exceptional two-agent domination and the source's two-bin greedy construction. The numerical theorem quantifies over all relevant total/maximum pairs. | Independent `ordered_tail_domination`; direct exceptional-case review |
| Corollary 4.5 | `numericalBound_normalize`, `numericalBound_scale`, `numericalBound_tail_scaled`, `ordered_numerical_tail`, `RealAllocation.bound_tail` | Scaling and actual residual comparisons. Zero-total and empty residuals are handled separately before positive-state division or next-item access. | Independent normalized positive-tail endpoint; direct scaling/zero-state review |
| Lemma 5.1 | `twoFormula_width`, `twoFormula_scaled_width` in `NumericalBounds`; `width_sharp_at_seven_twenty_sevenths` in `Consequences`; `Algorithm.bound_two_width` in `Terminal` | For `0 < alpha <= 1/3`, `2 hill 2 alpha - 1 >= 3 alpha/7`; positive trimmed width at the terminal and sharpness at `7/27`. | Independent `feasible_interval_width`; direct terminal/scaling review |
| Lemma 5.2 | `Trimmed.run_approximates`, `run_sound`, `trim_extremal`, `trim_unique_bucket` in `TrimmedSubsetSum` | Both one-sided approximation directions, exact witness soundness and bucket selection, with positive bucket width explicit. | Direct review |
| Lemma 5.3 | `Trimmed.final_hit`, `solve_correct`, `finite_solve_correct`, `solve_two_bin`; `Algorithm.two_feasible` in `Terminal` | Generic DP feasibility is discharged at the actual terminal using finite MMS attainment, the exact formula and a rational Boolean witness. | Direct review |
| Proposition 5.4 | `Trimmed.paper_bucket_bound`, `polynomial_complexity`, `solveOps_cubic`, `two_run_memory`, `solvePeak_quadratic`; terminal counter bounds | The `14s^2/3 + 1` cell estimate, cubic arithmetic charge, quadratic rolling state and separate cubic predecessor storage. | Direct review in the declared arithmetic/array model |

The exact-formula development includes `StableAllocation`, `SubsetSelection`,
`ExactFormulaUpper`, `ExactFormulaTwo` and `ExactFormulaLower`. Upper bounds use
proved exchange stability and finite subset selection. Lower bounds use genuine
finite normalized extremal valuations, including the exceptional six-item
construction. Combining them proves equality with the supremum over all finite
item counts.

## Definitions and equations

### Semantic definitions

`Foundations` defines allocations as item-to-agent maps, actual bundle loads,
finite minimax share, `IsNormalizedExact`, the set `hillValues` over all finite
item counts, and its real supremum `hill`. Basic domain obligations include
`mms_attained`, `exists_normalizedExact`, `hillValues_bddAbove`, `mms_le_hill`,
`maximum_le_hill`, `one_le_mul_hill`, `hill_le_one`, `exists_hill_allocation`
and `mms_smul`.

`monotoneHill` in `Consequences` is the monotone closure on its valid domain.
`hill_le_monotoneHill`, `monotoneHill_monotoneOn` and
`simultaneous_monotoneHill_allocation` establish its relation to the exact
share. `hill_three_not_monotone` supplies the relevant endpoint values; strict
improvement over the closure follows at `alpha = 2/5` from
`hill 3 (1/3) = 4/9 > 2/5 = hill 3 (2/5)`. This last implication is a mapped
corollary, not a separately named theorem.

### Equation map

| Equations | Formal counterpart |
|---|---|
| (1) | `hillBound`, with zero/degenerate states handled by the real/rational `bound` functions; `hillBound_eq_numericalBound` and `cast_bound` identify positive states. |
| (2), (5), (9), (12) | `hill_eq_multiFormula`, `hill_eq_twoFormula` and their scaled identities. |
| (3), (4) | `envelope` and `multiFormula_le_envelope`, composed with the semantic formula. |
| (6) | `safePrefix_spec`, `safePrefix_lt`, `knife_spec`; verified binary refinement in `BinaryCrossing` and cached specifications in `CachedBinaryAlgorithm`. |
| (7) | `bound_two_width`, `paper_bucket_bound` and `polynomial_bucket_bound`, including the maximum-at-least-average estimate. |
| (8) | Positive interval width divided by twice the item count in the concrete trimmed DP; exact masks/subsets connected by `witness_decodes`, `selectedSum_ofFn`, `complement_sum` and `finite_feasible_witness`. |
| (10) | `crossing_removes_many` in `OrderedPrefix`, `crossing_removed_mass`, and `next_pos_of_residual_pos`, connected to finite input rows in `OrderedTail`. |
| (11), (14) | Intersection-minimum and threshold inequalities in `TailDomination`; `EnvelopeIntersections` separately proves branch-switch and adjacent-envelope intersection equations. |
| (13) | `twoFormula_le_envelope` and its scaled counterpart for the required index range. |

`OrderedReduction` and `SortedRowProperties` establish row permutations,
nonincreasing order, preserved totals and exact maxima. `MergeSorting` provides
actual cached rational costs and their original indices. Ascending formal ranks
are related to the paper's descending ranks by proved reversal.

## Algorithms and implementation refinements

- **Algorithm 1:** `Trimmed.run` generates include/exclude candidates;
  `trim` keeps an exact extremal representative per bucket. Linked decision
  bits preserve reconstruction independently of overwritten rolling tables.
  `solve` scans both directions with closed interval endpoints. The arrays
  implement the source's direct-bucket option; its alternative balanced-map
  wording does not eliminate ordinary logarithmic map costs.
- **Algorithm 2:** `Algorithm.divide`, `choose` and `terminal` implement the
  corrected guard, feasible split and actual cheaper chooser. The caller proves
  DP feasibility from finite minimax attainment and the genuine Hill bound;
  it does not compute an exact minimax partition or assume simultaneous safety.
- **Algorithm 3:** `runCachedBinaryOnly` handles empty suffixes, one remaining
  agent, zero/single-positive early exits, two agents and recursive prefix
  assignment. `runCachedBinaryOnly_eq` establishes branch correspondence;
  `runCachedBinary_correct` supplies successful output and validity. The public
  pipeline derives sortedness and cache validity from its inputs.
- **Crossing and recursion:** `binarySafePrefix_eq_safePrefix`,
  `binaryPrefix_exact_bound` and `cachedKnife_spec` connect actual binary
  queries to the prefix before the first strict crossing. Recursion erases the
  selected agent, advances the suffix and splices the valid remaining allocation.
- **Source-specific costs:** `countedSortRows_operations_le`,
  `prefixRowsWork_linear_nm`, `cachedSuffix_eq_sum`,
  `runCachedBinary_operations_le`, `allocateBinaryRowsOps_bound`,
  `runCachedBinary_terminalCalls_le` and `PointerLift.lemma3_1_after_sorting`
  account for sorting, stored sums, recursive queries, one terminal and pointer
  lifting. `allocatePaperOps_source_bound` retains every stage before the
  singleton reduction. Numeric counter bounds and source-level cost interpretation
  are distinct obligations; [COST_MODEL.md](COST_MODEL.md) is authoritative.

## Bridge review

The solution bridges were separately inspected after the contracts were fixed.
They import the independent definitions and production development, never the
expected proof placeholders. Exact-maximum equivalence is proved both ways;
the exact-share bridge equates the sets under the supremum. Bundle, peak and
minimax representations agree by unfolding. The formula bridge retains every
two-agent branch. The tail bridge derives head/next-item positivity and upper
bounds from the ordered row, without adding a removed-mass hypothesis to its
contract; the width bridge supplies the valid-domain bounds.

The rational adapter maps the actual `allocatePaper` owner vector to its owner
function. Its proof establishes actual `some` output equality and safety; it
does not replace a failed run with a classically chosen allocation. The zero-agent
adapter branch lies outside the `n >= 2` contract. Source review found no circular
import, custom axiom, assumed conclusion or semantic weakening in these bridges.
That conclusion does not substitute for the separately recorded validation runs.

## Regressions and coverage boundary

Executable tests cover the zero-width terminal case, the genuinely cheaper
chooser, ordered residuals, cached binary queries, sorting, pointer lifting,
actual original-item loads and agreement between output-only and analyzed
outputs. Singleton tests place panic-backed costs behind `n >= m` inputs to
check that this branch reads no valuation, including the equality boundary and
large agent counts. The validator rejects panic diagnostics even when a Lean
process returns status zero. Tests supplement universal proofs.

This map covers the current paper's numbered mathematical claims, equations,
algorithms and substantive intermediate mathematical/cost statements, subject
to the explicit corrections. Literature priority, novelty, historical claims,
NP-hardness context and unrelated fairness results are not formalized here.
The mathematical exact-formula and ordered-lift dependencies are discharged.
No claim is made of a verified Lean compiler, arbitrary unsafe executable IR,
a bit-complexity theorem, or a VM runtime bound.
