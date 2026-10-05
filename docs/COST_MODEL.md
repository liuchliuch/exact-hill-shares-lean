# Algorithm and cost model

Let `n` be the number of agents and `m` the number of items. The existence
result concerns arbitrary nonnegative real valuations. Executable algorithms
receive exact rational costs. Comparisons, thresholds, floor bucket indices and
subset sums use exact arithmetic rather than floating-point approximations.

## What the counters measure

The runtime theorems bound explicit structural operation counters in a sequential
RAM model. Unit-cost operations include exact rational arithmetic, comparisons
and floor; integer/index control; indexed array reads and replacement; and
amortized array push. Traversing lists, finite sets, masks and DP cells is charged
explicitly. Immutable witness tails may be shared.

These are theorems about the declared counters. The relationship between those
charges and the output-only program is established through output/branch equality
proofs and source-level correspondence. There is no formal small-step simulation
of Lean execution, compiler-correctness proof, VM timing theorem, or bit-cost
bound. Rational numerator and denominator sizes, persistence copying, garbage
collection and compiler transformations require a different analysis.

## Output-only execution

`Algorithm.allocatePaper` is independently defined as an output-only program.
It does not evaluate `terminalOps`, `divideOps`, `solveOps` or `runOps`.
`allocatePaper_eq_counted` proves equality with the analyzed output.

`allocatePaperCounted` and `allocatePaperOps` are diagnostic interfaces.
Evaluating their annotations may repeat model computations, so their own
execution time is not bounded by the number they return. The analysis does not
assume lazy evaluation or compiler elimination of unused record fields.

## Source-shaped bound

For the source-aligned `allocatePaper` implementation, the proved stages are:

| Stage | Structural arithmetic charge |
|---|---|
| One counted merge sort per row | `O(n m log(m+1))` |
| Materialized prefix/suffix sums | `O(n m)` |
| Binary strict-crossing recursion | `O(n^2 log(m+1))` |
| At most one trimmed two-agent terminal | `O(m^3)` |
| Moving-pointer lift after sorting | `O(n m)` |

`allocatePaperOps_bound` gives the explicit combined bound

```text
120 n m (log2(m+1) + 1)
+ 1000 n^2 (log2(m+1) + 1)
+ 3000 (m+1)^3.
```

`allocatePaper_hill_and_runtime` combines that bound with correctness of the
actual original-item output. The main correctness API assumes two or more
agents and normalized nonnegative rows; the operation bound itself applies to
positive agent counts and nonnegative rational costs.

Each row is sorted and materialized once. Prefix arrays are built once, and each
active crossing boundary is materialized once. Rank owners are materialized
before the lift. The lift uses sorted-index cursors and global used flags, and
writes original-item owners directly. Each visited entry advances one cursor,
so at most `n m` entries are visited. Re-sorting on each lookup or recomputing a
matching for each output query would not satisfy this analysis.

## Why the corrected bound can depend only on items

When `n >= m`, `allocatePaper` assigns each item to a distinct agent before
reading any valuation. The exact Hill share is at least the largest individual
item, so this branch is safe. Its charge is `3 m + 2`. For the remaining branch,
`n < m` bounds the agent-dependent terms above by an item-cubic expression.

The resulting theorems are:

- `allocatePaperOps_cubic`: at most `6000 (m+1)^3` operations
- `allocatePaperOps_cubic_nonempty`: at most `48000 m^3` when `m > 0`
- `allocatePaper_hill_and_cubic`: actual-output correctness and the first bound

This uses a normalized-input promise and random access to an already available
input, including its dimensions. The output is a length-`m` owner vector; empty
bundles are implicit. Mandatory ingestion or validation of all `n m` input values
adds `O(n m)` work. Materializing `n` separate bundle containers adds output work.
Those costs must be included in applications that require them.

## Terminal and storage accounting

The two-agent terminal takes the singleton shortcut when `p/T >= 1/3` and uses
the one-sided trimmed DP only at positive bucket width. Both feasibility and
witness reconstruction are proved. The chooser receives her cheaper part,
including ties.

The DP has quadratic rolling state and cubic predecessor storage in the number
of residual items. Those are separate bounds. Rolling-state size must not be
reported as total memory for a run that retains reconstruction data, input
arrays and output owners.
