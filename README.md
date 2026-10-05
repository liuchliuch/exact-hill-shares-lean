# Exact Hill shares

[![Lean checks](https://github.com/liuchliuch/exact-hill-shares-lean/actions/workflows/lean.yml/badge.svg)](https://github.com/liuchliuch/exact-hill-shares-lean/actions/workflows/lean.yml)

Lean 4 formalization of [*Exact Hill Shares Are Simultaneous Guarantees*](https://arxiv.org/abs/2609.35801v1).

Allocation existence for arbitrary nonnegative real valuations, exact Hill formulas derived from their supremum definition, and a verified exact-rational allocation algorithm.

The executable entry point is `ExactHillShares.Algorithm.allocatePaper`. Runtime statements use unit-cost exact arithmetic and indexed access; they are not bit-complexity or Lean VM timing results. Source corrections document the terminal guard and the reduction required for an item-only arithmetic bound.

## Build and verify

Lean **4.19.0**, Mathlib and every transitive Git dependency are pinned.
Install [elan](https://github.com/leanprover/elan), then run:

```sh
elan toolchain install leanprover/lean4:v4.19.0
lake exe cache get
lake build
python3 scripts/verify.py
```

The verification command rebuilds the complete project library, audits originating declarations and their transitive axioms, and runs the retained regressions. Pinned Mathlib caches may be reused. Do not update `lake-manifest.json` when reproducing this version.

## Statements and proofs

Five paper-derived theorem contracts cover exact formulas, real-valued existence, ordered-tail domination, interval width, and rational output correctness. The sole definition hole is the executable allocator interface, whose actual implementation is visible in `Solution/Proofs.lean`. Mathematical propositions and model definitions are fixed; runtime proofs are covered by the full library checks, separately from these five contracts.

The [official Comparator](https://github.com/leanprover/comparator) runs in a separate Linux CI job with Landrun and the upstream systemd restriction. It compares target types and fixed declaration dependencies, enforces the axiom policy, and replays the exported solution through Lean’s default kernel. Rejection controls test the checking path. See [verification instructions](docs/VERIFICATION.md) for commands, pins and scope.

## Read the formalization

- [Paper correspondence](docs/PAPER.md)
- [Source corrections](docs/SOURCE_CORRECTIONS.md)
- [Cost model](docs/COST_MODEL.md)
- [Independent definitions](Challenge/Definitions.lean)
- [Contract proofs](Solution/Proofs.lean)
- [Executable examples](Tests/PaperPipeline.lean)

The source distribution contains the mathematical library, statement specifications, retained tests, pinned configuration and verification tools. Generated logs, dependencies and build caches are excluded; CI publishes its reports as workflow artifacts.

No project license has been selected. The cited paper and upstream dependencies retain their own licensing terms.
