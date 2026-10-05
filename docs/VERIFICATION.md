# Verification

The project pins Lean 4.19.0 and all mathematical dependencies in `lake-manifest.json`. `verification/library-provenance.json` records the complete fixed mathematical source inventory. `scripts/snapshot.py` hashes the current proof sources, comparison inputs and verification tools. A successful report is relevant only to that exact snapshot.

## Complete library

```sh
lake exe cache get
python3 scripts/verify.py
```

This performs a clean project build and checks every retained mathematical module. The axiom policy permits only `propext`, `Classical.choice` and `Quot.sound`. The proof library does not import specification placeholders. Additional executable regressions or contextual body checks are documented by the commands in `scripts/verify.py`.

The check reuses the pinned public Mathlib cache; it does not rebuild all public dependencies or verify the Lean compiler. Reports and logs are written to `.lake/publication-results/`, which is excluded from the source distribution.

## Official Comparator

The comparison covers **5 theorem targets**. Five paper-derived theorem contracts cover exact formulas, real-valued existence, ordered-tail domination, interval width, and rational output correctness. The sole definition hole is the executable allocator interface, whose actual implementation is visible in `Solution/Proofs.lean`. Mathematical propositions and model definitions are fixed; runtime proofs are covered by the full library checks, separately from these five contracts.

All official tools are pinned. Linux execution requires an unprivileged account, Landlock ABI 6 or newer, real Landrun, Go 1.24 or newer, and a working user systemd manager. The outer systemd process denies AF_UNIX sockets following upstream security guidance. A shell adapter preserves command argument separators; it does not change the official comparison or kernel code.

```sh
bash scripts/bootstrap-comparator.sh --with-landrun
python3 scripts/compare.py --sandboxed
```

The official compatible Comparator is built for Lean 4.19.0 by adapting only toolchain and dependency metadata; its Lean source is unchanged. Five controlled projects test acceptance and rejection, including changed statements, changed definitions, a forbidden axiom and an admitted proof. The allocator definition hole is limited to an executable function interface; its implementation requires inspection alongside its output theorem. Full validation additionally recompiles every proof and test into a fresh object directory and replays the imported safe declaration closure.

Comparator proves agreement with the checked specification, not that an informal paper was translated correctly. The paper map, definitions, hypotheses and any source corrections remain part of the mathematical review. The kernel used is Lean’s own default kernel; no external kernel is enabled.

The `Lean checks` workflow runs full library verification and official Comparator independently. Each job uploads its report and complete diagnostic logs, including on failure. Source reports must agree on the same source snapshot before release.
