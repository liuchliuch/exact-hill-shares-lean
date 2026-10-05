#!/usr/bin/env bash
# Exercise the actual origin/axiom/replay validator on isolated bad fixtures.
# None of the fixture modules is placed in the theorem source tree.
set -euo pipefail
ROOT=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
cd "$ROOT"
if [[ -n ${LEAN_HOME:-} ]]; then export PATH="$LEAN_HOME/bin:$PATH"; fi
TMP=$(mktemp -d "${TMPDIR:-/tmp}/exact-hill-audit-negative.XXXXXX")
trap 'rm -rf "$TMP"' EXIT
LOG=${AUDIT_LOG_DIR:-"$ROOT/build/validation"}
mkdir -p "$LOG"
BASE_PATH=$(lake env printenv LEAN_PATH)
export LEAN_PATH="$TMP:$BASE_PATH"

cat > "$TMP/SourceUnsafeAxiom.lean" <<'EOF'
import Init
namespace UnrelatedUnsafeNamespace
private unsafe axiom hiddenCompilerLikeAssumption : False
end UnrelatedUnsafeNamespace
EOF
if python3 scripts/scan-proof-sources.py "$TMP/SourceUnsafeAxiom.lean" \
    > "$LOG/negative-unsafe-source.log" 2>&1; then
  echo "FAIL: an explicit unsafe custom axiom escaped the source scanner" >&2; exit 1
fi
grep -q 'SOURCE_POLICY_REJECT' "$LOG/negative-unsafe-source.log"
grep -q $'\tunsafe' "$LOG/negative-unsafe-source.log"
grep -q $'\taxiom' "$LOG/negative-unsafe-source.log"

cat > "$TMP/SourceCommentFixture.lean" <<'EOF'
import Init
/- unsafe axiom ignored : False
   /- nested sorry, admit, macro, run_cmd -/
-/
-- private unsafe axiom documentationOnly : False
def ordinaryString : String := "unsafe axiom sorry admit"
theorem ordinaryProof : True := True.intro
EOF
python3 scripts/scan-proof-sources.py "$TMP/SourceCommentFixture.lean" \
  > "$LOG/negative-scanner-comment-control.log" 2>&1

cat > "$TMP/AuditPrivateAxiom.lean" <<'EOF'
import Init
namespace CompletelyUnrelatedNamespace
private axiom unusedHiddenAssumption : False
theorem visibleHarmlessStatement : True := True.intro
end CompletelyUnrelatedNamespace
EOF
lean --root="$TMP" -o "$TMP/AuditPrivateAxiom.olean" "$TMP/AuditPrivateAxiom.lean"
if lean --run scripts/AuditOrigins.lean -- --safe-declarations --axioms-only AuditPrivateAxiom \
    > "$LOG/negative-private-axiom.log" 2>&1; then
  echo "FAIL: unused private custom axiom escaped the validator" >&2; exit 1
fi
grep -q 'FORBIDDEN_AXIOMS' "$LOG/negative-private-axiom.log"
grep -q '_private.AuditPrivateAxiom' "$LOG/negative-private-axiom.log"

cat > "$TMP/AuditSorry.lean" <<'EOF'
import Init
namespace UnrelatedAgain
private theorem hiddenAdmission : False := by sorry
end UnrelatedAgain
EOF
lean --root="$TMP" -o "$TMP/AuditSorry.olean" "$TMP/AuditSorry.lean" \
  > "$LOG/negative-sorry-build.log" 2>&1
if lean --run scripts/AuditOrigins.lean -- --safe-declarations --axioms-only AuditSorry \
    > "$LOG/negative-sorry.log" 2>&1; then
  echo "FAIL: unused private sorryAx escaped the validator" >&2; exit 1
fi
grep -q 'FORBIDDEN_AXIOMS' "$LOG/negative-sorry.log"
grep -q 'sorryAx' "$LOG/negative-sorry.log"

# The forbidden axiom is deliberately in a dependency whose module was NOT
# requested as an audit origin. Only recursive proof-dependency collection
# discovers this violation at the safe project theorem/helper.
cat > "$TMP/AuditForeignDependency.lean" <<'EOF'
import Init
axiom foreignAssumption : False
EOF
cat > "$TMP/AuditTransitive.lean" <<'EOF'
import AuditForeignDependency
namespace YetAnotherNamespace
private theorem helper : False := foreignAssumption
theorem exported : False := helper
end YetAnotherNamespace
EOF
lean --root="$TMP" -o "$TMP/AuditForeignDependency.olean" "$TMP/AuditForeignDependency.lean"
lean --root="$TMP" -o "$TMP/AuditTransitive.olean" "$TMP/AuditTransitive.lean"
if lean --run scripts/AuditOrigins.lean -- --safe-declarations --axioms-only AuditTransitive \
    > "$LOG/negative-transitive-axiom.log" 2>&1; then
  echo "FAIL: transitive foreign custom axiom escaped the safe-origin audit" >&2; exit 1
fi
grep -q 'FORBIDDEN_AXIOMS' "$LOG/negative-transitive-axiom.log"
grep -q 'foreignAssumption' "$LOG/negative-transitive-axiom.log"

# Deliberately corrupt proof body, without introducing any extra axiom.
# The low-level doCheck=false operation is confined to this generated fixture.
cat > "$TMP/MakeInvalid.lean" <<'EOF'
import Lean
open Lean
def main (args : List String) : IO Unit := do
  initSearchPath (← findSysroot)
  let env ← importModules #[{ module := `Init }] {} (trustLevel := 0)
  let env := env.setMainModule `AuditInvalidArtifact
  let bad : Declaration := .thmDecl {
    name := `AnotherUnrelatedNamespace.incorrect
    levelParams := []
    type := mkConst ``False
    value := mkConst ``True.intro }
  match env.addDeclCore 0 bad none (doCheck := false) with
  | .error _ => throw <| IO.userError "Fixture creation unexpectedly failed"
  | .ok env => writeModule env (args.headD "AuditInvalidArtifact.olean")
EOF
lean --run "$TMP/MakeInvalid.lean" "$TMP/AuditInvalidArtifact.olean"
printf 'import AuditInvalidArtifact\n' > "$TMP/ImportInvalid.lean"
if lean -t 0 "$TMP/ImportInvalid.lean" > "$LOG/negative-trust-zero-import.log" 2>&1; then
  echo 'OBSERVATION: lean -t 0 accepted the invalid imported artifact; replay is required.' \
    | tee -a "$LOG/negative-trust-zero-import.log"
else
  echo 'OBSERVATION: this compiler rejected the invalid artifact at import.' \
    | tee -a "$LOG/negative-trust-zero-import.log"
fi
if lean --run scripts/AuditOrigins.lean AuditInvalidArtifact \
    > "$LOG/negative-invalid-artifact.log" 2>&1; then
  echo "FAIL: invalid proof body escaped kernel replay" >&2; exit 1
fi
grep -q 'AXIOM_AUDIT_PASSED' "$LOG/negative-invalid-artifact.log"
grep -q 'KERNEL_REPLAY_BEGIN' "$LOG/negative-invalid-artifact.log"
grep -q 'declaration type mismatch' "$LOG/negative-invalid-artifact.log"

# Ensure the repaired checked-kernel constructor/recursor lookup retains the
# exact metadata-equality checks, rather than merely accepting existing names.
cat > "$TMP/AuditShapeFixture.lean" <<'EOF'
import Init
structure AuditShape where
  value : Nat
EOF
lean --root="$TMP" -o "$TMP/AuditShapeFixture.olean" "$TMP/AuditShapeFixture.lean"
cat > "$TMP/CorruptShape.lean" <<'EOF'
import Lean
open Lean
def main (args : List String) : IO Unit := do
  let dir : System.FilePath := args.headD "."
  let (data, _region) ← readModuleData (dir / "AuditShapeFixture.olean")
  let ctorData := { data with constants := data.constants.map fun info =>
    match info with
    | .ctorInfo c => if c.name == `AuditShape.mk then
        .ctorInfo { c with numFields := c.numFields + 1 } else info
    | _ => info }
  saveModuleData (dir / "AuditMalformedConstructor.olean") `AuditMalformedConstructor ctorData
  let recData := { data with constants := data.constants.map fun info =>
    match info with
    | .recInfo r => if r.name == `AuditShape.rec then
        .recInfo { r with k := !r.k } else info
    | _ => info }
  saveModuleData (dir / "AuditMalformedRecursor.olean") `AuditMalformedRecursor recData
EOF
lean --run "$TMP/CorruptShape.lean" "$TMP"
for fixture in AuditMalformedConstructor AuditMalformedRecursor; do
  if lean --run scripts/AuditOrigins.lean -- --safe-declarations "$fixture" \
      > "$LOG/negative-$fixture.log" 2>&1; then
    echo "FAIL: malformed constructor/recursor escaped equality validation: $fixture" >&2; exit 1
  fi
  grep -q 'AXIOM_AUDIT_PASSED' "$LOG/negative-$fixture.log"
done
grep -q 'Invalid constructor AuditShape.mk' "$LOG/negative-AuditMalformedConstructor.log"
grep -q 'Invalid recursor AuditShape.rec' "$LOG/negative-AuditMalformedRecursor.log"
echo 'NEGATIVE_TESTS_PASSED: unsafe source axiom, private axiom, sorryAx, transitive foreign axiom, malformed proof, malformed constructor, and malformed recursor all rejected; comment/string control accepted.'
