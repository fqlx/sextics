#!/usr/bin/env bash
# Repeatable local checks; protected CI and owner approval remain authoritative.
set -euo pipefail

script_dir=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
repo_root=$(cd -- "$script_dir/../.." && pwd)
# shellcheck source=env.sh
source "$script_dir/env.sh"

all_modules=false
sandbox_tests=false
while (($#)); do
  case "$1" in
    --all-modules) all_modules=true ;;
    --with-sandbox-tests) sandbox_tests=true ;;
    --help|-h)
      cat <<'USAGE'
Usage: scripts/cloud/verify.sh [--all-modules] [--with-sandbox-tests]

Run the default Lake build, replay the built project modules sequentially
with leanchecker, build and check content, and run Python and Node regressions.
--all-modules also builds every shared-library source before replay.
--with-sandbox-tests additionally runs the real proposal sandbox regression
suite; it requires working Docker on Linux or sandbox-exec on macOS.

Run after setup.sh, ideally in a fresh checkout. This does not grant solve
acceptance, change approval rules, authenticate GitHub, or push a branch.
USAGE
      exit 0 ;;
    *) printf 'Unknown option: %s\n' "$1" >&2; exit 2 ;;
  esac
  shift
done

for executable in python3 node npm lake; do
  if ! command -v "$executable" >/dev/null; then
    printf '%s is missing; run scripts/cloud/setup.sh first.\n' "$executable" >&2
    exit 1
  fi
done
cd -- "$repo_root"
printf 'Verifying checkout %s\n' "$(git rev-parse HEAD)"
python3 --version
node --version

cd -- "$repo_root/formal/lean"
lake --version
if ! lake env bash -c 'command -v leanchecker >/dev/null'; then
  printf 'The pinned Lean toolchain does not expose leanchecker.\n' >&2
  exit 1
fi
# Keep the literal default build: lakefile.toml selects both public libraries.
lake build
if "$all_modules"; then
  source_modules=()
  module_list=$(python3 - <<'PY'
from pathlib import Path
sources = [Path('HodgeComputer.lean'), Path('HodgeTestbed.lean')]
for root in ('HodgeComputer', 'HodgeTestbed'):
    sources.extend(Path(root).rglob('*.lean'))
for source in sorted(sources):
    print('.'.join(source.with_suffix('').parts))
PY
  )
  while IFS= read -r module; do
    [[ -z "$module" ]] || source_modules+=("$module")
  done <<< "$module_list"
  lake build "${source_modules[@]}"
fi

# Restrict replay to the project's compiled modules, excluding dependency
# artifacts. Fresh processes avoid leanchecker's namespace-wide parallelism.
built_modules=()
module_list=$(python3 - <<'PY'
from pathlib import Path
import sys

root = Path('.lake/build/lib/lean')
modules = []
for path in sorted(root.rglob('*.olean')):
    parts = path.relative_to(root).with_suffix('').parts
    if parts and parts[0] in {'HodgeComputer', 'HodgeTestbed'}:
        modules.append(parts)
for parts in modules:
    name = '.'.join(parts)
    source = Path(*parts).with_suffix('.lean')
    if not source.is_file():
        sys.exit(f'Unexpected project artifact without source: {name}')
    if any(len(child) > len(parts) and child[:len(parts)] == parts for child in modules):
        # leanchecker interprets module names as prefixes. Aggregates currently
        # contain imports only, so have no new declarations to replay. Reject
        # future aggregates with declarations rather than replay concurrently.
        if any(line.strip() and not line.strip().startswith('import ')
               for line in source.read_text().splitlines()):
            sys.exit(f'{name} has declarations and child modules; exact sequential replay needs review')
        print(f'Skip import-only aggregate: {name}', file=sys.stderr)
        continue
    print(name)
PY
)
while IFS= read -r module; do
  [[ -z "$module" ]] || built_modules+=("$module")
done <<< "$module_list"
if ((${#built_modules[@]} == 0)); then
  printf 'Default Lake build produced no project modules to replay.\n' >&2
  exit 1
fi
for module in "${built_modules[@]}"; do
  printf 'Kernel replay: %s\n' "$module"
  lake env leanchecker --verbose "$module"
done
printf 'Kernel replay passed for %s built project modules (import-only aggregates omitted).\n' "${#built_modules[@]}"

cd -- "$repo_root"
python3 scripts/build-content.py
python3 scripts/validate-records.py
python3 scripts/check-content.py
python3 scripts/cloud/test-check-github.py
python3 scripts/proposals/test_check.py
python3 scripts/test-content.py
python3 scripts/test-discord-alerts.py
node scripts/test-leaderboard.cjs
node scripts/test-divisor.cjs
node scripts/test-discussion-links.cjs
node scripts/test-surface.cjs
npm --prefix server test
if "$sandbox_tests"; then
  python3 scripts/proposals/test_lean.py
fi
# Content generation should reproduce checked-in records without drift.
git diff --exit-code -- data leaderboard discussions docs
printf 'Cloud checkout verification passed.\n'
