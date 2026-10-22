#!/usr/bin/env bash
# Idempotent setup for a trusted maintenance checkout in a Linux cloud worker.
set -euo pipefail

repo=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../.." && pwd)
export SEXTICS_CLOUD_HOME="${SEXTICS_CLOUD_HOME:-/workspace/tooling/sextics}"
export UV_PYTHON_INSTALL_DIR="${UV_PYTHON_INSTALL_DIR:-$SEXTICS_CLOUD_HOME/python}"

fail() { printf 'Cloud setup: %s\n' "$*" >&2; exit 1; }
system_install() {
    command -v apt-get >/dev/null || fail "Install the missing system packages with your image's package manager (Debian/Ubuntu apt is supported automatically)."
    local elevate=()
    if [[ $(id -u) != 0 ]]; then
        command -v sudo >/dev/null || fail 'System packages are missing; an administrator must install them or provide passwordless sudo.'
        elevate=(sudo -n)
    fi
    "${elevate[@]}" apt-get update
    "${elevate[@]}" env DEBIAN_FRONTEND=noninteractive apt-get install -y "$@"
}

[[ $(uname -s) == Linux ]] || fail 'Run this setup in a Linux cloud worker.'
missing=0
for program in curl git tar xz zstd gcc make sha256sum flock; do
    command -v "$program" >/dev/null || missing=1
done
if [[ $missing == 1 ]]; then
    system_install ca-certificates curl git build-essential unzip zstd xz-utils util-linux
fi
mkdir -p "$SEXTICS_CLOUD_HOME"
# Serialize setup against the same persistent cache; do not share it with an
# untrusted worker or a concurrently running build that writes these packages.
exec 9> "$SEXTICS_CLOUD_HOME/setup.lock"
flock 9
scratch=$(mktemp -d "$SEXTICS_CLOUD_HOME/setup.XXXXXXXX")
trap 'rm -rf -- "$scratch"' EXIT

if [[ -n "${SEXTICS_CLOUD_PYTHON:-}" ]]; then
    python=$SEXTICS_CLOUD_PYTHON
elif command -v python3.11 >/dev/null; then
    python=$(command -v python3.11)
elif command -v uv >/dev/null; then
    # uv retains the configured proxy, certificate and Python-mirror settings.
    uv python install 3.11
    python=$(uv python find 3.11)
else
    system_install python3.11 python3.11-venv
    python=$(command -v python3.11) || fail 'Python 3.11 is unavailable. Supply SEXTICS_CLOUD_PYTHON or provision uv in the worker image.'
fi
"$python" -c 'import sys, venv; assert sys.version_info[:2] == (3, 11), "Python 3.11 is required"'
if ! "$python" -c 'import ensurepip' >/dev/null 2>&1; then
    system_install python3.11-venv
fi
printf '%s\n' "$python" > "$scratch/python-path"
mv "$scratch/python-path" "$SEXTICS_CLOUD_HOME/python-path"
# shellcheck source=env.sh
source "$repo/scripts/cloud/env.sh"

mkdir -p "$MATHLIB_CACHE_DIR" "$PIP_CACHE_DIR" "$npm_config_cache" "$SEXTICS_CLOUD_HOME/node"
case "$(uname -m)" in
    x86_64)
        node_hash=6c172a9ab6718f7b801fb5a7bd486af2ee5e32758086a04b84fcce2aa77095e6
        elan_arch=x86_64
        elan_hash=620db834935d0da55ac9cda207b2e370e8034061cbb0228af5eb6c14b02f0c0c ;;
    aarch64 | arm64)
        node_hash=dbabf7a1cbf947e6059ffad2c27b80041db97dea1e553b62afdee7f13fca336e
        elan_arch=aarch64
        elan_hash=4f088beed941e0c3591e712a62f42a45dce07feea76b5040cce5652f9a6ae54f ;;
    *) fail 'Only Linux x86_64 and aarch64 release binaries are supported.' ;;
esac
download() {
    # Keep the worker's proxy and CA settings, including managed placeholders.
    curl --fail --location --retry 3 --connect-timeout 30 "$1" --output "$2"
    printf '%s  %s\n' "$3" "$2" | sha256sum --check --status || fail "Checksum mismatch for $1"
}

if [[ ! -x "$SEXTICS_CLOUD_NODE_HOME/bin/node" ]] || [[ $("$SEXTICS_CLOUD_NODE_HOME/bin/node" --version) != "v$SEXTICS_CLOUD_NODE_VERSION" ]]; then
    archive=$(basename "$SEXTICS_CLOUD_NODE_HOME").tar.xz
    download "https://nodejs.org/dist/v$SEXTICS_CLOUD_NODE_VERSION/$archive" "$scratch/$archive" "$node_hash"
    tar -xJf "$scratch/$archive" -C "$scratch"
    [[ ! -e "$SEXTICS_CLOUD_NODE_HOME" ]] || fail "Existing Node installation is incomplete or has the wrong version: $SEXTICS_CLOUD_NODE_HOME (preserved)."
    mv "$scratch/$(basename "$SEXTICS_CLOUD_NODE_HOME")" "$SEXTICS_CLOUD_NODE_HOME"
fi

if [[ ! -x "$ELAN_HOME/bin/elan" ]]; then
    # The tagged elan-init.sh still downloads /latest; use the exact release
    # asset, with the SHA256 recorded by the official v4.2.0 GitHub release.
    archive="elan-$elan_arch-unknown-linux-gnu.tar.gz"
    download "https://github.com/leanprover/elan/releases/download/v4.2.0/$archive" "$scratch/$archive" "$elan_hash"
    mkdir "$scratch/elan"
    tar -xzf "$scratch/$archive" -C "$scratch/elan"
    "$scratch/elan/elan-init" -y --no-modify-path --default-toolchain none
fi
toolchain=$(tr -d '\r\n' < "$repo/formal/lean/lean-toolchain")
elan toolchain install "$toolchain"

# Re-running venv also repairs an interrupted creation without deleting packages.
"$python" -m venv "$SEXTICS_CLOUD_VENV"
"$SEXTICS_CLOUD_VENV/bin/python" -m pip install -r "$repo/scripts/requirements-content.txt"
npm ci --prefix "$repo/server" --ignore-scripts --no-audit --no-fund

mkdir -p "$repo/formal/lean/.lake" "$SEXTICS_CLOUD_PACKAGES"
packages_link="$repo/formal/lean/.lake/packages"
if [[ -L "$packages_link" ]]; then
    # Repoint only a link already managed by this setup. Preserve other caches.
    "$python" - "$packages_link" "$SEXTICS_CLOUD_HOME/lake" <<'PY'
import pathlib
import sys
target = pathlib.Path(sys.argv[1]).resolve()
cache = pathlib.Path(sys.argv[2]).resolve()
if not target.is_relative_to(cache):
    raise SystemExit(f'Existing dependency link points outside this cloud cache; preserved: {target}')
PY
    ln -sfn "$SEXTICS_CLOUD_PACKAGES" "$packages_link"
elif [[ -e "$packages_link" ]]; then
    fail "Existing $packages_link is preserved. Use a clean checkout, or explicitly relocate that directory before configuring persistent dependencies."
else
    ln -s "$SEXTICS_CLOUD_PACKAGES" "$packages_link"
fi

# Snapshot the inputs; Lake must consume the committed manifest, never update it.
for name in lean-toolchain lakefile.toml lake-manifest.json; do
    cp "$repo/formal/lean/$name" "$scratch/$name"
done
cd "$repo/formal/lean"
"$python" - <<'PY'
import json
import pathlib
import tomllib
config = tomllib.loads(pathlib.Path('lakefile.toml').read_text())
manifest = json.loads(pathlib.Path('lake-manifest.json').read_text())
required = next(p for p in config['require'] if p['name'] == 'mathlib')
resolved = next(p for p in manifest['packages'] if p['name'] == 'mathlib')
if required['rev'] != resolved['rev'] or required['git'] != resolved['url']:
    raise SystemExit('lakefile.toml and lake-manifest.json disagree about the exact mathlib pin; refusing to resolve or update dependencies.')
PY
check_package_sources() {
    # Refuse mutated package sources rather than overwriting an existing cache.
    "$python" - "$repo/formal/lean/lake-manifest.json" "$SEXTICS_CLOUD_PACKAGES" "$1" <<'PY'
import json
import pathlib
import subprocess
import sys
manifest = json.loads(pathlib.Path(sys.argv[1]).read_text())
for package in manifest['packages']:
    if package['type'] != 'git':
        raise SystemExit(f"Unsupported non-Git dependency: {package['name']}")
    path = pathlib.Path(sys.argv[2]) / package['name']
    if sys.argv[3] == 'allow-missing' and not path.exists():
        continue
    actual = subprocess.check_output(['git', '-C', str(path), 'rev-parse', 'HEAD'], text=True).strip()
    if actual != package['rev']:
        raise SystemExit(f"Cached {package['name']} revision mismatch; existing cache preserved.")
    for args in (['diff', '--quiet'], ['diff', '--cached', '--quiet']):
        if subprocess.run(['git', '-C', str(path), *args]).returncode:
            raise SystemExit(f"Cached {package['name']} has tracked changes; existing cache preserved.")
PY
}
check_package_sources allow-missing
proxy_help() {
    cat >&2 <<'TEXT'
Cloud network access must permit GET/HEAD of actual public cache blobs at
https://lakecache.blob.core.windows.net/mathlib4-master/f/*.ltar
and the pinned cache client's legacy fallback /mathlib4/f/*.ltar.
A successful request to the hostname or container alone does not test this.
Enable the cloud environment's requested network access policy, then retry setup.
Do not disable TLS, bypass the configured proxy, or replace the pinned cache URL.
TEXT
}
[[ -z "${MATHLIB_CACHE_GET_URL:-}" && -z "${MATHLIB_CACHE_FROM:-}" && -z "${MATHLIB_CACHE_REPO_SCOPE:-}" ]] ||
    fail 'A Mathlib cache source override is set. Use the pinned default cache configuration for this setup.'
# `lookup` reads an existing local archive. Populate this small root first;
# this also tests an actual cache transfer on a cold worker.
if ! lake exe cache get Mathlib.Init 2>&1 | tee "$scratch/cache-init.log"; then
    proxy_help
    exit 1
fi
lake exe cache lookup Mathlib.Init 2>&1 | tee "$scratch/cache-lookup.log"
artifact=$("$python" - "$scratch/cache-lookup.log" <<'PY'
import pathlib
import re
import sys
text = pathlib.Path(sys.argv[1]).read_text()
match = re.search(r'^Mathlib\.Init: .*[/\\]([0-9a-f]{16}\.ltar)$', text, re.MULTILINE)
if not match:
    raise SystemExit('Cache lookup did not identify the Mathlib.Init archive hash.')
# This is the primary public container of the committed Cache/Infra.lean;
# the cache client itself retains its own pinned default/fallback selection.
print('https://lakecache.blob.core.windows.net/mathlib4-master/f/' + match[1])
PY
)
status=0
http_code=$(curl --fail --location --retry 2 --connect-timeout 30 --max-time 120 \
    --output "$scratch/cache-artifact.ltar" --write-out '%{http_code}' "$artifact") || status=$?
if [[ $status != 0 || ! -s "$scratch/cache-artifact.ltar" ]]; then
    printf 'Cache artifact GET failed (HTTP %s): %s\n' "$http_code" "$artifact" >&2
    proxy_help
    exit 1
fi
if ! lake exe cache get 2>&1 | tee "$scratch/cache-get.log"; then
    proxy_help
    exit 1
fi
[[ -s "$SEXTICS_CLOUD_PACKAGES/mathlib/.lake/build/lib/lean/Mathlib/Tactic.olean" ]] ||
    fail 'The cache command did not provide Mathlib/Tactic.olean. Inspect cache misses and network access before building.'
check_package_sources require-all
for name in lean-toolchain lakefile.toml lake-manifest.json; do
    cmp -s "$repo/formal/lean/$name" "$scratch/$name" || fail "Lake changed $name; inspect the checkout before continuing."
done
lake --version
lean --version
printf 'Setup complete. Activate each new shell with:\n  source %q\n' "$repo/scripts/cloud/env.sh"
printf 'Dependencies persist in %s\n' "$SEXTICS_CLOUD_HOME"
