#!/usr/bin/env bash
# Source this file after setup.sh in every new cloud shell.
# It changes this shell only; it never rewrites a profile or Git credentials.

_sextics_cloud_repo=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../.." && pwd) || return
export SEXTICS_CLOUD_HOME="${SEXTICS_CLOUD_HOME:-/workspace/tooling/sextics}"
export ELAN_HOME="${ELAN_HOME:-$SEXTICS_CLOUD_HOME/elan}"
export UV_PYTHON_INSTALL_DIR="${UV_PYTHON_INSTALL_DIR:-$SEXTICS_CLOUD_HOME/python}"
export MATHLIB_CACHE_DIR="${MATHLIB_CACHE_DIR:-$SEXTICS_CLOUD_HOME/cache/mathlib}"
export PIP_CACHE_DIR="${PIP_CACHE_DIR:-$SEXTICS_CLOUD_HOME/cache/pip}"
export npm_config_cache="${npm_config_cache:-$SEXTICS_CLOUD_HOME/cache/npm}"

case "$(uname -s)/$(uname -m)" in
    Linux/x86_64) _sextics_cloud_platform=linux-x64 ;;
    Linux/aarch64 | Linux/arm64) _sextics_cloud_platform=linux-arm64 ;;
    *) printf '%s\n' 'Cloud setup supports glibc Linux x86_64 and aarch64.' >&2; return 1 ;;
esac
export SEXTICS_CLOUD_NODE_VERSION=24.22.1
export SEXTICS_CLOUD_NODE_HOME="$SEXTICS_CLOUD_HOME/node/node-v$SEXTICS_CLOUD_NODE_VERSION-$_sextics_cloud_platform"

if [[ -z "${SEXTICS_CLOUD_PYTHON:-}" ]]; then
    if [[ -r "$SEXTICS_CLOUD_HOME/python-path" ]]; then
        IFS= read -r SEXTICS_CLOUD_PYTHON < "$SEXTICS_CLOUD_HOME/python-path"
    else
        SEXTICS_CLOUD_PYTHON=$(command -v python3.11) || {
            printf '%s\n' 'Run scripts/cloud/setup.sh to provision Python 3.11 first.' >&2
            return 1
        }
    fi
fi
export SEXTICS_CLOUD_PYTHON
_sextics_cloud_keys=$("$SEXTICS_CLOUD_PYTHON" - "$_sextics_cloud_repo" "$_sextics_cloud_platform" <<'PY'
import hashlib
import pathlib
import sys

if sys.version_info[:2] != (3, 11):
    raise SystemExit('Cloud dependencies use Python 3.11, matching the content CI environment.')
root = pathlib.Path(sys.argv[1])
platform = sys.argv[2]
pins = hashlib.sha256(platform.encode())
for name in ('lean-toolchain', 'lake-manifest.json', 'lakefile.toml'):
    pins.update(name.encode() + b'\0' + (root / 'formal/lean' / name).read_bytes())
python = hashlib.sha256((platform + sys.version).encode())
python.update((root / 'scripts/requirements-content.txt').read_bytes())
print(platform + '-' + pins.hexdigest()[:24], python.hexdigest()[:24])
PY
) || return
read -r SEXTICS_CLOUD_DEPS_KEY _sextics_cloud_venv_key <<< "$_sextics_cloud_keys"
export SEXTICS_CLOUD_DEPS_KEY
export SEXTICS_CLOUD_PACKAGES="$SEXTICS_CLOUD_HOME/lake/$SEXTICS_CLOUD_DEPS_KEY/packages"
export SEXTICS_CLOUD_VENV="$SEXTICS_CLOUD_HOME/venvs/$_sextics_cloud_venv_key"
export VIRTUAL_ENV="$SEXTICS_CLOUD_VENV"
export PATH="$SEXTICS_CLOUD_VENV/bin:$SEXTICS_CLOUD_NODE_HOME/bin:$ELAN_HOME/bin:$PATH"
unset _sextics_cloud_repo _sextics_cloud_platform _sextics_cloud_keys _sextics_cloud_venv_key
