#!/usr/bin/env bash
# Check API authentication independently of Git's push credential path.
set -euo pipefail

script_dir=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)

repair=false
repository=fqlx/sextics
while (($#)); do
  case "$1" in
    --repair-stored-account) repair=true ;;
    --help|-h)
      cat <<'USAGE'
Usage: scripts/cloud/check-github.sh [--repair-stored-account] [owner/repository]

Require the GitHub API identity fqlx and push permission to fqlx/sextics
(or the given repository). With --repair-stored-account, switch only gh's
active account to an already authenticated fqlx account. Environment tokens
must be repaired in the runtime's credential settings; they are never unset.
Git credential configuration and remotes are never changed. This is not a
branch push test. Account switching is refused when Git uses gh credentials.
USAGE
      exit 0 ;;
    -*) printf 'Unknown option: %s\n' "$1" >&2; exit 2 ;;
    *) repository=$1 ;;
  esac
  shift
done
if [[ ! "$repository" =~ ^[A-Za-z0-9_.-]+/[A-Za-z0-9_.-]+$ ]]; then
  printf 'Expected owner/repository, received: %s\n' "$repository" >&2
  exit 2
fi
if ! command -v gh >/dev/null; then
  printf 'gh is missing; run scripts/cloud/setup.sh first.\n' >&2
  exit 1
fi

# Avoid inherited HTTP debug logging, which can expose credentials. Never
# print tokens, auth config files, or raw API diagnostics.
export GH_DEBUG= DEBUG= GH_PROMPT_DISABLED=1 GH_NO_UPDATE_NOTIFIER=1
environment_token=false
if [[ -n "${GH_TOKEN:-}" || -n "${GITHUB_TOKEN:-}" ]]; then
  environment_token=true
  printf 'gh uses a runtime environment token (GH_TOKEN takes precedence over GITHUB_TOKEN).\n'
fi

api_login() {
  gh api --hostname github.com user --jq .login 2>/dev/null
}
login=$(api_login) || login=
if [[ "$login" != fqlx ]] && "$repair"; then
  if "$environment_token"; then
    printf 'Cannot switch an environment-token identity. Configure a valid fqlx API credential in the cloud runtime, then retry.\n' >&2
    exit 1
  fi
  # gh's JSON is filtered before output and never includes the token. The
  # command's JSON exit status alone does not prove successful authentication.
  stored=$(gh auth status --hostname github.com --json hosts \
    --jq '.hosts["github.com"][] | select(.login == "fqlx" and .state == "success") | .login' \
    2>/dev/null) || stored=
  if [[ "$stored" != fqlx ]]; then
    printf 'No valid stored fqlx account is available. Configure the cloud runtime API credential or authenticate gh as fqlx, then retry.\n' >&2
    exit 1
  fi
  # gh can also serve as Git's credential helper. In that case switching its
  # active account could change working Git authentication without any Git
  # configuration edit. Leave that coupled setup for explicit runtime repair.
  if git -C "$script_dir/../.." config --get-regexp '^credential(\..*)?\.helper$' \
      2>/dev/null | grep -Eq 'gh[[:space:]].*auth[[:space:]]+git-credential'; then
    printf 'Git uses gh as a credential helper; switching accounts could change working push authentication. Repair the runtime API credential separately.\n' >&2
    exit 1
  fi
  if ! gh auth switch --hostname github.com --user fqlx >/dev/null 2>&1; then
    printf 'gh could not switch to its stored fqlx account. Git credential configuration was not changed.\n' >&2
    exit 1
  fi
  login=$(api_login) || login=
fi

if [[ -z "$login" ]]; then
  printf 'GitHub API authentication failed. Check runtime API credentials and api.github.com proxy access; working Git push authentication does not authenticate gh.\n' >&2
  exit 1
fi
if [[ "$login" != fqlx ]]; then
  printf 'GitHub API identity is %s; expected fqlx.\n' "$login" >&2
  if "$environment_token"; then
    printf 'Repair the runtime API credential; stored gh accounts cannot override an environment token.\n' >&2
  else
    printf 'Retry with --repair-stored-account to select an existing authenticated fqlx account.\n' >&2
  fi
  exit 1
fi

permission=$(gh api --hostname github.com "repos/$repository" --jq '.permissions.push == true' 2>/dev/null) || permission=
if [[ "$permission" != true ]]; then
  printf 'Authenticated as fqlx, but GitHub API push permission to %s was not confirmed. Check repository access and token permissions.\n' "$repository" >&2
  exit 1
fi
printf 'GitHub API identity fqlx and push permission to %s verified. Git credential configuration was not changed; verify a branch push separately.\n' "$repository"
