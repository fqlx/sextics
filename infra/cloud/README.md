# Cloud development setup

From the Linux cloud checkout root, run:

```sh
bash scripts/cloud/setup.sh
source scripts/cloud/env.sh
bash scripts/cloud/check-github.sh
bash scripts/cloud/verify.sh
```

Setup needs Bash and Python 3.11 or `uv` to install it. Missing system tools,
including `gh`, are installed with apt (root or passwordless sudo is required).
It installs the pinned content requirements in a virtual environment, Node and
the locked server dependencies, elan, the pinned Lean toolchain, and compiled
mathlib dependencies. No service needs to run. Source `env.sh` in **each new
shell** to put Python, Node, and `lake` on `PATH`; an install subprocess cannot
export its environment into a later agent shell.

Lean stays at `leanprover/lean4:v4.33.0`; mathlib stays at
`db584cd6d46c92f209a44c0f1c829460d327499d`. The committed Lake manifest fixes
transitive dependencies. Setup checks declarations and fetched revisions and
never runs `lake update`.

## Persistent development cache

`SEXTICS_CLOUD_HOME` defaults to `/workspace/tooling/sextics`. Preserve that
directory in the cloud environment's saved workspace/cache, outside Git. It holds
toolchains, Python environments, npm/pip downloads, `MATHLIB_CACHE_DIR` archives,
and dependency checkouts with their compiled artifacts. The dependency key
includes the platform and committed Lean/Lake configuration. The checkout's
`formal/lean/.lake/packages` links to this cache; project `.lake/build` stays
local to the checkout. Proposal artifacts never become trusted dependency cache.

Repeating setup reuses these installations. A second clean checkout can reuse
the dependencies while compiling its own project sources. Use separate cache
roots for concurrent jobs or users: writable development caches are not a trust
boundary for hostile submissions. Do not commit `.olean`, `.ilean`, `.ltar`,
toolchains, virtual environments, or `node_modules`.

Set the environment install script to `bash scripts/cloud/setup.sh` from the
repository root. Startup instructions should source `scripts/cloud/env.sh`, read
`AGENTS.md`, `CONTRIBUTING.md`, and `formal/lean/README.md`, and report readiness.
After configuration changes, save the reviewed draft, refresh setup, run the
checks, and publish/capture the tested workspace cache. Verify a new task inherits
both executable paths and compiled dependencies. A saved draft does not establish
that the running sidecar uses its rules.

## Proxy access

Retain the inherited `HTTP_PROXY`, `HTTPS_PROXY`, and CA trust. Keep TLS
verification. This environment uses **All (unrestricted)** domains, as selected
by its owner, so a package-host whitelist does not need ongoing maintenance.
This setting belongs in Codex Cloud settings and does not change repository
approval rules. For diagnosing destination failures, Lean uses hosts
`releases.lean-lang.org` and `lakecache.blob.core.windows.net`; `gh` needs
`api.github.com` separately from Git's `github.com` transport. Retain existing
package destinations for Python, Node/npm, GitHub, and release asset redirects.
Use the supported environment configuration workflow to apply network policy.
Editing `/etc/codex/network-policy.json` cannot grant access.

Probe a real object from the pinned cache through the normal proxy:

```sh
curl --fail --show-error --location \
  https://lakecache.blob.core.windows.net/mathlib4-master/f/a852990c44e679fd.ltar \
  --output /tmp/sextics-Mathlib.Init.ltar
```

For this mathlib pin, `lake exe cache lookup Mathlib.Init` identifies this object.
Its successful GET returns HTTP 200 and 11,210 bytes; the legacy `mathlib4`
container returns 404 for that hash. A bare host/container-root probe is
insufficient. Complete `lake exe cache get` too; existing cached files can conceal
broken networking.

For an allowlisted URL returning 403, record its URL/status and non-secret
`Server`, `x-ms-error-code`, and `x-ms-request-id` response fields. Distinguish a
proxy CONNECT/destination denial from an Azure storage rejection. Check live
policy/readiness against the saved draft and refresh the runtime after applying
the settings. Do not unset the proxy or disable TLS. Stop on cache failure
instead of starting a full mathlib source build.
Keep tokens and request authorization headers out of logs.

## GitHub identity and push

`check-github.sh` requires API identity `fqlx` and push permission on
`fqlx/sextics`. Its `--repair-stored-account` option only selects an existing,
authenticated `fqlx` account. Environment tokens take precedence over stored
accounts. Test managed credential placeholders through the configured proxy;
their appearance, or `gh auth status` during a destination denial, cannot prove
they are invalid. Repair a missing or wrongly scoped binding through the
runtime's supported credential settings, then rerun the API check.

Keep working Git push authentication. Do not run `gh auth setup-git`, replace Git
credential helpers, or copy credentials into source, chat, or published caches.
Verify a real branch push separately, choosing the intended maintenance branch:

```sh
git push https://github.com/fqlx/sextics.git HEAD:refs/heads/fqlx/cloud-setup
git ls-remote https://github.com/fqlx/sextics.git refs/heads/fqlx/cloud-setup
```

## Clean-checkout verification and review

Fetch a reviewed commit into a separate clean checkout. Run setup twice, source
`env.sh` in a fresh shell, and run `verify.sh`. Record the commit, toolchain and
dependency revisions, actual artifact GET, default build result, replayed module
count, content results, API identity, and remote branch SHA. Content generation
must reproduce tracked files without drift.

`verify.sh` runs the literal default `lake build` for both configured libraries,
then sequential `leanchecker` replay of built project modules, content checks,
and regression tests. The default targets cover their import closure, rather
than every optional construction source. `--all-modules` additionally selects
all shared sources. `--with-sandbox-tests` exercises the proposal verifier;
Linux requires Docker and a non-root user, and macOS requires `sandbox-exec`.

These are development checks. Protected proposal verification still compiles
candidate proofs in an OS sandbox and audits the exact theorem and axioms.
[CONTRIBUTING.md](../../CONTRIBUTING.md) and
[MAINTAINING.md](../../MAINTAINING.md) remain authoritative. Infrastructure goes
in a separate maintenance PR. This cloud environment is maintained in
`fqlx/sextics`, so fork setup changes target that fork's `main`. Contributions
to `hodge-computer/sextics` separately follow its exact-head owner authorization
and manual merge rules. Setup and local replay do not establish solve acceptance.
