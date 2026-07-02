# Verification CI — placement guide

These files make the website's **Verify** button reflect a *real* GitHub Actions run
rather than a hardcoded claim. Nothing here needs a build to be useful locally: the
seed `verification.json` is produced by running `verify.sh` on this machine, and CI
overwrites it (adding the `build` + `axioms` checks) on every run.

## Files

| staged here | move to (publish repo) | what it is |
|---|---|---|
| `ci/verify.sh`  | `ci/verify.sh`                  | the checks (chips, sorry, build, axioms); runs in CI **and** locally |
| `ci/Audit.lean` | `ci/Audit.lean`                 | `#print axioms` of the headline theorem of every level |
| `ci/verify.yml` | `.github/workflows/verify.yml`  | dispatchable workflow that runs `verify.sh` and commits the result |
| `website/verification.json` | `docs/verification.json` | the result the button reads (same-origin fetch) |
| `website/verify.js`         | `docs/verify.js`         | button + panel logic |

## One thing to set

The button composes the badge / run / dispatch URLs from the repo slug. In CI this
is filled automatically from `$GITHUB_REPOSITORY`. For the *seed* file (before the
first CI run) set the fallback once, at the top of `docs/verify.js`:

```js
const REPO = "OWNER/REPO";   // e.g. "Zetetic-Dhruv/world-model-specification"
```

## Layout assumption

`verify.sh` auto-detects the site (`docs/index.html`) and the corpus (any dir named
`WMSpec` or `TLT_Proofs`, excluding `.lake`). `Audit.lean` assumes a single package
whose Lean source roots include **both** `WMSpec/` and `TLT_Proofs/`. If your
lakefile splits them, run the audit once per package with the matching imports; the
chip + sorry checks are layout-independent.

## What each check means

- **chips** — every `<code>` handle in a `.handles` block on the site resolves to a
  real `theorem`/`def` in the corpus. Catches drift between the page and the proofs.
- **sorry** — no `sorry` / `admit` / `native_decide` in any cited module (CI also
  enforces this from the build log, which is authoritative).
- **build** — `lake build` compiles the corpus clean.
- **axioms** — the headline theorems depend only on `propext`, `Classical.choice`,
  `Quot.sound` (several use none), and never on `sorryAx`.

## Dispatch

The workflow has `workflow_dispatch`, so a maintainer can trigger a fresh run from
the Actions tab ("Run workflow"). The button's **Run verification →** link points
there. Anonymous visitors can't dispatch (that needs `actions:write` auth) — they
see the latest committed result plus the live status badge, which updates itself.
