# World-Model Theory

**Noumenal Research** · a specification theory of world models, machine-checked in Lean 4.

**Live site → https://noumenal-ai.github.io/world-model-theory**

A representation is a world model only when the mathematics says it is. Declare what a latent is
*for* — a target family, a readout budget, and a dynamics law — and the theory determines which
distinctions the latent must keep, which transitions can descend to it, and which representation is
forced. The site develops the theory across eight arguments, from the readout characterization to a
scoped conclusion for JEPA-class systems; every claim on it is a theorem in Lean 4.

## Layout

| path | what |
|---|---|
| `docs/` | the site (GitHub Pages) — the primary artifact |
| `docs/paper/` | the V1 theory paper (PDF) |
| `WMSpec/`, `TLT_Proofs/` | the Lean source of every theorem cited on the site |
| `ci/` | the verification script, axiom audit, and workflow |

## Verification

The site's **Verify** button reads [`docs/verification.json`](docs/verification.json), refreshed by
the `verify` workflow on every dispatch. It checks — literally, in CI — that:

- every theorem handle printed on the site resolves to a real declaration in the source here, and
- none of the cited modules contain `sorry`, `admit`, or `native_decide`.

The full `lake build` and the `#print axioms` audit ([`ci/Audit.lean`](ci/Audit.lean)) run in the
canonical monorepo, against a pinned Mathlib with PhysLean and TorchLean. The corpus is axiom-clean:
the headline theorems depend only on `propext`, `Classical.choice`, and `Quot.sound` (several use
none), and never on `sorryAx`.

To run the source-level checks locally:

```bash
ci/verify.sh          # writes docs/verification.json; exits non-zero if any handle fails to resolve
```

## Note on the source

`WMSpec/` and `TLT_Proofs/` carry the source of the cited theorems for reading and chip-level
verification. Building them requires the full dependency graph (Mathlib · PhysLean · TorchLean),
which lives in the canonical monorepo; this repository is the public specification and its witnesses.

## License

Apache 2.0 — see [LICENSE](LICENSE).
