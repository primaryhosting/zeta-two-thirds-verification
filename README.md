# Independent Verification — *More Than Two Thirds of the Zeros of the Riemann Zeta Function Lie on the Critical Line*

[![Verification](https://img.shields.io/badge/independent%20replication-passing-3fb950)](https://github.com/primaryhosting/zeta-23-lean/actions/runs/31458241556)
[![Kernels](https://img.shields.io/badge/kernels-Lean%20%2B%20nanoda-ffd54a)](#the-verification)
[![Axioms](https://img.shields.io/badge/axioms-propext%20·%20Classical.choice%20·%20Quot.sound-8a5fff)](#the-verification)
[![Not RH](https://img.shields.io/badge/scope-proportion%20result%2C%20NOT%20RH-e94560)](#what-this-is--and-is-not)
[![Docs CC BY 4.0](https://img.shields.io/badge/docs-CC%20BY%204.0-blue)](LICENSE)

> **This repository is an independent, third‑party verification of a formal proof — not a new theorem, and not a proof of the Riemann Hypothesis.**
> The theorem and its Lean 4 formalization are the work of **Claude / Anthropic**. Our contribution, by **Riemann Labs (primaryhosting)**, is to have rebuilt that formalization from scratch, in our own CI, and put it through the community verifier under **two independent proof kernels**. As far as we are aware, this is the first independent third‑party replication.

---

## The result being verified

In August 2026, an unreleased research version of **Claude (Anthropic)** improved the proven lower bound for the fraction of nontrivial zeros of the Riemann zeta function that lie on the critical line — from **41.6 %** (the record since 2020) to **67.2 %**, a little over two thirds. It is a **proportion result**. Anthropic states plainly that *“we don’t expect that the techniques Claude used will lead to proving the Riemann hypothesis.”*

The headline Lean statement (against Mathlib’s own `riemannZeta`) is:

```lean
theorem two_thirds_on_critical_line :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (2 / 3 - ε) * (Ncount T (2 * T) : ℝ) ≤ N0star T (2 * T)
```

i.e. `liminf_{T→∞} N₀*(T,2T) / N(T,2T) ≥ 2/3`, where `N` counts nontrivial zeros **with multiplicity** and `N₀*` counts **distinct** zeros on the line `Re s = 1/2` — the strong direction.

- **Paper (Anthropic):** <https://www.anthropic.com/research/riemann-zeta>
- **Formalization (Anthropic):** <https://github.com/anthropics/zeta-23-lean> · Apache‑2.0

## The verification

Reproduced by us in CI on our fork, **[primaryhosting/zeta-23-lean](https://github.com/primaryhosting/zeta-23-lean)** (branch `replication`), **[run 31458241556](https://github.com/primaryhosting/zeta-23-lean/actions/runs/31458241556)**:

| Check | Result |
|---|---|
| Full rebuild from the pinned toolchain (Lean `v4.33.0-rc2`, Mathlib `51e6992`) | `lake build` — **9,010 jobs, passing** |
| Enforced axiom audit | **42 headline statements**, each depending on only `[propext, Classical.choice, Quot.sound]`; **0 `sorryAx`** |
| Statement‑equality vs the trusted Mathlib‑only Challenge files (`leanprover/comparator`) | **passing**, all three configs |
| **Independent dual‑kernel replay** | each config: *“Nanoda kernel accepts the solution”* **and** *“Lean default kernel accepts the solution”* → *“Your solution is okay!”* |

The full narrative, with quoted CI log lines and the trusted definitions, is in **[VERIFICATION.md](VERIFICATION.md)** ([PDF](docs/independent-replication-report.pdf)); a from‑scratch statement‑faithfulness audit is in **[AUDIT.md](AUDIT.md)**; the exact CI workflow is in **[ci/replicate.yml](ci/replicate.yml)**.

### Reproduce it yourself

```bash
git clone https://github.com/primaryhosting/zeta-23-lean
cd zeta-23-lean && git checkout replication
lake exe cache get          # prebuilt Mathlib for the pinned commit
lake build                  # the full development (≈9,010 jobs)
lake build Solution && lake env lean comparator/PrintAxioms.lean   # axiom audit
# full comparator + dual-kernel replay: see ci/replicate.yml (needs landrun + nanoda)
```

## What this is — and is not

- **Not the Riemann Hypothesis.** It bounds a *proportion*; it says nothing about the remaining third of the zeros.
- **Not our theorem.** The mathematics and the Lean proof are Claude / Anthropic’s. We verified them.
- **Formalization verification ≠ mathematical peer review.** We confirm the Lean proof is sound and states the claimed theorem against Mathlib’s real `riemannZeta`. Peer review of the underlying paper is a separate, ongoing process.
- **Priority claim, hedged.** We are not aware of a prior independent third‑party replication — which is not the same as asserting none exists.

## Contents

| Path | What |
|---|---|
| `VERIFICATION.md` | Independent replication report (with quoted CI evidence) |
| `docs/independent-replication-report.pdf` | The same, typeset |
| `AUDIT.md` | From‑scratch statement‑faithfulness + axiom audit |
| `ci/replicate.yml` | The CI workflow that produced the evidence |
| `lean/independent-rederivation/` | **Our own** AXLE-verified Lean re-derivation of the §3 linear-algebra core (von Neumann, Sylvester, rank–trace) — downloadable, standalone |
| `CITATION.cff` / `CITATION.bib` | How to cite this verification |

> **Note on the paper.** Anthropic’s paper is **not redistributed here** — it is marked *do not distribute* and is only linked. What *is* included and downloadable is (a) our verification reports, and (b) our own independent Lean re-derivation of the method’s §3 core in [`lean/independent-rederivation/`](lean/independent-rederivation/) (Aristotle → AXLE, Lean 4.32.0). The full Anthropic formalization is Apache‑2.0 and lives at [`anthropics/zeta-23-lean`](https://github.com/anthropics/zeta-23-lean) / our [fork](https://github.com/primaryhosting/zeta-23-lean).

## How to cite

If you refer to this independent verification, please cite it via [`CITATION.cff`](CITATION.cff) / [`CITATION.bib`](CITATION.bib), **and** cite the original theorem and formalization by Claude / Anthropic.

## Credits & attribution

- **Theorem & Lean formalization:** Claude (Anthropic). Human collaborators named by Anthropic: **Jarred Sumner** (posed the problem / encouragement), mathematicians **Levent Alpöge** and **Ralph Furman** (validation), **Eric Easley** (formalization); experts **Brian Conrey** and **Dan Goldston** examined the paper. Lean formalization: `anthropics/zeta-23-lean` (Apache‑2.0).
- **Independent verification:** Riemann Labs (primaryhosting).
- **Read our viewpoint:** <https://torus.riemannlab.com/viewpoint>

## License

The verification documents, reports, and scripts in **this** repository are released under **CC BY 4.0** (see [`LICENSE`](LICENSE)). They cite and link — but do **not** redistribute — Anthropic’s paper; the referenced Lean formalization is Apache‑2.0 and lives in its own repositories.
