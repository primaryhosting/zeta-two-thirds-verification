# Independent audit — `anthropics/zeta-23-lean`

Auditor: run on the cloned repo at HEAD, 2026-08-10. Independent of the repo's own `AUDIT.md`
(claims re-checked against the actual sources, not taken on trust).

## Result under audit
"More than two thirds of the zeros of ζ lie on the critical line" (author: Claude/Anthropic).
Formal claim: `liminf_{T→∞} N₀*(T,2T) / N(T,2T) ≥ 2/3`, unconditionally, against Mathlib's `riemannZeta`.
**This is a proportion-on-the-line result, NOT a proof of RH** (the paper is explicit; §1.5).

## What I checked WITHOUT a build (complete)

| Check | Method | Result |
|---|---|---|
| Toolchain matches paper | `lean-toolchain`, `lakefile.toml` | ✓ Lean 4.33.0-rc2, Mathlib `51e6992` |
| Real formalization, not a stub | file tree | ✓ ~300 files: WeilEF, RvM, LinAlg, PrimeSide, XiPrime, ThmD/E |
| `sorry`/`admit`/`native_decide` | repo-wide grep | ✓ only in `comparator/Challenge*` (deliberate statement placeholders); **none under `Zeta23/`, none in `Solution`** |
| Stray `axiom` declarations | grep + read context | ✓ the two `axiom` lines in `FromPNTPlus/Tactic/AdditiveCombination.lean` are **inside a `/- … -/` doc-comment** (upstream PNT+ tactic examples) — they declare nothing |
| **Statement faithfulness** | read `comparator/ChallengeDeps.lean` + `Challenge.lean` | ✓ see below — the theorems mean what the paper claims |

### Faithfulness detail (the part no kernel can certify for you)
- `IsNontrivialZero ρ := riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1` — Mathlib's **actual** `riemannZeta`, open critical strip.
- `zeroMult ρ := (analyticOrderAt riemannZeta ρ).toNat` — multiplicity via Mathlib; `.toNat` sends ⊤→0 so `1 ≤ zeroMult` = genuine finite-order zero. Careful and correct.
- `N0star := (zerosIn ∩ {ρ.re = 1/2}).ncard` — distinct zeros **on Re s = ½**.
- Theorem A: `∀ ε>0, ∃ T₀, ∀ T ≥ T₀, (2/3 − ε)·Ncount T (2T) ≤ N0star T (2T)`.
  - **Strong direction:** denominator `Ncount` counts **with multiplicity**; numerator `N0star` counts **distinct on-line**. Not a weakened restatement.
  - No hidden hypotheses on the ζ theorems (A–D). Theorem E correctly carries `1 < q` and `χ.IsPrimitive`.
- Constants faithful: B = 1/2 simple, C = 3/4 distinct, D = Montgomery–Taylor `cMT` in closed form.

**Verdict on the checkable part: PASS.** The formalization is genuine, `sorry`-free in the library,
free of stray axioms, and the theorem statements faithfully express "≥ 2/3 of ζ's nontrivial zeros
(distinct, on the line) vs all zeros with multiplicity," against Mathlib's real ζ.

## What the repo's own audit documents (strong, but I have NOT yet re-run)
- `lake build`: 9010 jobs, no errors, no `sorry` warnings.
- `#print axioms` on all 27+6 headline theorems = `[propext, Classical.choice, Quot.sound]` — Lean's
  three standard axioms only; no `sorryAx`, no project axiom.
- `leanprover/comparator` run (statement-equality + axiom audit + **independent `nanoda` kernel replay**):
  "Your solution is okay!" on all three configs. This is a gold-standard architecture — trust base is
  just Mathlib's defs + two ~60-line files + the kernel(s).

## Remaining for FULL independent confirmation — DISK-GATED
To reproduce the above myself (not trust the record):
```
lake exe cache get            # ~5–7 GB Mathlib .olean cache for the pinned commit
lake build Solution && lake env lean comparator/PrintAxioms.lean
lake build Zeta23.LinAlg.RankTrace   # the self-contained §3 core, independently
```
**Blocker:** only 9.9 GiB free (disk 95% full). The cache alone risks filling it. Options: free space
first, or accept the documented comparator+nanoda run as the independent-kernel evidence (it already
uses a second kernel).

## "Build off it" — the honest, bounded surface
- The **§3 LinAlg cone is Mathlib-only** (self-contained): `PosIndex, VonNeumann, Sylvester,
  HermitianPosPart, Inertia, RankTrace, Weyl`. This is the layer our fleet can independently
  re-derive/verify. It caps at ~0.68 without new analysis (paper Remark 1.1), so it's
  verification/understanding, not frontier advance.
- Extending the 2/3 theorem itself needs pair-correlation beyond what's known — not in fleet reach.
