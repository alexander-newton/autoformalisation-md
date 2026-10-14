# MechDesign — a small, machine-checked mechanism-design library in Lean 4

A compact Lean 4 / Mathlib formalisation of core results in mechanism and information
design. Every theorem listed below is fully proved: there is no `sorry`, and `#print axioms` shows only
Lean's standard `propext`, `Classical.choice` and `Quot.sound`.

| Benchmark | File | Main statements |
|---|---|---|
| **Myerson (1981)**: Myerson's lemma | `MechDesign/Myerson.lean` | `Myerson.Mech.IC_iff`, `Mech.IC.envelope`, `Mech.IC.monotoneOn` |
| Revenue equivalence | `MechDesign/Myerson.lean` | `Myerson.Mech.revenue_equivalence` |
| Revenue = virtual surplus | `MechDesign/Myerson.lean` | `Myerson.revenue_eq_virtualSurplus` |
| Optimal mechanism (posted price under regularity) | `MechDesign/Myerson.lean` | `Myerson.revenue_le`, `Myerson.postedPrice_optimal` |
| **Doval–Skreta (2022)**: canonical mechanisms (beliefs as output messages) | `MechDesign/DovalSkreta.lean` | `canonical_IC`, `canonical_outcome_eq`, `canonical_posterior`, `canonical_bayesPlausible` |
| Lagrangian strong duality (compact domain) | `MechDesign/Duality.lean` | `Duality.strong_duality` |
| **Kolotilin (2018) / Dworczak–Kolotilin**: persuasion duality | `MechDesign/Persuasion.lean` | `Persuasion.weak_duality`, `exists_optimal`, `strong_duality` |

## What is formalised

### Myerson
A single buyer has a value θ ∈ [a, b] and quasilinear utility θq − t.
* **Myerson's lemma.** A direct mechanism (q, t) is incentive compatible iff q is nondecreasing
  and U(θ) = U(a) + ∫ₐ^θ q. We prove the envelope formula from scratch with a Riemann-sum
  squeeze argument, which needs no differentiability assumptions.
* **Revenue equivalence.** This follows as a corollary.
* **Revenue = virtual surplus.** For a continuous density f with CDF F,
  E[t] = ∫ q·J − U(a), where J(θ) = θf(θ) − (1 − F(θ)) = φ(θ)f(θ). The proof uses
  integration by parts for absolutely continuous functions.
* **Optimal mechanism.** Every IC and IR mechanism earns at most ∫ max(J, 0). If J
  single-crosses zero at p (regularity), the posted price p attains that bound.

### Doval–Skreta
The paper's key step is a revelation principle for limited commitment: it is without loss to
use mechanisms whose input is the agent's type and whose public output is the principal's
**posterior**, and that posterior is self-consistent. We formalise the one-shot core of this
result with finite types, messages and allocations. Take any mechanism, any best-responding
strategy, and any continuation that depends only on the public posterior (this is where
sequential rationality of the uncommitted principal enters). Merging the output messages that
induce the same posterior gives a canonical mechanism with these properties:
* it is incentive compatible;
* it has the same (allocation, posterior) distribution for every type;
* it is self-consistent: output β induces posterior β;
* it is Bayes plausible.

### Persuasion duality (Kolotilin's LP approach)
With finitely many states and actions, Bayesian persuasion is a linear program over obedient
recommendation schemes. Its dual prices each state at
p_y(θ) = max_a [v(a,θ) + Σ_{a'} y(a,a')(w(a,θ) − w(a',θ))].
* We prove weak duality and existence of an optimal scheme.
* We prove strong duality (no gap): value = inf_{y≥0} Σ μ(θ) p_y(θ).
* Strong duality comes from an abstract theorem, `Duality.strong_duality`: there is no duality
  gap for linear programs over compact convex sets. Its proof is a Hahn–Banach separation.

## Building

```
lake exe cache get   # optional: prebuilt Mathlib
lake build
```
Toolchain: Lean `v4.35.0`, Mathlib `v4.35.0`.

## Roadmap
* Multi-bidder Myerson auction (BIC → interim reduction via Fubini).
* Ironing (non-regular distributions).
* The multi-period Doval–Skreta model and the Coasian dynamics.
* Continuous-state persuasion duality (Dworczak–Kolotilin), using convex price functions.
