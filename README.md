# MechDesign — a small, machine-checked mechanism-design library in Lean 4

A compact Lean 4 / Mathlib formalisation of core results in mechanism and information
design. Every theorem listed below is fully proved: there is no `sorry`, and `#print axioms` shows only
Lean's standard `propext`, `Classical.choice` and `Quot.sound`.

| Benchmark | File | Main statements |
|---|---|---|
| **Myerson (1981)**: Myerson's lemma | `MechDesign/Myerson.lean` | `Myerson.Mech.IC_iff`, `Supports.sub_eq`, `Mech.IC.envelope` |
| Revenue equivalence | `MechDesign/Myerson.lean` | `Myerson.Mech.revenue_equivalence` |
| Revenue = virtual surplus | `MechDesign/Myerson.lean` | `Myerson.revenue_eq_virtualSurplus` |
| Optimal mechanism (posted price under regularity) | `MechDesign/Myerson.lean` | `Myerson.revenue_le`, `Myerson.postedPrice_optimal` |
| **Myerson (1981)**: optimal auction, n bidders | `MechDesign/Auction.lean` | `Auction.myerson_optimal`, `Mechanism.revenue_eq`, `Mechanism.revenue_le` |
| **Doval–Skreta (2022)**: canonical mechanisms (beliefs as output messages) | `MechDesign/DovalSkreta.lean` | `Play.canonical_IC`, `Play.canonical_outcome_eq`, `Play.canonical_posterior`, `Play.canonical_bayesPlausible` |
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

### Myerson's optimal auction (n bidders)
Bidders have independent types on [a, b] with continuous positive densities, so the joint law
is the product measure. Bidder i's *interim* rule averages its allocation and payment over the
other bidders' types. Each interim rule is a one-bidder mechanism, so the results above apply
bidder by bidder.
* **Resampling** (`map_update`). Redrawing one bidder's type leaves the joint law unchanged.
  This is the only new probabilistic fact the proofs need.
* **Revenue = virtual surplus** (`Mechanism.revenue_eq`).
  E[revenue] = E[Σᵢ qᵢ φᵢ(θᵢ)] − Σᵢ Uᵢ(a).
* **Myerson's bound** (`Mechanism.revenue_le`). A feasible, BIC, interim-IR auction earns at
  most E[max(0, maxᵢ φᵢ(θᵢ))].
* **Optimality** (`myerson_optimal`). Suppose virtual values are nondecreasing (regularity).
  The Myerson auction gives the item to the highest nonnegative virtual value at the threshold
  price, and it attains the bound.
  * The auction is dominant-strategy incentive compatible.
  * A general lemma, "DSIC ⇒ BIC" (`bic_of_dsic`), averages this to Bayesian incentive
    compatibility, so no further Fubini argument is needed.
* **Non-vacuity** (`hasDensity_withDensity`, `isProbabilityMeasure_withDensity`). The density
  hypothesis holds for the measure with density f on [a, b].

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

## Style

The proofs aim to read like a Halmos textbook: name the one concept a proof keeps circling,
prove a few short facts about it, and let each theorem be a short corollary.

* **Myerson.** IC says exactly that `q` *supports* `U`: every chord slope lies between
  `q`'s values at the chord's endpoints. Three facts about supports give Myerson's lemma:
  supporting functions are monotone, a monotone function supports its integral, and two
  functions supported by the same `f` differ by a constant. One integration-by-parts identity
  for primitives gives the revenue formula.
* **Doval–Skreta.** The prior, mechanism and strategy are bundled into a `Play`. The
  canonical mechanism is the image of a play under "relabel each outcome by its posterior".
  IC then follows from two facts about averages: an average lies below any upper bound, and
  an average of maximisers is a maximum.
* **Duality.** One Hahn–Banach separation does the work. The point `(0, OPT + ε)` lies
  above the downward-closed image of the feasible set. Pushing that image downward shows the
  separating functional has the right signs.

## Building

```
lake exe cache get   # optional: prebuilt Mathlib
lake build
```
Toolchain: Lean `v4.35.0`, Mathlib `v4.35.0`.

## Roadmap
* Ironing (non-regular distributions).
* The multi-period Doval–Skreta model and the Coasian dynamics.
* Continuous-state persuasion duality (Dworczak–Kolotilin), using convex price functions.
