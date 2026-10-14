# MechDesign — a small, machine-checked mechanism-design library in Lean 4

A compact Lean 4 / Mathlib formalisation of core results in mechanism and information
design. Every theorem listed below is fully proved: there is no `sorry`, and `#print axioms`
shows only Lean's standard `propext`, `Classical.choice` and `Quot.sound`. The statements have
been red-teamed against their natural-language descriptions. Where a formal statement is a
special case of the paper's result, or carries an extra hypothesis, this README says so under
**Scope**.

| Benchmark | File | Main statements |
|---|---|---|
| **Myerson (1981)**: Myerson's lemma, revenue equivalence | `Myerson.lean` | `Myerson.Mech.IC_iff`, `Mech.IC.envelope`, `Mech.revenue_equivalence` |
| Revenue = virtual surplus; posted price optimal under regularity | `Myerson.lean` | `Myerson.revenue_eq_virtualSurplus`, `revenue_le`, `postedPrice_optimal` |
| **Riley–Zeckhauser (1983)**: posted prices optimal for any distribution | `Ironing.lean` | `Ironing.exists_postedPrice_optimal`, `revenue_postedPrice` |
| **Myerson (1981)**: optimal auction, n bidders, with **ironing** | `Ironing.lean`, `Auction.lean` | `Auction.ironed_optimal`, `Auction.myerson_optimal`, `Mechanism.revenue_le` |
| **Doval–Skreta (2022)**: the revelation step behind canonical mechanisms | `DovalSkreta.lean` | `Play.canonical_IC`, `canonical_outcome_eq`, `canonical_posterior`, `canonical_bayesPlausible` |
| Lagrangian strong duality over a compact convex set | `Duality.lean` | `Duality.strong_duality` |
| **Persuasion LP duality with state prices** (after Kolotilin 2018; Dworczak–Kolotilin) | `Persuasion.lean` | `Persuasion.value_eq_iInf`, `strong_duality`, `price_isDKPrice` |

## What is formalised

### Myerson: one buyer
A single buyer has a value θ ∈ [a, b] and quasilinear utility θq − t.
* **Myerson's lemma.** A direct mechanism (q, t) is incentive compatible iff q is nondecreasing
  and U(θ) = U(a) + ∫ₐ^θ q.
* **Revenue equivalence.** This follows as a corollary.
* **Revenue = virtual surplus.** For a continuous f with ∫ₐᵇ f = 1 and CDF F, revenue equals
  ∫ q·J − U(a), where J(θ) = θf(θ) − (1 − F(θ)) = φ(θ)f(θ).
* **Myerson's bound.** Every IC, IR mechanism with allocation probabilities in [0, 1] earns at
  most ∫ max(J, 0). If J single-crosses zero at p, the posted price p attains that bound.

### Ironing
* **The key identity.** A nondecreasing allocation Q : [a, b] → [0, 1] is an *average of
  threshold rules*: ∫ₐᵇ Q g = ∫₀¹ (∫ from p(s) to b of g) ds (`integral_mul_eq_threshold`).
* **One buyer, any distribution (Riley–Zeckhauser).** Each tail ∫ₚᵇ J is the revenue
  p(1 − F(p)) of the posted price p (`revenue_postedPrice`). So some posted price beats every
  IC, IR mechanism (`exists_postedPrice_optimal`), with no regularity assumption.
* **n bidders (Myerson §6).** A score φ̄ *irons* the virtual value when:
  * φ̄ is monotone;
  * the gap D(p) = ∫ₐᵖ (J − φ̄ f) is ≥ 0 and vanishes at b;
  * φ̄ is flat wherever D > 0 (`Ironed`).

  For any monotone allocation the gap term ∫ Q (J − φ̄ f) is ≤ 0 (`gapTerm_nonpos`). It is
  exactly 0 when the allocation depends on the type only through φ̄ (`gapTerm_eq_zero`):
  a threshold never lies inside an ironing interval.
* **The ironed auction is optimal** (`ironed_optimal`). The highest nonnegative ironed virtual
  value wins, at the threshold price. The regular case is a corollary (`myerson_optimal`),
  since a monotone virtual value irons itself with zero gap (`ironed_virtualValue`).

### Myerson's auction: the n-bidder machinery
* **Interim rules.** Bidder i's *interim* rule averages its allocation and payment over the
  other bidders' types, so each interim rule is a one-buyer mechanism.
* **Resampling** (`map_update`). Redrawing one bidder's type leaves the product law unchanged.
* **Revenue against any score** (`revenue_eq_score`).
  E[revenue] = E[Σᵢ qᵢ hᵢ(θᵢ)] + Σᵢ ∫ₐᵇ Qᵢ(Jᵢ − hᵢ fᵢ) − Σᵢ Uᵢ(a).
* **DSIC ⇒ BIC** (`bic_of_dsic`). A highest-score auction with monotone scores is
  dominant-strategy IC slice by slice; averaging gives Bayesian incentive compatibility
  (`highestScore_properties`).

### Doval–Skreta
We formalise the **one-shot revelation step** behind Doval–Skreta's canonical mechanisms, with
finite types, messages and allocations.
* **The setting.** Take any mechanism and any best-responding agent strategy. Relabel each
  public outcome by (the principal's posterior, the allocation).
* **The resulting canonical mechanism:**
  * is incentive compatible (`canonical_IC`);
  * gives every type the same distribution of (allocation, posterior), so every player's
    payoff is unchanged (`canonical_outcome_eq`);
  * is self-consistent: announcing β induces posterior β (`canonical_posterior`);
  * is Bayes plausible (`canonical_bayesPlausible`).
* **On-path posteriors are beliefs** (`post_isDist`).

### Persuasion as a linear program
With finitely many states and actions, Bayesian persuasion is a linear program over obedient
recommendation schemes. Its Lagrangian dual, with obedience multipliers y ≥ 0, prices each
state at p_y(θ) = max_a [v(a,θ) + Σ_{a'} y(a,a')(w(a,θ) − w(a',θ))].
* **Duality.** We prove weak duality, existence of an optimal scheme, and no duality gap:
  value = inf_{y≥0} Σ μ(θ) p_y(θ) (`value_eq_iInf`).
* **Link to Dworczak–Kolotilin** (`price_isDKPrice`). Each p_y is a feasible
  Dworczak–Kolotilin price. For every belief ν and every receiver-optimal action a at ν,
  Σ ν(θ) p_y(θ) ≥ Σ ν(θ) v(a,θ).
* **Engine.** Strong duality comes from `Duality.strong_duality`, a Hahn–Banach separation
  for linear programs over compact convex sets.

## Scope (read before citing)
* **Myerson, one buyer.** Allocations must lie in [0, 1]. The density is assumed continuous;
  nonnegativity is not needed by the proofs.
* **Common support.** In the n-bidder results all bidders share the support [a, b]; Myerson
  allows asymmetric supports [aᵢ, bᵢ]. Each density must be continuous on ℝ (any continuous
  density on [a, b] extends) and positive on [a, b].
* **Bounded measurable competitors.** Competing auctions are assumed to have bounded,
  measurable allocations and payments (`Mechanism.BddMeasurable`). Integrable but unbounded
  ex-post payments are excluded.
* **Clamped virtual values.** Virtual values are evaluated at the type clamped into [a, b].
  Types lie in [a, b] almost surely, so this is harmless.
* **Ironing is assumed, not constructed.** `ironed_optimal` takes an ironing φ̄ as a
  hypothesis (`Ironed`). Existence of the ironing, via the convex hull of the revenue curve
  in quantile space, is not yet formalised. In the regular case it is proved
  (`ironed_virtualValue`).
* **Doval–Skreta is the one-shot step only.** Sequential rationality, participation and
  multiple periods are not modelled. Instead, the continuation is assumed to depend on the
  outcome only through (allocation, posterior). In DS, different outcomes with the same
  posterior could select different continuation equilibria. This relabelling step also holds
  under full commitment.
* **Persuasion is the finite case.** It is finite states and actions, not Kolotilin's
  continuous-state model. The dual infimum is shown to equal the value but is not shown to be
  attained.

## Style
The proofs aim to read like a Halmos textbook: name the one concept a proof keeps circling,
prove a few short facts about it, and let each theorem be a short corollary. See `CLAUDE.md`.
* **Myerson.** IC says exactly that `q` *supports* `U`: every chord slope lies between `q`'s
  values at the chord's endpoints.
* **Ironing.** A monotone allocation is an average of thresholds. With that, Riley–Zeckhauser
  and the ironing bound are each one line, and complementary slackness says a threshold never
  lies inside an ironing interval.
* **Doval–Skreta.** The canonical mechanism is the image of a play under "relabel each outcome
  by its posterior". IC then follows from two facts about averages.
* **Duality.** One Hahn–Banach separation. The separating functional's signs come from pushing
  the image of the feasible set downward.

## Building
```
lake exe cache get   # optional: prebuilt Mathlib
lake build
```
Toolchain: Lean `v4.35.0`, Mathlib `v4.35.0`.

## Roadmap
* Existence of ironings: the convex hull of the revenue curve.
* The multi-period Doval–Skreta model and the Coasian dynamics.
* Continuous-state persuasion duality (Dworczak–Kolotilin), using convex price functions.
