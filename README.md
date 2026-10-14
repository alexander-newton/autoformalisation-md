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
| **Riley–Zeckhauser (1983)**: posted prices optimal for any continuous density | `Ironing.lean` | `Ironing.exists_postedPrice_optimal`, `revenue_postedPrice` |
| **Myerson (1981)**: optimal auction, n bidders, **any continuous positive prior** (ironing) | `Hull.lean`, `Ironing.lean`, `Auction.lean` | `Auction.exists_optimal_auction`, `ironed_optimal`, `myerson_optimal` |
| Existence of ironings (convex hull in quantile coordinates) | `Hull.lean` | `Ironing.exists_ironed` |
| Uniqueness of the ironing a.e. | `Ironing.lean` | `Ironing.Ironed.ae_eq` |
| **Bulow–Roberts (1989)**: the hull is the concave hull of the revenue curve | `RevenueCurve.lean` | `Ironing.hull_eq_concaveHull`, `fslope_hull_eq_slope` |
| **Doval–Skreta (2022)**: the revelation step behind canonical mechanisms | `DovalSkreta.lean` | `Play.canonical_IC`, `canonical_outcome_eq`, `canonical_posterior`, `canonical_bayesPlausible` |
| Lagrangian strong duality over a compact convex set | `Duality.lean` | `Duality.strong_duality` |
| **Persuasion LP duality with state prices** (after Kolotilin 2018; Dworczak–Kolotilin) | `Persuasion.lean` | `Persuasion.value_eq_iInf_DK`, `value_eq_iInf`, `dk_weak`, `price_isDKPrice` |

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
* **One buyer, any continuous density (Riley–Zeckhauser).** Each tail ∫ₚᵇ J is the revenue
  p(1 − F(p)) of the posted price p (`revenue_postedPrice`). So some posted price beats every
  IC, IR mechanism (`exists_postedPrice_optimal`), with no regularity assumption.
* **n bidders (Myerson §6).** A score φ̄ *irons* the virtual value when:
  * φ̄ is monotone;
  * the gap D(p) = ∫ₐᵖ (J − φ̄ f) is ≥ 0 and vanishes at b;
  * φ̄ is flat wherever D > 0 (`Ironed`).

  For any monotone allocation Q with values in [0, 1], the gap term ∫ Q (J − φ̄ f) is ≤ 0
  (`gapTerm_nonpos`). It is
  exactly 0 when the allocation depends on the type only through φ̄ (`gapTerm_eq_zero`):
  a threshold never lies inside an ironing interval.
* **The ironed auction is optimal** (`ironed_optimal`). The highest nonnegative ironed virtual
  value wins, at the threshold price. The regular case is a corollary (`myerson_optimal`),
  since a monotone virtual value irons itself with zero gap (`ironed_virtualValue`).
* **Every density admits an ironing** (`exists_ironed`). Measure types by their quantile F
  and call a function *F-convex* if it is convex in that coordinate.
  * The ironed revenue curve Ĝ is the largest F-convex function below G(p) = ∫ₐᵖ J, and φ̄
    is its right F-slope on [a, b) (`ironedValue_ironed`).
  * φ̄ is monotone and bounded (three-chord lemma), and Ĝ(p) = ∫ₐᵖ φ̄ f by a weighted
    version of the `Supports` lemma (`FSupports.sub_eq`).
  * Where Ĝ < G, a short chord still lies below G, so maximality forces Ĝ to be that chord,
    and φ̄ is flat there (`HullSetting.flat`).
* **The ironing is unique a.e.** (`Ironed.ae_eq`). Two ironings φ, ψ of the same continuous
  positive density agree a.e. on [a, b]. The gap integrands differ by (φ − ψ) f, so
  ∫ (φ − ψ)² f is a sum of four gap terms: two vanish by complementary slackness, two are ≤ 0
  by the ironing bound (a bounded monotone score is a rescaled allocation).
* **It is the textbook ironing** (`hull_eq_concaveHull`). Selling with probability q takes the
  price P(q) = F⁻¹(1 − q) and earns R(q) = q P(q). Since G(p) = a − R(1 − F(p)), the type-space
  hull is Ĝ(p) = a − R̄(1 − F(p)), where R̄ is the least concave majorant of R on [0, 1]. Every
  chord slope of Ĝ in quantile coordinates is a chord slope of R̄ (`fslope_hull_eq_slope`). In
  this chord sense, the ironed virtual value is marginal ironed revenue.
* **Myerson's optimal auction exists for every continuous positive prior**
  (`exists_optimal_auction`): no regularity assumption and no assumed ironing.

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
* **On-path posteriors are beliefs** (`post_isDist`): every outcome with positive total
  probability induces a probability vector. An outcome reached only by zero-prior types
  induces the junk "belief" 0; a full-support prior rules this out.

### Persuasion as a linear program
With finitely many states and actions, Bayesian persuasion is a linear program over obedient
recommendation schemes. Its Lagrangian dual, with obedience multipliers y ≥ 0, prices each
state at p_y(θ) = max_a [v(a,θ) + Σ_{a'} y(a,a')(w(a,θ) − w(a',θ))].
* **Duality.** We prove weak duality, existence of an optimal scheme, and no duality gap:
  value = inf_{y≥0} Σ μ(θ) p_y(θ) (`value_eq_iInf`).
* **The persuasion duality, finite case** (`value_eq_iInf_DK`). A Dworczak–Kolotilin price p
  satisfies Σ ν(θ) p(θ) ≥ Σ ν(θ) v(a,θ) for every belief ν and every receiver-optimal action
  a at ν. The value of persuasion equals the least expected cost of such a price.
  * Every DK price bounds the value (`dk_weak`).
  * The state prices p_y are DK prices (`price_isDKPrice`), and they close the gap.
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
* **The ironing is built in type space.** `exists_ironed` builds the hull directly in type
  space, with convexity measured by the quantile F. Its equivalence with the concave hull of
  the revenue curve is proved for the hull itself and its chord slopes (`hull_eq_concaveHull`,
  `fslope_hull_eq_slope`); the ironed value as a one-sided derivative of R̄ is not stated
  separately. Uniqueness (`Ironed.ae_eq`) is a.e. on [a, b] and needs a positive density.
  `Ironed` asks for a bounded measurable φ̄, not a continuous one: the proofs never use
  continuity.
* **Densities must be positive on the closed interval.** A density vanishing at an endpoint
  (e.g. Beta(2,2)) is excluded: there the virtual value is unbounded, and `Ironed` asks for a
  bounded φ̄.
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
* The multi-period Doval–Skreta model (sequential rationality under limited commitment) and the
  Coasian dynamics.
* Continuous-state persuasion duality (Dworczak–Kolotilin), using convex price functions.
