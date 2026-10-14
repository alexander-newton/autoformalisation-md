/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Data.Real.Basic

/-!
# Doval–Skreta: canonical mechanisms with beliefs as output messages

Doval & Skreta (*Mechanism Design with Limited Commitment*, Econometrica 2022) show that when
the principal cannot commit to future mechanisms, it is without loss to use *canonical*
mechanisms: the agent reports her type (input messages = types) and the mechanism publicly
outputs the principal's **posterior belief** (output messages = beliefs), which is then
*self-consistent*: the posterior induced by output `β` is `β` itself.

The engine is a one-shot statement: whatever happens after the mechanism (the principal's
sequentially rational continuation, future mechanisms, ...) affects payoffs only through the
public allocation `x` and the principal's posterior `β`.  We formalise exactly this: take any
mechanism `ζ : M → Δ(S × X)` with a best-responding agent strategy `σ : Θ → Δ(M)`, and any
continuation utility `u θ x β` that depends on the public posterior. Then the canonical
mechanism `ζc : Θ → Δ(Δ(Θ) × X)`, obtained by merging all public outputs that induce the same
posterior,

* is incentive compatible (`canonical_IC`),
* induces the same joint distribution of (allocation, posterior) for each type
  (`canonical_outcome_eq`), hence the same payoffs for every player,
* is self-consistent: the posterior after output `(β, x)` is `β` (`canonical_posterior`),
* is Bayes plausible: posteriors average back to the prior (`canonical_bayesPlausible`).

Distributions are nonnegative real vectors summing to one; posteriors are elements of `Θ → ℝ`.
-/

open Finset

namespace DovalSkreta

variable {Θ M S X : Type*} [Fintype Θ] [Fintype M] [Fintype S] [Fintype X]
  [DecidableEq Θ] [DecidableEq X]

/-- `p` is a probability vector. -/
def IsDist {α : Type*} [Fintype α] (p : α → ℝ) : Prop := (∀ a, 0 ≤ p a) ∧ ∑ a, p a = 1

section Setup

/-- The environment: prior `μ`, mechanism `ζ` (input message ↦ distribution over public
output message × allocation), and agent strategy `σ` (type ↦ distribution over inputs). -/
variable (μ : Θ → ℝ) (ζ : M → S × X → ℝ) (σ : Θ → M → ℝ)

/-- Probability that a type-`θ` agent's play produces public outcome `o`. -/
def outProb (θ : Θ) (o : S × X) : ℝ := ∑ m, σ θ m * ζ m o

/-- Joint probability of type `θ` and public outcome `o`. -/
def joint (θ : Θ) (o : S × X) : ℝ := μ θ * outProb ζ σ θ o

/-- Marginal probability of public outcome `o`. -/
def marg (o : S × X) : ℝ := ∑ θ, joint μ ζ σ θ o

/-- The principal's posterior after observing public outcome `o` (Bayes' rule). -/
noncomputable def post (o : S × X) : Θ → ℝ := fun θ => joint μ ζ σ θ o / marg μ ζ σ o

/-- The canonical relabelling of a public outcome: (posterior it induces, allocation). -/
noncomputable def relabel (o : S × X) : (Θ → ℝ) × X := (post μ ζ σ o, o.2)

/-- The finite set of canonical outputs. -/
noncomputable def outputs : Finset ((Θ → ℝ) × X) :=
  haveI := Classical.decEq (Θ → ℝ); univ.image (relabel μ ζ σ)

open Classical in
/-- **The canonical mechanism**: input = reported type, output = (posterior, allocation).
A report `θ` produces output `b` with the total probability of all original public outcomes
that induce `b`. -/
noncomputable def canonical (θ : Θ) (b : (Θ → ℝ) × X) : ℝ :=
  ∑ o ∈ univ.filter (fun o => relabel μ ζ σ o = b), outProb ζ σ θ o

/-- Change of variables: integrating against the canonical mechanism is integrating against
the original one after relabelling outcomes by the posterior they induce. -/
theorem sum_canonical (θ : Θ) (g : (Θ → ℝ) × X → ℝ) :
    ∑ b ∈ outputs μ ζ σ, canonical μ ζ σ θ b * g b =
      ∑ o, outProb ζ σ θ o * g (relabel μ ζ σ o) := by
  classical
  unfold canonical outputs
  simp_rw [sum_mul]
  rw [← Finset.sum_fiberwise_of_maps_to (s := univ) (t := univ.image (relabel μ ζ σ))
    (g := relabel μ ζ σ) (fun o _ => mem_image_of_mem _ (mem_univ o))]
  refine sum_congr (by congr 1) fun b _ => sum_congr (by ext; simp) fun o ho => ?_
  rw [(mem_filter.1 ho).2]

/-- The agent's expected utility (in the original mechanism) of sending message `m` when her
type is `θ`; continuation payoffs depend on the public posterior. -/
def payoff (u : Θ → X → (Θ → ℝ) → ℝ) (θ : Θ) (m : M) : ℝ :=
  ∑ o, ζ m o * u θ o.2 (post μ ζ σ o)

/-- The agent's expected utility in the canonical mechanism, type `θ` reporting `θ'`. -/
noncomputable def canonicalPayoff (u : Θ → X → (Θ → ℝ) → ℝ) (θ θ' : Θ) : ℝ :=
  ∑ b ∈ outputs μ ζ σ, canonical μ ζ σ θ' b * u θ b.2 b.1

theorem canonicalPayoff_eq (u : Θ → X → (Θ → ℝ) → ℝ) (θ θ' : Θ) :
    canonicalPayoff μ ζ σ u θ θ' = ∑ m, σ θ' m * payoff μ ζ σ u θ m := by
  unfold canonicalPayoff payoff
  rw [sum_canonical μ ζ σ θ' (fun b => u θ b.2 b.1)]
  simp only [outProb, relabel, sum_mul, mul_sum]
  rw [sum_comm]; simp_rw [mul_assoc]

end Setup

variable {μ : Θ → ℝ} {ζ : M → S × X → ℝ} {σ : Θ → M → ℝ}

/-- **Outcome equivalence.** For every type, the canonical mechanism under truth-telling induces
the same expectation of every function of (allocation, posterior) as the original mechanism
under `σ`; in particular all players' payoffs coincide. -/
theorem canonical_outcome_eq (θ : Θ) (g : X → (Θ → ℝ) → ℝ) :
    ∑ b ∈ outputs μ ζ σ, canonical μ ζ σ θ b * g b.2 b.1 =
      ∑ o, outProb ζ σ θ o * g o.2 (post μ ζ σ o) :=
  sum_canonical μ ζ σ θ (fun b => g b.2 b.1)

/-- **Revelation principle with beliefs as outputs (incentive compatibility).**
If `σ` only puts weight on best responses, truth-telling is optimal in the canonical
mechanism. -/
theorem canonical_IC (hσ : ∀ θ, IsDist (σ θ)) (u : Θ → X → (Θ → ℝ) → ℝ)
    (hbr : ∀ θ m, 0 < σ θ m → ∀ m', payoff μ ζ σ u θ m' ≤ payoff μ ζ σ u θ m)
    (θ θ' : Θ) : canonicalPayoff μ ζ σ u θ θ' ≤ canonicalPayoff μ ζ σ u θ θ := by
  rw [canonicalPayoff_eq, canonicalPayoff_eq]
  -- every message is weakly worse than the equilibrium payoff
  have key : ∀ m', payoff μ ζ σ u θ m' ≤ ∑ m, σ θ m * payoff μ ζ σ u θ m := by
    intro m'
    calc payoff μ ζ σ u θ m' = ∑ m, σ θ m * payoff μ ζ σ u θ m' := by
          rw [← sum_mul, (hσ θ).2, one_mul]
      _ ≤ _ := sum_le_sum fun m _ => by
          rcases ((hσ θ).1 m).lt_or_eq with h | h
          · exact mul_le_mul_of_nonneg_left (hbr θ m h m') h.le
          · simp [← h]
  calc ∑ m, σ θ' m * payoff μ ζ σ u θ m
      ≤ ∑ m, σ θ' m * ∑ m, σ θ m * payoff μ ζ σ u θ m :=
        sum_le_sum fun m _ => mul_le_mul_of_nonneg_left (key m) ((hσ θ').1 m)
    _ = _ := by rw [← sum_mul, (hσ θ').2, one_mul]

/-- The canonical mechanism is a well-defined mechanism: each report yields a probability
distribution over canonical outputs. -/
theorem canonical_isDist (hσ : ∀ θ, IsDist (σ θ)) (hζ : ∀ m, IsDist (ζ m)) (θ : Θ) :
    (∀ b, 0 ≤ canonical μ ζ σ θ b) ∧ ∑ b ∈ outputs μ ζ σ, canonical μ ζ σ θ b = 1 := by
  refine ⟨fun b => sum_nonneg fun o _ => sum_nonneg fun m _ =>
    mul_nonneg ((hσ θ).1 m) ((hζ m).1 o), ?_⟩
  have := sum_canonical μ ζ σ θ (fun _ => 1)
  simp only [mul_one] at this
  rw [this, outProb, sum_comm]
  simp [← mul_sum, (hζ _).2, (hσ θ).2]

/-- **Self-consistency of beliefs.** Under truth-telling in the canonical mechanism, the joint
probability of type `θ` and output `b = (β, x)` equals `β θ` times the probability of `b`:
the posterior induced by output `β` is `β` itself. -/
theorem canonical_posterior (hμ : ∀ θ, 0 ≤ μ θ) (hσ : ∀ θ m, 0 ≤ σ θ m)
    (hζ : ∀ m o, 0 ≤ ζ m o) (θ : Θ) (b : (Θ → ℝ) × X) :
    μ θ * canonical μ ζ σ θ b = b.1 θ * ∑ θ', μ θ' * canonical μ ζ σ θ' b := by
  classical
  simp only [canonical, mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun o ho => ?_
  have hb : relabel μ ζ σ o = b := by convert (mem_filter.1 ho).2
  rw [← hb]
  change joint μ ζ σ θ o = post μ ζ σ o θ * marg μ ζ σ o
  have hj : ∀ θ, 0 ≤ joint μ ζ σ θ o := fun θ =>
    mul_nonneg (hμ θ) (sum_nonneg fun m _ => mul_nonneg (hσ θ m) (hζ m o))
  rcases (sum_nonneg fun θ _ => hj θ : 0 ≤ marg μ ζ σ o).lt_or_eq with h | h
  · simp [post, div_mul_cancel₀ _ h.ne']
  · rw [← h, mul_zero]
    exact (sum_eq_zero_iff_of_nonneg (fun θ _ => hj θ)).1 h.symm θ (mem_univ θ)

/-- **Bayes plausibility.** The canonical posteriors average back to the prior. -/
theorem canonical_bayesPlausible (hσ : ∀ θ, IsDist (σ θ)) (hζ : ∀ m, IsDist (ζ m))
    (hμ : ∀ θ, 0 ≤ μ θ) (θ : Θ) :
    ∑ b ∈ outputs μ ζ σ, (∑ θ', μ θ' * canonical μ ζ σ θ' b) * b.1 θ = μ θ := by
  simp_rw [mul_comm _ (b.1 θ) , ← canonical_posterior hμ (fun θ => (hσ θ).1)
    (fun m => (hζ m).1), ← mul_sum, (canonical_isDist hσ hζ θ).2, mul_one]


end DovalSkreta
