/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Prod

/-!
# Doval–Skreta: canonical mechanisms with beliefs as output messages

Doval & Skreta (*Mechanism Design with Limited Commitment*, Econometrica 2022) show that when
the principal cannot commit to future mechanisms, it is without loss to use *canonical*
mechanisms: the agent reports a type and the mechanism publicly announces the principal's
**posterior**, which is then *self-consistent*: announcing `β` induces the posterior `β`.

The engine is a one-shot statement. Whatever happens after the mechanism (the principal's
sequentially rational continuation, future mechanisms, ...) affects payoffs only through the
public allocation `x` and the posterior `β`. So take any play of any mechanism and *relabel*
each public outcome `o = (s, x)` by `(posterior after o, x)`. The relabelled mechanism

* is incentive compatible (`canonical_IC`),
* induces the same distribution of (allocation, posterior) for each type
  (`canonical_outcome_eq`), so every player's payoff is unchanged,
* is self-consistent (`canonical_posterior`) and Bayes plausible (`canonical_bayesPlausible`).

Distributions are nonnegative real vectors summing to one; beliefs are vectors `Θ → ℝ`.
-/

open Finset Classical

namespace DovalSkreta

/-- `p` is a probability vector. -/
def IsDist {α : Type*} [Fintype α] (p : α → ℝ) : Prop := (∀ a, 0 ≤ p a) ∧ ∑ a, p a = 1

namespace IsDist

variable {α : Type*} [Fintype α] {p f : α → ℝ}

lemma wavg_const (hp : IsDist p) (c : ℝ) : ∑ a, p a * c = c := by rw [← sum_mul, hp.2, one_mul]

/-- An average lies below any upper bound. -/
lemma wavg_le (hp : IsDist p) {c : ℝ} (h : ∀ a, f a ≤ c) : ∑ a, p a * f a ≤ c :=
  (sum_le_sum fun a _ => mul_le_mul_of_nonneg_left (h a) (hp.1 a)).trans_eq (hp.wavg_const c)

/-- An average of maximisers is a maximum. -/
lemma le_wavg (hp : IsDist p) (h : ∀ a, 0 < p a → ∀ b, f b ≤ f a) (b : α) :
    f b ≤ ∑ a, p a * f a :=
  (hp.wavg_const (f b)).symm.trans_le <| sum_le_sum fun a _ => by
    rcases (hp.1 a).eq_or_lt with h0 | h0
    · simp [← h0]
    · exact mul_le_mul_of_nonneg_left (h a h0 b) h0.le

end IsDist

/-- A play of a mechanism: a prior `μ` over types, a mechanism `ζ` mapping input messages to
distributions over public outcomes `o`, each with an allocation `alloc o`, and the agent's
strategy `σ`. (Doval–Skreta's outcomes are pairs (output message, allocation).) -/
structure Play (Θ M O X : Type*) where
  μ : Θ → ℝ
  ζ : M → O → ℝ
  σ : Θ → M → ℝ
  alloc : O → X

variable {Θ M O X : Type*} [Fintype Θ] [Fintype M] [Fintype O]

namespace Play

variable (P : Play Θ M O X)

/-- All the probabilities involved are probabilities. (Normalisation of the prior is not
used by the proofs; it is part of what a play means.) -/
structure Valid : Prop where
  μ : IsDist P.μ
  ζ : ∀ m, IsDist (P.ζ m)
  σ : ∀ θ, IsDist (P.σ θ)

/-- Probability that type `θ`'s play produces public outcome `o`. -/
def outProb (θ : Θ) (o : O) : ℝ := ∑ m, P.σ θ m * P.ζ m o

/-- Joint probability of type `θ` and public outcome `o`. -/
def joint (θ : Θ) (o : O) : ℝ := P.μ θ * P.outProb θ o

/-- The principal's posterior after public outcome `o` (Bayes' rule). -/
noncomputable def post (o : O) : Θ → ℝ := fun θ => P.joint θ o / ∑ θ', P.joint θ' o

/-- Relabel a public outcome by (the posterior it induces, the allocation). -/
noncomputable def relabel (o : O) : (Θ → ℝ) × X := (P.post o, P.alloc o)

/-- The canonical outputs. -/
noncomputable def outputs : Finset ((Θ → ℝ) × X) := univ.image P.relabel

/-- **The canonical mechanism**: report `θ` yields output `b = (β, x)` with the total
probability of the original public outcomes relabelled to `b`. -/
noncomputable def canonical (θ : Θ) (b : (Θ → ℝ) × X) : ℝ :=
  ∑ o ∈ univ.filter (P.relabel · = b), P.outProb θ o

/-- The image of a weight on outcomes under `relabel`. -/
noncomputable def pushforward (w : O → ℝ) (b : (Θ → ℝ) × X) : ℝ :=
  ∑ o ∈ univ.filter (P.relabel · = b), w o

/-- **Change of variables**: integrating against the image of `w` under `relabel` is
integrating against `w` after relabelling. -/
theorem sum_pushforward (w : O → ℝ) (g : (Θ → ℝ) × X → ℝ) :
    ∑ b ∈ P.outputs, P.pushforward w b * g b = ∑ o, w o * g (P.relabel o) := by
  simp_rw [pushforward, sum_mul]
  rw [← sum_fiberwise_of_maps_to (g := P.relabel) fun o _ => mem_image_of_mem _ (mem_univ o)]
  exact sum_congr rfl fun b _ => sum_congr (by ext; simp) fun o ho => by
    rw [(mem_filter.1 ho).2]

/-- **Change of variables**: the canonical mechanism is the image of the original one under
`relabel`. -/
theorem sum_canonical (θ : Θ) (g : (Θ → ℝ) × X → ℝ) :
    ∑ b ∈ P.outputs, P.canonical θ b * g b = ∑ o, P.outProb θ o * g (P.relabel o) :=
  P.sum_pushforward (P.outProb θ) g

/-- Expected utility of type `θ` sending message `m` in the original mechanism, when
continuation utility `u θ x β` depends on the allocation and the public posterior. -/
noncomputable def payoff (u : Θ → X → (Θ → ℝ) → ℝ) (θ : Θ) (m : M) : ℝ :=
  ∑ o, P.ζ m o * u θ (P.alloc o) (P.post o)

/-- Expected utility of type `θ` reporting `θ'` in the canonical mechanism. -/
noncomputable def canonicalPayoff (u : Θ → X → (Θ → ℝ) → ℝ) (θ θ' : Θ) : ℝ :=
  ∑ b ∈ P.outputs, P.canonical θ' b * u θ b.2 b.1

/-- Reporting `θ'` canonically is playing `σ θ'` originally. -/
theorem canonicalPayoff_eq (u : Θ → X → (Θ → ℝ) → ℝ) (θ θ' : Θ) :
    P.canonicalPayoff u θ θ' = ∑ m, P.σ θ' m * P.payoff u θ m := by
  simp only [canonicalPayoff, sum_canonical, payoff, outProb, relabel, sum_mul, mul_sum]
  rw [sum_comm]; simp_rw [mul_assoc]

variable {P}

/-- **Outcome equivalence**: for each type, truth-telling in the canonical mechanism yields the
same expectation of every function of (allocation, posterior) as `σ` does originally. -/
theorem canonical_outcome_eq (θ : Θ) (g : X → (Θ → ℝ) → ℝ) :
    ∑ b ∈ P.outputs, P.canonical θ b * g b.2 b.1 =
      ∑ o, P.outProb θ o * g (P.alloc o) (P.post o) :=
  P.sum_canonical θ fun b => g b.2 b.1

/-- **Incentive compatibility**: if `σ` puts weight only on best responses, truth-telling is
optimal in the canonical mechanism. (A misreport mixes messages, none better than the
equilibrium mixture of best responses.) -/
theorem canonical_IC (hP : P.Valid) (u : Θ → X → (Θ → ℝ) → ℝ)
    (hbr : ∀ θ m, 0 < P.σ θ m → ∀ m', P.payoff u θ m' ≤ P.payoff u θ m) (θ θ' : Θ) :
    P.canonicalPayoff u θ θ' ≤ P.canonicalPayoff u θ θ := by
  rw [canonicalPayoff_eq, canonicalPayoff_eq]
  exact (hP.σ θ').wavg_le ((hP.σ θ).le_wavg (hbr θ))

/-- Each report yields a probability distribution over canonical outputs. -/
theorem canonical_isDist (hP : P.Valid) (θ : Θ) :
    (∀ b, 0 ≤ P.canonical θ b) ∧ ∑ b ∈ P.outputs, P.canonical θ b = 1 := by
  refine ⟨fun b => sum_nonneg fun o _ => sum_nonneg fun m _ =>
    mul_nonneg ((hP.σ θ).1 m) ((hP.ζ m).1 o), ?_⟩
  have := P.sum_canonical θ fun _ => 1
  simp only [mul_one, outProb] at this
  rw [this, sum_comm]
  simp [← mul_sum, (hP.ζ _).2, (hP.σ θ).2]

/-- **Self-consistency**: under truth-telling, `P(θ, b) = β(θ) P(b)` for each output
`b = (β, x)`; the posterior after announcing `β` is `β`. -/
theorem canonical_posterior (hP : P.Valid) (θ : Θ) (b : (Θ → ℝ) × X) :
    P.μ θ * P.canonical θ b = b.1 θ * ∑ θ', P.μ θ' * P.canonical θ' b := by
  simp only [canonical, mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun o ho => ?_
  have hb : P.relabel o = b := by convert (mem_filter.1 ho).2
  rw [← hb, ← mul_sum]
  change P.joint θ o = P.joint θ o / (∑ θ', P.joint θ' o) * ∑ θ', P.joint θ' o
  have hj : ∀ θ, 0 ≤ P.joint θ o := fun θ =>
    mul_nonneg (hP.μ.1 θ) (sum_nonneg fun m _ => mul_nonneg ((hP.σ θ).1 m) ((hP.ζ m).1 o))
  rcases (sum_nonneg fun θ _ => hj θ).eq_or_lt with h | h
  · rw [← h, mul_zero]
    exact (sum_eq_zero_iff_of_nonneg fun θ _ => hj θ).1 h.symm θ (mem_univ θ)
  · rw [div_mul_cancel₀ _ h.ne']

/-- On path the principal's posterior is a genuine belief. (Off path, where the outcome has
probability zero, `post` is the junk value `0`.) -/
theorem post_isDist (hP : P.Valid) {o : O} (ho : 0 < ∑ θ, P.joint θ o) :
    IsDist (P.post o) := by
  refine ⟨fun θ => div_nonneg (mul_nonneg (hP.μ.1 θ) (sum_nonneg fun m _ =>
    mul_nonneg ((hP.σ θ).1 m) ((hP.ζ m).1 o))) ho.le, ?_⟩
  simp only [post]; rw [← sum_div, div_self ho.ne']

/-- **Bayes plausibility**: the canonical posteriors average back to the prior. -/
theorem canonical_bayesPlausible (hP : P.Valid) (θ : Θ) :
    ∑ b ∈ P.outputs, (∑ θ', P.μ θ' * P.canonical θ' b) * b.1 θ = P.μ θ := by
  calc _ = ∑ b ∈ P.outputs, P.μ θ * P.canonical θ b :=
        sum_congr rfl fun b _ => by rw [canonical_posterior hP θ b, mul_comm]
    _ = P.μ θ := by rw [← mul_sum, (canonical_isDist hP θ).2, mul_one]

/-! ### The canonical mechanism as a play -/

variable (P) in
/-- **The canonical play**: the agent reports a type (truthfully) or takes the exit message
`m₀`, and the mechanism announces a canonical output `(β, x)`, a posterior together with an
allocation. Exiting yields the relabelled outcome of `m₀`. -/
noncomputable def toCanonical (m₀ : M) : Play Θ (Option Θ) P.outputs X where
  μ := P.μ
  ζ r b := r.elim (P.pushforward (P.ζ m₀) b.1) fun θ => P.canonical θ b.1
  σ θ r := r.elim 0 fun θ' => if θ = θ' then 1 else 0
  alloc b := b.1.2

variable {m₀ : M}

@[simp] lemma toCanonical_alloc (b : P.outputs) : (P.toCanonical m₀).alloc b = b.1.2 := rfl

@[simp] lemma toCanonical_exitProb (b : P.outputs) :
    (P.toCanonical m₀).ζ none b = P.pushforward (P.ζ m₀) b.1 := rfl

@[simp] lemma toCanonical_outProb (θ : Θ) (b : P.outputs) :
    (P.toCanonical m₀).outProb θ b = P.canonical θ b.1 := by
  simp [outProb, toCanonical, Fintype.sum_option]

/-- In the canonical play, announcing `β` induces the posterior `β`, on path and off. -/
lemma toCanonical_post (hP : P.Valid) (b : P.outputs) : (P.toCanonical m₀).post b = b.1.1 := by
  ext θ
  have hpost := canonical_posterior hP θ b.1
  simp only [post, joint, toCanonical_outProb]
  change P.μ θ * P.canonical θ b.1 / ∑ θ', P.μ θ' * P.canonical θ' b.1 = b.1.1 θ
  have hnn : ∀ θ', 0 ≤ P.μ θ' * P.canonical θ' b.1 :=
    fun θ' => mul_nonneg (hP.μ.1 θ') ((canonical_isDist hP θ').1 _)
  rcases (sum_nonneg fun θ' _ => hnn θ').eq_or_lt with h | h
  · -- off path: every original outcome relabelled to `b` has probability zero, so its
    -- posterior is the junk value `0`, as is the canonical one
    obtain ⟨o, -, ho⟩ := mem_image.1 b.2
    have hmarg : ∑ θ', P.joint θ' o = 0 := by
      refine le_antisymm ?_ (sum_nonneg fun θ' _ => mul_nonneg (hP.μ.1 θ') (sum_nonneg
        fun m _ => mul_nonneg ((hP.σ θ').1 m) ((hP.ζ m).1 o)))
      rw [h]; refine sum_le_sum fun θ' _ => ?_
      rw [joint, canonical]
      exact mul_le_mul_of_nonneg_left (single_le_sum (f := P.outProb θ') (fun o' _ =>
        sum_nonneg fun m _ => mul_nonneg ((hP.σ θ').1 m) ((hP.ζ m).1 o'))
        (mem_filter.2 ⟨mem_univ o, ho⟩)) (hP.μ.1 θ')
    rw [← h, div_zero, ← ho]
    simp [relabel, post, hmarg]
  · rw [hpost, mul_div_assoc, div_self h.ne', mul_one]

lemma toCanonical_valid (hP : P.Valid) : (P.toCanonical m₀).Valid where
  μ := hP.μ
  ζ r := by
    cases r with
    | none =>
      have := P.sum_pushforward (P.ζ m₀) fun _ => 1
      simp only [mul_one, (hP.ζ m₀).2] at this
      exact ⟨fun b => sum_nonneg fun o _ => (hP.ζ m₀).1 o,
        (Finset.sum_coe_sort P.outputs _).trans this⟩
    | some θ =>
      exact ⟨fun b => (canonical_isDist hP θ).1 _, by
        simpa [toCanonical] using (Finset.sum_coe_sort P.outputs (P.canonical θ)).trans
          (canonical_isDist hP θ).2⟩
  σ θ := ⟨fun r => by cases r <;> simp only [toCanonical, Option.elim] <;> positivity,
    by simp [toCanonical, Fintype.sum_option]⟩

/-- **The canonical play is outcome-equivalent**: each type gets the same distribution of
(allocation, posterior) as under `σ` in the original play. -/
lemma toCanonical_outcome_eq (hP : P.Valid) (θ : Θ) (g : X → (Θ → ℝ) → ℝ) :
    ∑ b, (P.toCanonical m₀).outProb θ b *
        g ((P.toCanonical m₀).alloc b) ((P.toCanonical m₀).post b) =
      ∑ o, P.outProb θ o * g (P.alloc o) (P.post o) := by
  simp only [toCanonical_outProb, toCanonical_post hP]
  rw [← canonical_outcome_eq θ g]
  exact Finset.sum_coe_sort P.outputs (fun b => P.canonical θ b * g b.2 b.1)

/-- **The canonical play is truthful**: reporting one's type is a best response, against
misreports and against exiting. -/
lemma toCanonical_IC (hP : P.Valid) (u : Θ → X → (Θ → ℝ) → ℝ)
    (hbr : ∀ θ m, 0 < P.σ θ m → ∀ m', P.payoff u θ m' ≤ P.payoff u θ m) (θ : Θ)
    (r : Option Θ) : (P.toCanonical m₀).payoff u θ r ≤ (P.toCanonical m₀).payoff u θ (some θ) := by
  have e : ∀ θ', (P.toCanonical m₀).payoff u θ (some θ') = P.canonicalPayoff u θ θ' :=
    fun θ' => by
      simp only [payoff, canonicalPayoff, toCanonical_post hP]
      exact Finset.sum_coe_sort P.outputs (fun b => P.canonical θ' b * u θ b.2 b.1)
  cases r with
  | some θ' => rw [e, e]; exact canonical_IC hP u hbr θ θ'
  | none =>
    -- exiting relabels the original exit message, which is no better than equilibrium play
    have hexit : (P.toCanonical m₀).payoff u θ none = P.payoff u θ m₀ := by
      simp only [payoff, toCanonical_post hP, toCanonical_alloc, toCanonical_exitProb]
      rw [Finset.sum_coe_sort P.outputs (fun b => P.pushforward (P.ζ m₀) b * u θ b.2 b.1)]
      exact P.sum_pushforward (P.ζ m₀) fun b => u θ b.2 b.1
    rw [hexit, e, canonicalPayoff_eq]
    exact (hP.σ θ).le_wavg (hbr θ) m₀

/-- If `m₀` surely yields the allocation `x₀`, so does exiting the canonical play. -/
lemma toCanonical_exit {x₀ : X} (h : ∀ o, 0 < P.ζ m₀ o → P.alloc o = x₀) (b : P.outputs)
    (hb : 0 < (P.toCanonical m₀).ζ none b) : (P.toCanonical m₀).alloc b = x₀ := by
  -- some original outcome relabelled to `b` has positive exit probability
  by_contra hne
  refine hb.not_ge (sum_nonpos fun o ho => not_lt.1 fun hpos => hne ?_)
  rw [← h o hpos, toCanonical_alloc, ← (mem_filter.1 ho).2]
  rfl

end Play

end DovalSkreta
