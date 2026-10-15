/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Mathlib.Analysis.Convex.Continuous
import Mathlib.Analysis.Convex.Deriv
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.Tactic.LinearCombination

/-!
# Persuasion with a continuum of states: the price duality (Dworczak–Kolotilin)

The state `θ` lies in `[0, 1]` with an arbitrary prior. The sender's payoff `V m`, measurable
and bounded (`IsPayoff`), depends on the receiver's posterior mean `m` (Kolotilin 2018;
Dworczak & Kolotilin 2024). A signal is
described by the joint law of `(θ, m)`; Bayes' rule says exactly that `m` is the conditional
mean of `θ` given `m` (`Signal.mean_eq`).

A **price** is a convex function `p ≥ V` on `[0, 1]`, a price for each state.
* **Weak duality** (`Signal.value_le`): every signal earns at most the price's expected cost
  `∫ p dμ`. The one identity is that a posterior mean is unbiased:
  `E[g(m) (θ - m)] = 0` (`Signal.integral_mul_sub`). Integrating a supporting line of `p` at
  `m` then gives `E p(m) ≤ E p(θ)`.
* **Verification theorem** (`Signal.optimal_of_slack`), the sufficiency of complementary
  slackness: if `p = V` at every induced posterior mean and `p` is affine on the states pooled
  into each mean, then the signal and the price are both optimal.
* **Corollaries.** Full disclosure is optimal for convex `V` (`full_optimal`), no disclosure
  for concave `V` (`silent_optimal`).
-/

open MeasureTheory Set

namespace MeanPersuasion

/-! ### Supporting lines of a convex function -/

/-- The right derivative: a monotone choice of subgradient of a convex function. -/
noncomputable def subgrad (p : ℝ → ℝ) (x : ℝ) : ℝ := derivWithin p (Ioi x) x

variable {p : ℝ → ℝ}

/-- **A convex function lies above its supporting lines.** -/
lemma le_support (hp : ConvexOn ℝ univ p) (x y : ℝ) : p x + subgrad p x * (y - x) ≤ p y := by
  rcases lt_trichotomy x y with h | rfl | h
  · -- to the right, the right derivative is below the chord slope
    have := hp.rightDeriv_le_slope_of_mem_interior (by simp) (mem_univ y) h
    rw [slope_def_field, le_div_iff₀ (sub_pos.2 h)] at this
    rw [subgrad]; linarith
  · simp
  · -- to the left, the chord slope is below the left derivative, hence the right one
    have h1 := hp.slope_le_leftDeriv_of_mem_interior (mem_univ y) (by simp) h
    have h2 := hp.leftDeriv_le_rightDeriv_of_mem_interior (x := x) (by simp)
    rw [slope_def_field, div_le_iff₀ (sub_pos.2 h)] at h1
    rw [subgrad]; nlinarith

/-- A convex function on `ℝ` is continuous. -/
lemma continuous_of_convexOn (hp : ConvexOn ℝ univ p) : Continuous p :=
  continuousOn_univ.1 (hp.continuousOn isOpen_univ)

lemma subgrad_mono (hp : ConvexOn ℝ univ p) : Monotone (subgrad p) :=
  fun x y h => hp.monotoneOn_rightDeriv (by simp) (by simp) h

/-- Affine functions are convex. -/
lemma convexOn_affine (a b c : ℝ) : ConvexOn ℝ univ fun x => a + b * (x - c) :=
  ⟨convex_univ, fun x _ y _ s t _ _ hst => le_of_eq <| by
    simp only [smul_eq_mul]; linear_combination (c * b - a) * hst⟩

/-! ### Signals -/

/-- A **signal**, described by the joint law `π` of the state `θ` and the posterior mean `m`
it induces (`z = (θ, m)`). States and means lie in `[0, 1]`, and `m` is the conditional mean of
`θ` given `m`: `E[θ g(m)] = E[m g(m)]` for every bounded measurable `g`. -/
structure Signal where
  π : Measure (ℝ × ℝ)
  [isProb : IsProbabilityMeasure π]
  state_mem : ∀ᵐ z ∂π, z.1 ∈ Icc (0 : ℝ) 1
  mean_mem : ∀ᵐ z ∂π, z.2 ∈ Icc (0 : ℝ) 1
  mean_eq : ∀ g : ℝ → ℝ, Measurable g → ∀ C, (∀ x, |g x| ≤ C) →
    ∫ z, z.1 * g z.2 ∂π = ∫ z, z.2 * g z.2 ∂π

attribute [instance] Signal.isProb

/-- A **price** for the sender's payoff `V`: a convex function above `V` on `[0, 1]`. -/
structure IsPrice (V p : ℝ → ℝ) : Prop where
  convex : ConvexOn ℝ univ p
  le : ∀ x ∈ Icc (0 : ℝ) 1, V x ≤ p x

/-- An admissible **sender payoff**: measurable and bounded on `[0, 1]`. It may jump, as a step
payoff `1{m ≥ t}` does. -/
structure IsPayoff (V : ℝ → ℝ) : Prop where
  measurable : Measurable V
  bdd : ∃ B, ∀ x ∈ Icc (0 : ℝ) 1, |V x| ≤ B

lemma IsPayoff.of_continuous {V : ℝ → ℝ} (hV : Continuous V) : IsPayoff V :=
  ⟨hV.measurable, (isCompact_Icc.exists_bound_of_continuousOn hV.continuousOn).imp
    fun _ h x hx => h x hx⟩

lemma IsPrice.continuous {V : ℝ → ℝ} (hp : IsPrice V p) : Continuous p :=
  continuous_of_convexOn hp.convex

namespace Signal

variable (S : Signal)

/-- The prior: the law of the state. -/
noncomputable def prior : Measure ℝ := S.π.map Prod.fst

/-- The sender's expected payoff, when her payoff is `V` of the posterior mean. -/
noncomputable def value (V : ℝ → ℝ) : ℝ := ∫ z, V z.2 ∂S.π

variable {S}

lemma integral_prior {f : ℝ → ℝ} (hf : Continuous f) : ∫ θ, f θ ∂S.prior = ∫ z, f z.1 ∂S.π :=
  integral_map measurable_fst.aemeasurable hf.aestronglyMeasurable

/-- A continuous function of the state or of the mean is integrable. -/
lemma integrable_comp {f : ℝ → ℝ} (hf : Continuous f) {q : ℝ × ℝ → ℝ} (hq : Continuous q)
    (hmem : ∀ᵐ z ∂S.π, q z ∈ Icc (0 : ℝ) 1) : Integrable (fun z => f (q z)) S.π :=
  let ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hf.continuousOn
  (integrable_const C).mono' (hf.comp hq).aestronglyMeasurable (hmem.mono fun _ hz => hC _ hz)

lemma integrable_payoff {V : ℝ → ℝ} (hV : IsPayoff V) : Integrable (fun z => V z.2) S.π :=
  let ⟨B, hB⟩ := hV.bdd
  (integrable_const B).mono' (hV.measurable.comp measurable_snd).aestronglyMeasurable
    (S.mean_mem.mono fun _ hz => hB _ hz)

omit S in
/-- A weight in `[0, 1]` times a bounded function of the mean is integrable, for any finite
law of `(θ, m)`. -/
lemma _root_.MeanPersuasion.integrable_mul_of_mem {π : Measure (ℝ × ℝ)} [IsFiniteMeasure π]
    {q : ℝ × ℝ → ℝ} (hq : Continuous q) (hmem : ∀ᵐ z ∂π, q z ∈ Icc (0 : ℝ) 1)
    {g : ℝ → ℝ} (hg : Measurable g) {C : ℝ} (hC : ∀ x, |g x| ≤ C) :
    Integrable (fun z => q z * g z.2) π :=
  (integrable_const C).mono' (hq.measurable.mul (hg.comp measurable_snd)).aestronglyMeasurable
    (hmem.mono fun z hz => calc
      _ = |q z| * |g z.2| := by rw [Real.norm_eq_abs, abs_mul]
      _ ≤ 1 * C := mul_le_mul (abs_le.2 ⟨by linarith [hz.1], hz.2⟩) (hC _) (abs_nonneg _)
          zero_le_one
      _ = C := one_mul C)

lemma integrable_mul {q : ℝ × ℝ → ℝ} (hq : Continuous q) (hmem : ∀ᵐ z ∂S.π, q z ∈ Icc (0 : ℝ) 1)
    {g : ℝ → ℝ} (hg : Measurable g) {C : ℝ} (hC : ∀ x, |g x| ≤ C) :
    Integrable (fun z => q z * g z.2) S.π :=
  integrable_mul_of_mem hq hmem hg hC

lemma integrable_mul_sub {g : ℝ → ℝ} (hg : Measurable g) {C : ℝ} (hC : ∀ x, |g x| ≤ C) :
    Integrable (fun z => g z.2 * (z.1 - z.2)) S.π :=
  ((integrable_mul continuous_fst S.state_mem hg hC).sub
    (integrable_mul continuous_snd S.mean_mem hg hC)).congr
    (ae_of_all _ fun _ => by simp only [Pi.sub_apply]; ring)

/-- **The posterior mean is unbiased**: `E[g(m) (θ - m)] = 0` for bounded measurable `g`. -/
theorem integral_mul_sub {g : ℝ → ℝ} (hg : Measurable g) {C : ℝ} (hC : ∀ x, |g x| ≤ C) :
    ∫ z, g z.2 * (z.1 - z.2) ∂S.π = 0 := by
  simp_rw [mul_sub, mul_comm (g _)]
  rw [integral_sub (integrable_mul continuous_fst S.state_mem hg hC)
    (integrable_mul continuous_snd S.mean_mem hg hC), S.mean_eq g hg C hC, sub_self]

/-- Adding an unbiased term `g(m) (θ - m)` does not change an expectation. -/
lemma integral_add_mul_sub {f : ℝ × ℝ → ℝ} (hf : Integrable f S.π) {g : ℝ → ℝ}
    (hg : Measurable g) {C : ℝ} (hC : ∀ x, |g x| ≤ C) :
    ∫ z, f z + g z.2 * (z.1 - z.2) ∂S.π = ∫ z, f z ∂S.π := by
  rw [integral_add hf (integrable_mul_sub hg hC), integral_mul_sub hg hC, add_zero]

/-- The subgradient of a convex function, clamped outside `[0, 1]` so that it is bounded. -/
noncomputable def clampedSubgrad (p : ℝ → ℝ) (x : ℝ) : ℝ :=
  max (subgrad p 0) (min (subgrad p x) (subgrad p 1))

lemma clampedSubgrad_spec (hp : ConvexOn ℝ univ p) :
    Measurable (clampedSubgrad p) ∧ (∀ x, |clampedSubgrad p x| ≤ |subgrad p 0| + |subgrad p 1|)
      ∧ ∀ x ∈ Icc (0 : ℝ) 1, clampedSubgrad p x = subgrad p x := by
  have hm := subgrad_mono hp
  -- the clamped subgradient lies between its values at `0` and `1`
  have hlo : ∀ x, subgrad p 0 ≤ clampedSubgrad p x := fun x => le_max_left _ _
  have hhi : ∀ x, clampedSubgrad p x ≤ subgrad p 1 :=
    fun x => max_le (hm zero_le_one) (min_le_right _ _)
  refine ⟨measurable_const.max (hm.measurable.min measurable_const), fun x => abs_le.2 ⟨?_, ?_⟩,
    fun x hx => by rw [clampedSubgrad, min_eq_left (hm hx.2), max_eq_right (hm hx.1)]⟩
  · linarith [hlo x, neg_abs_le (subgrad p 0), abs_nonneg (subgrad p 1)]
  · linarith [hhi x, le_abs_self (subgrad p 1), abs_nonneg (subgrad p 0)]

/-- **Jensen for signals**: a convex function of the posterior mean is on average below the
same function of the state. -/
theorem integral_mean_le (hp : ConvexOn ℝ univ p) :
    ∫ z, p z.2 ∂S.π ≤ ∫ z, p z.1 ∂S.π := by
  have hpc := continuous_of_convexOn hp
  obtain ⟨hg, hC, heq⟩ := clampedSubgrad_spec hp
  have hi := integrable_comp hpc continuous_snd S.mean_mem
  -- integrate the supporting line at the mean; its slope term is unbiased
  rw [← integral_add_mul_sub hi hg hC]
  refine integral_mono_ae (hi.add (integrable_mul_sub hg hC))
    (integrable_comp hpc continuous_fst S.state_mem) (S.mean_mem.mono fun z hz => ?_)
  simpa only [heq _ hz] using le_support hp z.2 z.1

variable {V : ℝ → ℝ}

/-- **Weak duality**: no signal beats the expected cost of a price. -/
theorem value_le (hV : IsPayoff V) (hp : IsPrice V p) : S.value V ≤ ∫ θ, p θ ∂S.prior := by
  rw [integral_prior hp.continuous]
  calc S.value V ≤ ∫ z, p z.2 ∂S.π := integral_mono_ae (integrable_payoff hV)
        (integrable_comp hp.continuous continuous_snd S.mean_mem)
        (S.mean_mem.mono fun z hz => hp.le _ hz)
    _ ≤ ∫ z, p z.1 ∂S.π := integral_mean_le hp.convex

/-- **Sufficiency of complementary slackness** (Dworczak–Kolotilin): if the price equals `V` at
every induced posterior mean, and is affine (with slope `ℓ m`) on the states pooled into each
mean `m`, then the value of the signal equals the expected cost of the price. (The slope can
always be taken to be `clampedSubgrad p`.) -/
theorem value_eq_of_slack (hp : IsPrice V p) (hVp : ∀ᵐ z ∂S.π, V z.2 = p z.2)
    {ℓ : ℝ → ℝ} (hℓ : Measurable ℓ) {C : ℝ} (hC : ∀ x, |ℓ x| ≤ C)
    (haff : ∀ᵐ z ∂S.π, p z.1 = p z.2 + ℓ z.2 * (z.1 - z.2)) :
    S.value V = ∫ θ, p θ ∂S.prior := by
  have hpc := hp.continuous
  rw [integral_prior hpc, value, integral_congr_ae hVp, integral_congr_ae haff,
    integral_add_mul_sub (integrable_comp hpc continuous_snd S.mean_mem) hℓ hC]

/-- **Verification theorem**: under complementary slackness the signal is optimal among all
signals with the same prior, and the price is optimal among all prices. -/
theorem optimal_of_slack (hV : IsPayoff V) (hp : IsPrice V p)
    (hVp : ∀ᵐ z ∂S.π, V z.2 = p z.2) {ℓ : ℝ → ℝ} (hℓ : Measurable ℓ) {C : ℝ}
    (hC : ∀ x, |ℓ x| ≤ C) (haff : ∀ᵐ z ∂S.π, p z.1 = p z.2 + ℓ z.2 * (z.1 - z.2)) :
    (∀ S' : Signal, S'.prior = S.prior → S'.value V ≤ S.value V) ∧
      ∀ q, IsPrice V q → ∫ θ, p θ ∂S.prior ≤ ∫ θ, q θ ∂S.prior := by
  have h := value_eq_of_slack hp hVp hℓ hC haff
  exact ⟨fun S' hS' => h ▸ hS' ▸ S'.value_le hV hp, fun q hq => h ▸ S.value_le hV hq⟩

end Signal

/-! ### Full and no disclosure -/

variable (μ : Measure ℝ) [IsProbabilityMeasure μ]

omit [IsProbabilityMeasure μ] in
/-- Expectations under a signal built from the prior. -/
lemma integral_map_snd {φ : ℝ → ℝ × ℝ} (hφ : Measurable φ) {V : ℝ → ℝ} (hV : Continuous V) :
    ∫ z, V z.2 ∂(μ.map φ) = ∫ θ, V (φ θ).2 ∂μ :=
  integral_map hφ.aemeasurable (hV.comp continuous_snd).aestronglyMeasurable

/-- The signal that reveals the state: `m = θ`. -/
noncomputable def full (hμ : ∀ᵐ θ ∂μ, θ ∈ Icc (0 : ℝ) 1) : Signal where
  π := μ.map fun θ => (θ, θ)
  state_mem := (ae_map_iff (by fun_prop) (measurableSet_Icc.preimage measurable_fst)).2 hμ
  mean_mem := (ae_map_iff (by fun_prop) (measurableSet_Icc.preimage measurable_snd)).2 hμ
  mean_eq g hg _ _ := by
    rw [integral_map (by fun_prop) (by fun_prop), integral_map (by fun_prop) (by fun_prop)]

/-- The prior mean. -/
noncomputable def priorMean : ℝ := ∫ θ, θ ∂μ

variable {μ}

lemma priorMean_mem (hμ : ∀ᵐ θ ∂μ, θ ∈ Icc (0 : ℝ) 1) : priorMean μ ∈ Icc (0 : ℝ) 1 := by
  have hi : Integrable (fun θ : ℝ => θ) μ := (integrable_const (1 : ℝ)).mono'
    measurable_id.aestronglyMeasurable (hμ.mono fun θ h => abs_le.2 ⟨by linarith [h.1], h.2⟩)
  refine ⟨integral_nonneg_of_ae (hμ.mono fun θ h => h.1), ?_⟩
  calc priorMean μ ≤ ∫ _, (1 : ℝ) ∂μ := integral_mono_ae hi (integrable_const 1)
        (hμ.mono fun θ h => h.2)
    _ = 1 := by simp

/-- The signal that reveals nothing: `m` is the prior mean. -/
noncomputable def silent (hμ : ∀ᵐ θ ∂μ, θ ∈ Icc (0 : ℝ) 1) : Signal where
  π := μ.map fun θ => (θ, priorMean μ)
  state_mem := (ae_map_iff (by fun_prop) (measurableSet_Icc.preimage measurable_fst)).2 hμ
  mean_mem := (ae_map_iff (by fun_prop) (measurableSet_Icc.preimage measurable_snd)).2
    (ae_of_all _ fun _ => priorMean_mem hμ)
  mean_eq g hg _ _ := by
    rw [integral_map (by fun_prop) (by fun_prop), integral_map (by fun_prop) (by fun_prop)]
    simp [integral_mul_const, priorMean]

lemma full_prior (hμ : ∀ᵐ θ ∂μ, θ ∈ Icc (0 : ℝ) 1) : (full μ hμ).prior = μ := by
  rw [Signal.prior, full, Measure.map_map measurable_fst (by fun_prop)]; exact Measure.map_id

lemma silent_prior (hμ : ∀ᵐ θ ∂μ, θ ∈ Icc (0 : ℝ) 1) : (silent hμ).prior = μ := by
  rw [Signal.prior, silent, Measure.map_map measurable_fst (by fun_prop)]; exact Measure.map_id

variable {V : ℝ → ℝ}

/-- **Full disclosure is optimal when `V` is convex**: `V` is then its own price. -/
theorem full_optimal (hV : ConvexOn ℝ univ V) (hμ : ∀ᵐ θ ∂μ, θ ∈ Icc (0 : ℝ) 1)
    (S : Signal) (hS : S.prior = μ) : S.value V ≤ (full μ hμ).value V := by
  have hp : IsPrice V V := ⟨hV, fun _ _ => le_rfl⟩
  calc S.value V ≤ ∫ θ, V θ ∂μ := hS ▸ S.value_le (.of_continuous hp.continuous) hp
    _ = (full μ hμ).value V := by
      dsimp only [Signal.value, full]; rw [integral_map_snd μ (by fun_prop) hp.continuous]

/-- **No disclosure is optimal when `V` is concave**: a supporting line at the prior mean is a
price that costs exactly `V` of the prior mean. -/
theorem silent_optimal (hV : ConcaveOn ℝ univ V) (hμ : ∀ᵐ θ ∂μ, θ ∈ Icc (0 : ℝ) 1)
    (S : Signal) (hS : S.prior = μ) : S.value V ≤ (silent hμ).value V := by
  set c := priorMean μ
  set t := subgrad (-V) c
  -- a supporting line of `V` at the prior mean is a price
  have hp : IsPrice V fun x => V c + -t * (x - c) := ⟨convexOn_affine _ _ _, fun x _ => by
    have := le_support hV.neg c x; simp only [Pi.neg_apply] at this; linarith⟩
  have hVc : Continuous V := by simpa using continuous_of_convexOn hV.neg
  have hi : Integrable (fun θ : ℝ => θ) μ := (integrable_const (1 : ℝ)).mono'
    measurable_id.aestronglyMeasurable (hμ.mono fun θ h => abs_le.2 ⟨by linarith [h.1], h.2⟩)
  calc S.value V ≤ ∫ θ, V c + -t * (θ - c) ∂μ := hS ▸ S.value_le (.of_continuous hVc) hp
    _ = V c := by
      have h1 : Integrable (fun θ : ℝ => θ - c) μ := hi.sub (integrable_const c)
      rw [integral_add (integrable_const _) (h1.const_mul _), integral_const_mul,
        integral_sub hi (integrable_const c)]
      simp [c, priorMean]
    _ = (silent hμ).value V := by
      dsimp only [Signal.value, silent]; rw [integral_map_snd μ (by fun_prop) hVc]
      simp [c]

end MeanPersuasion
