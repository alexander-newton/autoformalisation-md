/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import MechDesign.Strassen
import Mathlib.Probability.Kernel.Disintegration.Integral
import Mathlib.Probability.Kernel.Disintegration.StandardBorel

/-!
# Dworczak–Kolotilin (2024): the persuasion duality, one-dimensional moment case

We reproduce the duality of Dworczak & Kolotilin, *The persuasion duality* (Theoretical
Economics 19, 2024), Sections 2–4, for the state space `Ω = [0, 1]` and an objective
`V(μ) = v(E_μ[ω])` that depends on the posterior through its mean.

* **Posteriors.** A signal (`Signal`) is the joint law of `(θ, m)`; the posterior after the
  posterior mean `m` is the conditional law of `θ` (`Signal.posterior`, a disintegration). Its
  mean is `m` (`Signal.integral_posterior_id`).
* **The dual (D)** (DK, Section 2): a *state price* (`IsStatePrice`) is a Lipschitz `p` on the
  states with `v(E_ν ω) ≤ ∫ p dν` for **every** belief `ν` on `[0, 1]`. The dual value
  (`stateValue`) is the least cost `∫ p dμ₀` of a state price.
* **Theorem 1 (weak duality)** (`Signal.value_le_statePrice`): apply the dual constraint to
  each posterior, then average over posteriors (DK, Appendix A.1).
-/

open MeasureTheory Set ProbabilityTheory

namespace MeanPersuasion

variable {v p : ℝ → ℝ}

/-! ### Posteriors -/

namespace Signal

variable (S : Signal)

/-- The joint law of (posterior mean, state). -/
noncomputable def flip : Measure (ℝ × ℝ) := S.π.map Prod.swap

instance : IsProbabilityMeasure S.flip := by unfold flip; infer_instance

/-- **The posterior** after the posterior mean `m`: the conditional law of the state given `m`. -/
noncomputable def posterior : Kernel ℝ ℝ := S.flip.condKernel

instance : IsMarkovKernel S.posterior := by unfold posterior; infer_instance

lemma flip_fst : S.flip.fst = S.posteriorMeans.ν := by
  rw [flip, Measure.fst, Measure.map_map measurable_fst measurable_swap]; rfl

variable {S}

/-- **Averaging over posteriors** recovers the joint law. -/
lemma integral_posterior {F : ℝ × ℝ → ℝ} (hFm : Measurable F) (hF : Integrable F S.π) :
    ∫ m, ∫ θ, F (θ, m) ∂S.posterior m ∂S.posteriorMeans.ν = ∫ z, F z ∂S.π := by
  have hF' : Integrable (fun z : ℝ × ℝ => F z.swap) S.flip :=
    (integrable_map_measure (hFm.comp measurable_swap).aestronglyMeasurable
      measurable_swap.aemeasurable).2 (by simpa [Function.comp_def] using hF)
  have h := Measure.integral_condKernel hF'
  simp only [Prod.swap_prod_mk] at h
  rw [← flip_fst, posterior, h, flip, integral_map measurable_swap.aemeasurable
    (f := fun x : ℝ × ℝ => F x.swap) (hFm.comp measurable_swap).aestronglyMeasurable]
  simp

/-- Posteriors are beliefs on `[0, 1]`. -/
lemma ae_posterior_mem :
    ∀ᵐ m ∂S.posteriorMeans.ν, ∀ᵐ θ ∂S.posterior m, θ ∈ Icc (0 : ℝ) 1 := by
  have h : ∀ᵐ z ∂S.flip, z.2 ∈ Icc (0 : ℝ) 1 :=
    (ae_map_iff measurable_swap.aemeasurable (measurableSet_Icc.preimage measurable_snd)).2
      S.state_mem
  rw [← S.flip.disintegrate S.flip.condKernel] at h
  rw [← flip_fst]; exact Measure.ae_ae_of_ae_compProd h

lemma integrable_posterior_of_bdd {f : ℝ → ℝ} (hf : IsPayoff f) :
    ∀ᵐ m ∂S.posteriorMeans.ν, Integrable f (S.posterior m) :=
  ae_posterior_mem.mono fun _ hm => integrable_of_mem hm hf

/-- **The posterior's mean is the posterior mean** (DK's martingale constraint): `∫ θ, h(m) (θ - m)`
vanishes for the bounded `h(m) = E[θ | m] - m`, so `∫ h² = 0`. -/
lemma ae_integral_posterior_id :
    ∀ᵐ m ∂S.posteriorMeans.ν, ∫ θ, θ ∂S.posterior m = m := by
  set ν := S.posteriorMeans.ν
  set h : ℝ → ℝ := fun m => ∫ θ, θ ∂S.posterior m - m
  have hmeas : Measurable h :=
    (stronglyMeasurable_id.integral_kernel (κ := S.posterior)).measurable.sub measurable_id
  have hid := IsPayoff.of_continuous continuous_id
  -- on posteriors and means in `[0, 1]`, `|h| ≤ 1`
  have hbd : ∀ᵐ m ∂ν, |h m| ≤ 1 := by
    filter_upwards [ae_posterior_mem, S.posteriorMeans.mem] with m hm hm'
    have h1 := integral_mono_ae (integrable_const (0 : ℝ)) (integrable_of_mem hm hid)
      (hm.mono fun θ hθ => hθ.1)
    have h2 := integral_mono_ae (integrable_of_mem hm hid) (integrable_const (1 : ℝ))
      (hm.mono fun θ hθ => hθ.2)
    have hone : (S.posterior m).real univ = 1 := by simp
    simp only [integral_const, smul_eq_mul, mul_one, mul_zero, hone, id] at h1 h2
    rw [abs_le]; constructor <;> linarith [hm'.1, hm'.2]
  set g : ℝ → ℝ := fun m => max (-1) (min (h m) 1)
  have hg : Measurable g := measurable_const.max (hmeas.min measurable_const)
  have hgC : ∀ x, |g x| ≤ 1 := fun x => abs_le.2 ⟨le_max_left _ _,
    max_le (by norm_num) (min_le_right _ _)⟩
  have hgh : ∀ᵐ m ∂ν, g m = h m := hbd.mono fun m hm => by
    simp only [g, min_eq_left (abs_le.1 hm).2, max_eq_right (abs_le.1 hm).1]
  -- the martingale condition, averaged over posteriors: `∫ g h dν = 0`
  have hzero := S.integral_mul_sub hg hgC
  rw [← integral_posterior (F := fun z => g z.2 * (z.1 - z.2)) (by fun_prop)
    (integrable_mul_sub hg hgC)] at hzero
  have hgh2 : ∫ m, h m ^ 2 ∂ν = 0 := by
    rw [← hzero]
    refine integral_congr_ae ?_
    filter_upwards [ae_posterior_mem, hgh] with m hm hgm
    have hone : (S.posterior m).real univ = 1 := by simp
    rw [integral_const_mul, integral_sub (integrable_of_mem hm hid : Integrable (fun a : ℝ => a) _)
      (integrable_const m), integral_const, hone, one_smul, hgm, sq]
  have := (integral_eq_zero_iff_of_nonneg (fun m => sq_nonneg (h m))
    ((integrable_const (1 : ℝ)).mono' (hmeas.pow_const 2).aestronglyMeasurable
      (hbd.mono fun m hm => by
        rw [Real.norm_eq_abs, abs_pow]; nlinarith [abs_nonneg (h m)]))).1 hgh2
  filter_upwards [this] with m hm
  have : h m = 0 := by simpa using hm
  linarith

end Signal

/-! ### The dual problem (D) -/

/-- A **state price** (DK's dual variable, with states `Ω = [0, 1]`): Lipschitz on the states,
and for every belief `ν` on `[0, 1]` the expected price `∫ p dν` covers the payoff `v` of the
belief's mean. (`p` is a function on `ℝ`; only its values on `[0, 1]` matter, and it is taken
measurable.) -/
structure IsStatePrice (v p : ℝ → ℝ) : Prop where
  lipschitz : ∃ K, LipschitzOnWith K p (Icc 0 1)
  measurable : Measurable p
  le : ∀ ν : Measure ℝ, IsProbabilityMeasure ν → (∀ᵐ x ∂ν, x ∈ Icc (0 : ℝ) 1) →
    v (∫ x, x ∂ν) ≤ ∫ x, p x ∂ν

/-- The **dual value** of (D): the least cost of a state price. -/
noncomputable def stateValue (v : ℝ → ℝ) (μ : Measure ℝ) : ℝ :=
  ⨅ p : {p // IsStatePrice v p}, ∫ θ, p.1 θ ∂μ

namespace IsStatePrice

variable (hp : IsStatePrice v p)
include hp

/-- A state price is bounded on `[0, 1]`. -/
lemma isPayoff : IsPayoff p := by
  obtain ⟨K, hK⟩ := hp.lipschitz
  refine ⟨hp.measurable, |p 0| + K, fun x hx => ?_⟩
  have := hK.dist_le_mul x hx 0 ⟨le_rfl, zero_le_one⟩
  rw [Real.dist_eq, Real.dist_eq, sub_zero, abs_of_nonneg hx.1] at this
  linarith [abs_sub_abs_le_abs_sub (p x) (p 0), mul_le_of_le_one_right (NNReal.coe_nonneg K) hx.2]

/-- A state price lies above `v` on `[0, 1]`: test it on point beliefs. -/
lemma le_apply {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) : v x ≤ p x := by
  simpa using hp.le (Measure.dirac x) inferInstance ((ae_dirac_iff measurableSet_Icc).2 hx)

end IsStatePrice

/-! ### Averaging over posteriors -/

namespace Signal

variable {S : Signal} {f : ℝ → ℝ}

lemma integrable_integral_posterior (hf : IsPayoff f) :
    Integrable (fun m => ∫ θ, f θ ∂S.posterior m) S.posteriorMeans.ν := by
  obtain ⟨B, hB⟩ := hf.bdd
  refine (integrable_const B).mono'
    (hf.measurable.stronglyMeasurable.integral_kernel).aestronglyMeasurable
    (ae_posterior_mem.mono fun m hm => ?_)
  rw [Real.norm_eq_abs]
  exact (abs_integral_le_integral_abs).trans ((integral_mono_ae (integrable_of_mem hm hf).abs
    (integrable_const B) (hm.mono fun θ hθ => hB θ hθ)).trans (by simp))

/-- The prior is the average of the posteriors. -/
lemma integral_prior_eq (hf : IsPayoff f) :
    ∫ θ, f θ ∂S.prior = ∫ m, ∫ θ, f θ ∂S.posterior m ∂S.posteriorMeans.ν := by
  obtain ⟨B, hB⟩ := hf.bdd
  rw [show ∫ θ, f θ ∂S.prior = ∫ z, f z.1 ∂S.π from
    integral_map measurable_fst.aemeasurable hf.measurable.aestronglyMeasurable]
  exact (S.integral_posterior (F := fun z => f z.1) (hf.measurable.comp measurable_fst)
    ((integrable_const B).mono' (hf.measurable.comp measurable_fst).aestronglyMeasurable
      (S.state_mem.mono fun z hz => hB _ hz))).symm

/-- At almost every posterior mean, the posterior's expected state price covers `v`. -/
lemma ae_le_integral_posterior (hp : IsStatePrice v p) :
    ∀ᵐ m ∂S.posteriorMeans.ν, v m ≤ ∫ θ, p θ ∂S.posterior m := by
  filter_upwards [ae_posterior_mem, ae_integral_posterior_id] with m hm hmean
  simpa [hmean] using hp.le (S.posterior m) inferInstance hm

/-- **Theorem 1 (weak duality)** of Dworczak–Kolotilin: no signal beats the cost of a state
price. Each posterior is a belief with mean `m`, so `v m ≤ ∫ p d(posterior)`; average. -/
theorem value_le_statePrice (S : Signal) (hv : IsPayoff v) (hp : IsStatePrice v p) :
    S.value v ≤ ∫ θ, p θ ∂S.prior := by
  rw [S.value_eq hv, integral_prior_eq hp.isPayoff]
  exact integral_mono_ae (integrable_of_mem S.posteriorMeans.mem hv)
    (integrable_integral_posterior hp.isPayoff) (ae_le_integral_posterior hp)

end Signal

/-! ### Theorem 2 and Corollary 1 -/

/-- A price convex on `ℝ` is a state price: it is Lipschitz on `[0, 1]`, with constant the
slopes at the endpoints, and by Jensen `∫ p dν ≥ p(E_ν ω) ≥ v(E_ν ω)`. -/
lemma IsPrice.isStatePrice (hp : IsPrice v p) : IsStatePrice v p := by
  have hm := subgrad_mono hp.convex
  have hs : ∀ x ∈ Icc (0 : ℝ) 1, |subgrad p x| ≤ |subgrad p 0| + |subgrad p 1| := fun x hx =>
    abs_le.2 ⟨by linarith [neg_abs_le (subgrad p 0), abs_nonneg (subgrad p 1), hm hx.1],
      by linarith [le_abs_self (subgrad p 1), abs_nonneg (subgrad p 0), hm hx.2]⟩
  refine ⟨⟨_, LipschitzOnWith.of_le_add_mul' (|subgrad p 0| + |subgrad p 1|) fun x hx y _ => ?_⟩,
    hp.continuous.measurable, fun ν _ hν => ?_⟩
  · -- the supporting line at `x` bounds the drop from `x` to `y`
    have h1 := le_support hp.convex x y
    have h2 := mul_le_mul (hs x hx) (le_refl |x - y|) (abs_nonneg _) (by positivity)
    have h3 := neg_abs_le (subgrad p x * (y - x))
    rw [abs_mul, abs_sub_comm y x] at h3
    rw [Real.dist_eq]; linarith
  · -- Jensen: integrate the supporting line at the mean
    set m := ∫ x, x ∂ν
    have hid : Integrable (fun x : ℝ => x) ν :=
      integrable_of_mem hν (IsPayoff.of_continuous continuous_id)
    have hmI : m ∈ Icc (0 : ℝ) 1 := ⟨integral_nonneg_of_ae (hν.mono fun x h => h.1),
      by simpa using integral_mono_ae hid (integrable_const (1 : ℝ)) (hν.mono fun x h => h.2)⟩
    have hline : ∫ x, p m + subgrad p m * (x - m) ∂ν = p m := by
      have h1 : Integrable (fun x : ℝ => x - m) ν := hid.sub (integrable_const m)
      rw [integral_add (integrable_const _) (h1.const_mul _), integral_const_mul,
        integral_sub hid (integrable_const m)]
      simp [m]
    calc v m ≤ p m := hp.le m hmI
      _ = ∫ x, p m + subgrad p m * (x - m) ∂ν := hline.symm
      _ ≤ ∫ x, p x ∂ν := integral_mono_ae ((integrable_const _).add
          ((hid.sub (integrable_const m)).const_mul _))
          (integrable_of_mem hν (.of_continuous hp.continuous))
          (ae_of_all _ fun x => le_support hp.convex m x)

variable {μ : Measure ℝ} [IsProbabilityMeasure μ]

/-- **Theorem 2 (no duality gap and primal attainment)** of Dworczak–Kolotilin, for an upper
semicontinuous bounded `v`: some signal is optimal, and its value is the least cost of a state
price. -/
theorem exists_optimal_signal_stateValue (hμ : ∀ᵐ θ ∂μ, θ ∈ Icc (0 : ℝ) 1) (hv : IsPayoff v)
    (hvu : UpperSemicontinuous v) :
    ∃ S : Signal, S.prior = μ ∧ (∀ S' : Signal, S'.prior = μ → S'.value v ≤ S.value v) ∧
      S.value v = stateValue v μ := by
  obtain ⟨S, hS, hval, hopt⟩ := exists_optimal_signal hμ hv hvu
  obtain ⟨B, hB⟩ := exists_isPrice_const hv
  have : Nonempty {p // IsStatePrice v p} := ⟨⟨_, hB.isStatePrice⟩⟩
  have hbdd : BddBelow (range fun p : {p // IsStatePrice v p} => ∫ θ, p.1 θ ∂μ) :=
    ⟨S.value v, by rintro _ ⟨p, rfl⟩; exact hS ▸ S.value_le_statePrice hv p.2⟩
  -- `value ≤ stateValue` by weak duality; `stateValue ≤ priceValue = value` since prices are
  -- state prices
  refine ⟨S, hS, hopt, le_antisymm (le_ciInf fun p => hS ▸ S.value_le_statePrice hv p.2) ?_⟩
  rw [hval]
  obtain ⟨B', hB'⟩ := exists_isPrice_const hv
  have : Nonempty {p // IsPrice v p} := ⟨⟨_, hB'⟩⟩
  exact le_ciInf fun p => ciInf_le hbdd ⟨p.1, p.2.isStatePrice⟩

/-- Both optimal **if and only if no duality gap** between them: `value = ∫ p dμ`. -/
lemma optimal_iff_value_eq (hμ : ∀ᵐ θ ∂μ, θ ∈ Icc (0 : ℝ) 1) (hv : IsPayoff v)
    (hvu : UpperSemicontinuous v) {S : Signal} (hS : S.prior = μ) (hp : IsStatePrice v p) :
    ((∀ S' : Signal, S'.prior = μ → S'.value v ≤ S.value v) ∧
      ∀ q, IsStatePrice v q → ∫ θ, p θ ∂μ ≤ ∫ θ, q θ ∂μ) ↔ S.value v = ∫ θ, p θ ∂μ := by
  obtain ⟨S₀, hS₀, -, hval₀⟩ := exists_optimal_signal_stateValue hμ hv hvu
  obtain ⟨B, hB⟩ := exists_isPrice_const hv
  have : Nonempty {p // IsStatePrice v p} := ⟨⟨_, hB.isStatePrice⟩⟩
  refine ⟨fun ⟨hSopt, hpopt⟩ => le_antisymm (hS ▸ S.value_le_statePrice hv hp) ?_, fun h => ?_⟩
  · -- `∫ p dμ ≤ stateValue = value of S₀ ≤ value of S`
    have : ∫ θ, p θ ∂μ ≤ stateValue v μ := le_ciInf fun q => hpopt q.1 q.2
    linarith [hSopt S₀ hS₀]
  · -- no gap: optimality of both follows from weak duality
    exact ⟨fun S' hS' => h ▸ hS' ▸ S'.value_le_statePrice hv hp,
      fun q hq => h ▸ hS ▸ S.value_le_statePrice hv hq⟩

/-- **Corollary 1 (complementary slackness)** of Dworczak–Kolotilin: a signal and a state price
are both optimal if and only if the state price exactly covers `v` at almost every posterior,
`v m = ∫ p d(posterior after m)`. (DK state it for every posterior in the support; their proof
passes through this almost-everywhere form.) -/
theorem complementary_slackness (hμ : ∀ᵐ θ ∂μ, θ ∈ Icc (0 : ℝ) 1) (hv : IsPayoff v)
    (hvu : UpperSemicontinuous v) {S : Signal} (hS : S.prior = μ) (hp : IsStatePrice v p) :
    ((∀ S' : Signal, S'.prior = μ → S'.value v ≤ S.value v) ∧
      ∀ q, IsStatePrice v q → ∫ θ, p θ ∂μ ≤ ∫ θ, q θ ∂μ) ↔
    ∀ᵐ m ∂S.posteriorMeans.ν, v m = ∫ θ, p θ ∂S.posterior m := by
  rw [optimal_iff_value_eq hμ hv hvu hS hp]
  -- the gap `∫ p dμ - value` is the average of the nonnegative slack at each posterior
  have hgap : ∫ θ, p θ ∂μ - S.value v =
      ∫ m, (∫ θ, p θ ∂S.posterior m - v m) ∂S.posteriorMeans.ν := by
    rw [← hS, Signal.integral_prior_eq hp.isPayoff, S.value_eq hv,
      integral_sub (Signal.integrable_integral_posterior hp.isPayoff)
        (integrable_of_mem S.posteriorMeans.mem hv)]
  have hslack := integral_eq_zero_iff_of_nonneg_ae
    (Signal.ae_le_integral_posterior hp |>.mono fun m hm => sub_nonneg.2 hm)
    ((Signal.integrable_integral_posterior hp.isPayoff).sub
      (integrable_of_mem S.posteriorMeans.mem hv))
  constructor
  · intro h
    filter_upwards [hslack.1 (by rw [← hgap, h, sub_self])] with m hm
    simp only [Pi.zero_apply, sub_eq_zero] at hm; exact hm.symm
  · intro h
    have := integral_eq_zero_of_ae (h.mono fun m hm => by simp [hm] :
      (fun m => ∫ θ, p θ ∂S.posterior m - v m) =ᵐ[S.posteriorMeans.ν] 0)
    linarith

end MeanPersuasion
