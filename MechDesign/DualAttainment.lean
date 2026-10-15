/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import MechDesign.StatePrices
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Topology.ContinuousMap.Bounded.Normed

/-!
# Dworczak–Kolotilin, Theorem 3: when is the best state price attained?

For an upper semicontinuous bounded `v`, the following are equivalent
(`dual_attainment_tfae`, DK Theorem 3):
* (i) the dual (D) has an optimal state price;
* (ii) the concave closure `V̂` (`closure`) is *superdifferentiable* at the prior: some Lipschitz
  `p` has `V̂(μ₀) = ∫ p dμ₀` and `V̂(η) ≤ ∫ p dη` for every prior `η`;
* (iii) `V̂` has *bounded steepness* at the prior: `V̂(η) - V̂(μ₀) ≤ L ‖η - μ₀‖_KR`.

**Proof, following DK (Appendix A.5).** (i) ⇔ (ii) is their Lemma 6: an optimal state price is
a supergradient and conversely, by Theorem 2 at every prior. (ii) ⇒ (iii) is immediate.
(iii) ⇒ (ii) is **Gale's theorem** (`gale`): the hypograph of `V̂` and the open cone
`t > V̂(μ₀) + L ‖x - x₀‖` are disjoint convex sets, and a separating hyperplane is a supporting
hyperplane of slope at most `L`. DK work in `M(Ω)` with the Kantorovich–Rubinstein norm and
represent its dual by Lipschitz functions. We instead embed beliefs isometrically into the
Banach space of bounded functions on the `1`-Lipschitz test functions (`embed`), and read the
price off the supporting hyperplane at point masses: `p(ω) = H(δ_ω)`. A continuous linear map
commutes with the Bochner integral, so `H(η) = ∫ p dη`.
-/

open MeasureTheory Set ProbabilityTheory BoundedContinuousFunction

namespace MeanPersuasion

/-! ### Gale's theorem -/

section Gale

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A linear functional on `E × ℝ` in coordinates: `f (x, t) = f (x, 0) + t f (0, 1)`. -/
lemma apply_prod_eq (f : E × ℝ →L[ℝ] ℝ) (x : E) (t : ℝ) :
    f (x, t) = f (x, 0) + t * f (0, 1) := by
  rw [← smul_eq_mul, ← map_smul, ← map_add, Prod.smul_mk, smul_zero, smul_eq_mul, mul_one,
    Prod.mk_add_mk, add_zero, zero_add]

/-- The open cone strictly above `t₀ + L ‖x - x₀‖`. -/
def coneAbove (x₀ : E) (t₀ L : ℝ) : Set (E × ℝ) := {b | t₀ + L * ‖b.1 - x₀‖ < b.2}

omit [NormedSpace ℝ E] in
lemma isOpen_coneAbove (x₀ : E) (t₀ L : ℝ) : IsOpen (coneAbove x₀ t₀ L) :=
  isOpen_lt (continuous_const.add (continuous_const.mul
    ((continuous_fst.sub continuous_const).norm))) continuous_snd

lemma convex_coneAbove (x₀ : E) (t₀ : ℝ) {L : ℝ} (hL : 0 ≤ L) : Convex ℝ (coneAbove x₀ t₀ L) := by
  intro b hb c hc s t hs ht hst
  simp only [coneAbove, mem_ofPred_eq, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
    smul_eq_mul] at hb hc ⊢
  -- the norm is convex, and a convex combination of strict inequalities is strict
  have hn : ‖s • b.1 + t • c.1 - x₀‖ ≤ s * ‖b.1 - x₀‖ + t * ‖c.1 - x₀‖ :=
    calc ‖s • b.1 + t • c.1 - x₀‖ = ‖s • (b.1 - x₀) + t • (c.1 - x₀)‖ := by
          congr 1; rw [smul_sub, smul_sub, sub_add_sub_comm, ← add_smul, hst, one_smul]
      _ ≤ _ := (norm_add_le _ _).trans (by
          rw [norm_smul, norm_smul, Real.norm_of_nonneg hs, Real.norm_of_nonneg ht])
  have h1 := wavg_lt hs ht hst hb hc
  have h2 : s * (t₀ + L * ‖b.1 - x₀‖) + t * (t₀ + L * ‖c.1 - x₀‖) =
      t₀ + L * (s * ‖b.1 - x₀‖ + t * ‖c.1 - x₀‖) := by linear_combination t₀ * hst
  linarith [mul_le_mul_of_nonneg_left hn hL]

/-- A functional bounded above on a line through the origin vanishes on it. -/
lemma eq_zero_of_forall_lt (f : E × ℝ →L[ℝ] ℝ) {u : ℝ} (h : ∀ x : E, f (x, 0) < u) (x : E) :
    f (x, 0) = 0 := by
  have hk : ∀ k : ℝ, k * f (x, 0) < u := fun k => by
    have := h (k • x); rwa [show ((k • x, (0 : ℝ)) : E × ℝ) = k • (x, 0) by simp, map_smul,
      smul_eq_mul] at this
  have h1 := nonpos_of_forall_le (b := f (x, 0)) (u := u) fun k _ => (hk k).le
  have h2 := nonpos_of_forall_le (b := -f (x, 0)) (u := u) fun k _ => by linarith [hk (-k)]
  linarith

/-- **Gale's theorem** (Gale 1967): if a convex set `A` of points `(x, t)` lies below the cone
`t ≤ t₀ + L ‖x - x₀‖` and contains `(x₀, t₀)`, it lies below a hyperplane through `(x₀, t₀)`
whose slope has norm at most `L`. Separate `A` from the open cone above. -/
theorem gale {A : Set (E × ℝ)} (hA : Convex ℝ A) {x₀ : E} {t₀ L : ℝ} (hL : 0 ≤ L)
    (h₀ : (x₀, t₀) ∈ A) (hle : ∀ a ∈ A, a.2 ≤ t₀ + L * ‖a.1 - x₀‖) :
    ∃ H : E →L[ℝ] ℝ, (∀ a ∈ A, a.2 ≤ t₀ + H (a.1 - x₀)) ∧ ∀ x, H x ≤ L * ‖x‖ := by
  obtain ⟨f, u, hfB, hfA⟩ := geometric_hahn_banach_open (convex_coneAbove x₀ t₀ hL)
    (isOpen_coneAbove x₀ t₀ L) hA (Set.disjoint_left.2 fun a ha ha' => by
      have := hle a ha'; simp only [coneAbove, mem_ofPred_eq] at ha; linarith)
  set c := f (0, 1)
  -- in coordinates, the cone gives `f (x, 0) + t c < u` above `t₀ + L ‖x - x₀‖`
  have hB : ∀ x (s : ℝ), 0 < s → f (x, 0) + (t₀ + L * ‖x - x₀‖ + s) * c < u := fun x s hs => by
    rw [← apply_prod_eq]; exact hfB _ (by simp only [coneAbove, mem_ofPred_eq]; linarith)
  -- `c < 0`: pushing up in `t` gives `c ≤ 0`, and `c = 0` would make `f` vanish
  have hc0 : c ≤ 0 := Duality.nonpos_of_forall_lt (a := f (x₀, 0) + (t₀ + 1) * c) (u := u)
    fun s hs => by have := hB x₀ (1 + s) (by linarith); simp at this; linarith
  have hc : c < 0 := hc0.lt_of_ne fun hz => by
    have hzero := eq_zero_of_forall_lt f fun x => by
      have := hB x 1 one_pos; rwa [hz, mul_zero, add_zero] at this
    have h1 := hfA _ h₀; rw [apply_prod_eq, hzero, ← hz] at h1
    have h2 := hB x₀ 1 one_pos; rw [hzero, ← hz] at h2
    simp at h1 h2; linarith
  -- normalise: `H = f (·, 0) / (-c)`; then `t ≤ H x - u/(-c)` on `A` and `≥` on the cone
  set H : E →L[ℝ] ℝ := (-c)⁻¹ • f.comp (ContinuousLinearMap.inl ℝ E ℝ)
  have hH : ∀ x, H x = f (x, 0) / (-c) := fun x => by simp [H, div_eq_inv_mul]
  have hAle : ∀ a ∈ A, a.2 ≤ H a.1 - u / (-c) := fun a ha => by
    have := hfA a ha; rw [apply_prod_eq] at this
    rw [hH, ← sub_div, le_div_iff₀ (by linarith)]; linarith
  have hBle : ∀ x, H x - u / (-c) ≤ t₀ + L * ‖x - x₀‖ := fun x =>
    le_of_forall_pos_lt_add fun s hs => by
      have := hB x s hs
      rw [hH, ← sub_div, div_lt_iff₀ (by linarith)]; nlinarith
  have hx₀ : H x₀ - u / (-c) = t₀ := le_antisymm (by simpa using hBle x₀) (hAle _ h₀)
  refine ⟨H, fun a ha => ?_, fun x => ?_⟩
  · have := hAle a ha; rw [map_sub]; linarith
  · have := hBle (x₀ + x); rw [map_add, add_sub_cancel_left] at this; linarith

end Gale

/-! ### Beliefs as bounded functions on the Lipschitz test functions -/

/-- The `1`-Lipschitz test functions vanishing at `0`: the unit ball defining DK's
Kantorovich–Rubinstein norm (with `ω₀ = 0`). -/
def TestFn : Type := {f : ℝ → ℝ // LipschitzWith 1 f ∧ f 0 = 0}

instance : TopologicalSpace TestFn := ⊥

instance : DiscreteTopology TestFn := ⟨rfl⟩

lemma TestFn.abs_le (f : TestFn) (x : ℝ) : |f.1 x| ≤ |x| := by
  have := f.2.1.dist_le_mul x 0; simpa [f.2.2, Real.dist_eq] using this

lemma TestFn.continuous (f : TestFn) : Continuous f.1 := f.2.1.continuous

/-- The **Kantorovich–Rubinstein distance** between two beliefs (DK, Section 2; for
probability measures the mass term vanishes). -/
noncomputable def krDist (η μ : Measure ℝ) : ℝ := ⨆ f : TestFn, (∫ x, f.1 x ∂η - ∫ x, f.1 x ∂μ)

/-- The point mass at `ω`, as the bounded function `f ↦ f ω` (with `ω` clamped to `[0, 1]`). -/
noncomputable def delta (ω : ℝ) : TestFn →ᵇ ℝ :=
  mkOfDiscrete (fun f => f.1 (projIcc 0 1 zero_le_one ω)) 2 fun f g => by
    have h1 := f.abs_le (projIcc 0 1 zero_le_one ω)
    have h2 := g.abs_le (projIcc 0 1 zero_le_one ω)
    have h3 := abs_le_one_of_mem (projIcc 0 1 zero_le_one ω)
    rw [Real.dist_eq]; linarith [abs_sub (f.1 (projIcc 0 1 zero_le_one ω))
      (g.1 (projIcc 0 1 zero_le_one ω))]

@[simp] lemma delta_apply (ω : ℝ) (f : TestFn) : delta ω f = f.1 (projIcc 0 1 zero_le_one ω) := rfl

lemma norm_delta_sub_le (ω ω' : ℝ) : ‖delta ω - delta ω'‖ ≤ |ω - ω'| :=
  (norm_le (abs_nonneg _)).2 fun f => by
    simp only [coe_sub, Pi.sub_apply, delta_apply, Real.norm_eq_abs]
    exact (f.2.1.dist_le_mul _ _).trans (by
      simpa [Real.dist_eq, Subtype.dist_eq] using
        (LipschitzWith.projIcc zero_le_one).dist_le_mul ω ω')

lemma norm_delta_le (ω : ℝ) : ‖delta ω‖ ≤ 1 :=
  (norm_le zero_le_one).2 fun f => by
    simpa using (f.abs_le _).trans (abs_le_one_of_mem (projIcc 0 1 zero_le_one ω))

lemma continuous_delta : Continuous delta :=
  (LipschitzWith.of_dist_le_mul (K := 1) fun ω ω' => by
    simpa [dist_eq_norm, Real.dist_eq] using norm_delta_sub_le ω ω').continuous

lemma integrable_delta (η : Measure ℝ) [IsFiniteMeasure η] : Integrable delta η :=
  (integrable_const (1 : ℝ)).mono' continuous_delta.aestronglyMeasurable
    (ae_of_all _ norm_delta_le)

/-- **The embedding** of a belief: `embed η = ∫ δ_ω dη(ω)`, i.e. `f ↦ ∫ f dη`. -/
noncomputable def embed (η : Measure ℝ) : TestFn →ᵇ ℝ := ∫ ω, delta ω ∂η

lemma embed_apply {η : Measure ℝ} [IsFiniteMeasure η] (hη : ∀ᵐ x ∂η, x ∈ Icc (0 : ℝ) 1)
    (f : TestFn) : embed η f = ∫ x, f.1 x ∂η := by
  rw [embed, ← evalCLM_apply (𝕜 := ℝ), ← ContinuousLinearMap.integral_comp_comm _
    (integrable_delta η)]
  exact integral_congr_ae (hη.mono fun x hx => by simp [projIcc_of_mem _ hx])

/-- The Kantorovich–Rubinstein distance is at most the distance of the embeddings. -/
lemma krDist_le {η μ : Measure ℝ} [IsFiniteMeasure η] [IsFiniteMeasure μ]
    (hη : ∀ᵐ x ∂η, x ∈ Icc (0 : ℝ) 1) (hμ : ∀ᵐ x ∂μ, x ∈ Icc (0 : ℝ) 1) :
    krDist η μ ≤ ‖embed η - embed μ‖ := by
  have : Nonempty TestFn := ⟨⟨fun _ => 0, LipschitzWith.const' 0, rfl⟩⟩
  exact ciSup_le fun f => by
    rw [← embed_apply hη, ← embed_apply hμ]
    exact (le_abs_self _).trans (by simpa using norm_coe_le_norm (embed η - embed μ) f)

lemma embed_add {η₁ η₂ : Measure ℝ} [IsFiniteMeasure η₁] [IsFiniteMeasure η₂] :
    embed (η₁ + η₂) = embed η₁ + embed η₂ :=
  integral_add_measure (integrable_delta η₁) (integrable_delta η₂)

lemma embed_smul (η : Measure ℝ) {a : ℝ} (ha : 0 ≤ a) :
    embed (ENNReal.ofReal a • η) = a • embed η := by
  rw [embed, integral_smul_measure, ENNReal.toReal_ofReal ha]; rfl

/-! ### Mixing signals: the concave closure is concave -/

variable {v : ℝ → ℝ}

/-- **Mixing two signals**: with probability `a` run `S₁`, otherwise `S₂`. -/
noncomputable def Signal.mix (S₁ S₂ : Signal) {a : ℝ} (ha : a ∈ Icc (0 : ℝ) 1) : Signal where
  π := ENNReal.ofReal a • S₁.π + ENNReal.ofReal (1 - a) • S₂.π
  isProb := ⟨by
    simp only [Measure.add_apply, Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
    rw [← ENNReal.ofReal_add ha.1 (by linarith [ha.2]), add_sub_cancel, ENNReal.ofReal_one]⟩
  state_mem := ae_add_measure_iff.2 ⟨Measure.smul_absolutelyContinuous.ae_le S₁.state_mem,
    Measure.smul_absolutelyContinuous.ae_le S₂.state_mem⟩
  mean_mem := ae_add_measure_iff.2 ⟨Measure.smul_absolutelyContinuous.ae_le S₁.mean_mem,
    Measure.smul_absolutelyContinuous.ae_le S₂.mean_mem⟩
  mean_eq g hg C hC := by
    have i := fun (S : Signal) (q : ℝ × ℝ → ℝ) (hq : Continuous q)
      (hm : ∀ᵐ z ∂S.π, q z ∈ Icc (0 : ℝ) 1) (c : ENNReal) (hc : c ≠ ⊤) =>
      (S.integrable_mul hq hm hg hC).smul_measure hc
    rw [integral_add_measure (i S₁ _ continuous_fst S₁.state_mem _ ENNReal.ofReal_ne_top)
        (i S₂ _ continuous_fst S₂.state_mem _ ENNReal.ofReal_ne_top),
      integral_add_measure (i S₁ _ continuous_snd S₁.mean_mem _ ENNReal.ofReal_ne_top)
        (i S₂ _ continuous_snd S₂.mean_mem _ ENNReal.ofReal_ne_top),
      integral_smul_measure, integral_smul_measure, integral_smul_measure, integral_smul_measure,
      S₁.mean_eq g hg C hC, S₂.mean_eq g hg C hC]

section mix

variable {S₁ S₂ : Signal} {a : ℝ} (ha : a ∈ Icc (0 : ℝ) 1)
include ha

lemma Signal.mix_prior : (S₁.mix S₂ ha).prior =
    ENNReal.ofReal a • S₁.prior + ENNReal.ofReal (1 - a) • S₂.prior := by
  simp only [Signal.prior, Signal.mix, Measure.map_add _ _ measurable_fst]
  rw [Measure.map_smul _ measurable_fst.aemeasurable,
    Measure.map_smul _ measurable_fst.aemeasurable]

lemma Signal.mix_value (hv : IsPayoff v) :
    (S₁.mix S₂ ha).value v = a * S₁.value v + (1 - a) * S₂.value v := by
  have i := fun (S : Signal) => (S.integrable_payoff hv).smul_measure
    (ENNReal.ofReal_ne_top (r := a))
  simp only [Signal.value, Signal.mix]
  rw [integral_add_measure ((S₁.integrable_payoff hv).smul_measure ENNReal.ofReal_ne_top)
      ((S₂.integrable_payoff hv).smul_measure ENNReal.ofReal_ne_top),
    integral_smul_measure, integral_smul_measure, ENNReal.toReal_ofReal ha.1,
    ENNReal.toReal_ofReal (by linarith [ha.2]), smul_eq_mul, smul_eq_mul]

end mix

/-- The **concave closure** `V̂(η)` of DK: the value of persuasion at the prior `η`. -/
noncomputable def concaveClosure (v : ℝ → ℝ) (η : Measure ℝ) : ℝ :=
  ⨆ S : {S : Signal // S.prior = η}, S.1.value v

section closure

variable {η : Measure ℝ} [IsProbabilityMeasure η] (hη : ∀ᵐ x ∂η, x ∈ Icc (0 : ℝ) 1)
  (hv : IsPayoff v) (hvu : UpperSemicontinuous v)
include hη hv hvu

/-- The concave closure is attained, and equals the dual value (Theorem 2). -/
lemma concaveClosure_spec : ∃ S : Signal, S.prior = η ∧ S.value v = concaveClosure v η ∧
    (∀ S' : Signal, S'.prior = η → S'.value v ≤ concaveClosure v η) ∧
    concaveClosure v η = stateValue v η := by
  obtain ⟨S, hS, hopt, hval⟩ := exists_optimal_signal_stateValue hη hv hvu
  have : Nonempty {S : Signal // S.prior = η} := ⟨⟨S, hS⟩⟩
  have hc : concaveClosure v η = S.value v :=
    le_antisymm (ciSup_le fun S' => hopt S'.1 S'.2)
      (le_ciSup (f := fun S' : {S : Signal // S.prior = η} => S'.1.value v)
        ⟨S.value v, by rintro _ ⟨S', rfl⟩; exact hopt S'.1 S'.2⟩ ⟨S, hS⟩)
  exact ⟨S, hS, hc.symm, fun S' hS' => hc ▸ hopt S' hS', hc.trans hval⟩

/-- No disclosure is worth `v` of the mean, so `v(E_η ω) ≤ V̂(η)`. -/
lemma le_concaveClosure : v (∫ x, x ∂η) ≤ concaveClosure v η := by
  obtain ⟨S, -, -, hle, -⟩ := concaveClosure_spec hη hv hvu
  have hval : (silent hη).value v = v (priorMean η) := by
    rw [Signal.value, show (silent hη).π = η.map fun θ => (θ, priorMean η) from rfl,
      integral_map (φ := fun θ => (θ, priorMean η)) (by fun_prop)
        (f := fun z : ℝ × ℝ => v z.2) (hv.measurable.comp measurable_snd).aestronglyMeasurable]
    simp
  exact hval ▸ hle _ (silent_prior hη)

end closure

/-! ### Theorem 3 -/

/-- `V̂` is **superdifferentiable** at `μ` (DK, Section 3): a Lipschitz price `p` touches `V̂`
from above at `μ`, `V̂(μ) = ∫ p dμ` and `V̂(η) ≤ ∫ p dη` for every prior `η`. -/
def Superdifferentiable (v : ℝ → ℝ) (μ : Measure ℝ) : Prop :=
  ∃ p : ℝ → ℝ, (∃ K, LipschitzOnWith K p (Icc 0 1)) ∧ Measurable p ∧
    concaveClosure v μ = ∫ x, p x ∂μ ∧ ∀ η : Measure ℝ, IsProbabilityMeasure η →
      (∀ᵐ x ∂η, x ∈ Icc (0 : ℝ) 1) → concaveClosure v η ≤ ∫ x, p x ∂η

/-- `V̂` has **bounded steepness** at `μ` (DK, after Gale 1967): moving the prior raises the
value at most in proportion to the Kantorovich–Rubinstein distance. -/
def BoundedSteepness (v : ℝ → ℝ) (μ : Measure ℝ) : Prop :=
  ∃ L : ℝ, ∀ η : Measure ℝ, IsProbabilityMeasure η → (∀ᵐ x ∂η, x ∈ Icc (0 : ℝ) 1) →
    concaveClosure v η - concaveClosure v μ ≤ L * krDist η μ

/-- **The price read off a hyperplane** `H` through `(μ, c)`: the state `ω` costs the height of
the hyperplane at its point mass, `c + H(δ_ω - μ)`. -/
noncomputable def hyperplanePrice (c : ℝ) (H : (TestFn →ᵇ ℝ) →L[ℝ] ℝ) (μ : Measure ℝ)
    (ω : ℝ) : ℝ :=
  c + H (delta ω - embed μ)

section hyperplanePrice

variable {c : ℝ} {H : (TestFn →ᵇ ℝ) →L[ℝ] ℝ} {μ : Measure ℝ}

/-- A hyperplane of slope at most `K` gives a `K`-Lipschitz price, as point masses `δ_x, δ_y` are
at most `|x - y|` apart. -/
lemma lipschitzWith_hyperplanePrice {K : ℝ} (hK : 0 ≤ K) (hH : ∀ x, |H x| ≤ K * ‖x‖) :
    LipschitzWith (Real.toNNReal K) (hyperplanePrice c H μ) :=
  LipschitzWith.of_le_add_mul' K fun x y => by
    have := hH (delta x - delta y)
    have := norm_delta_sub_le x y
    simp only [hyperplanePrice, map_sub, Real.dist_eq] at *
    nlinarith [le_abs_self (H (delta x) - H (delta y))]

/-- A linear map commutes with the integral: the price costs `c + H(η - μ)` under `η`. -/
lemma integral_hyperplanePrice (η : Measure ℝ) [IsProbabilityMeasure η] :
    ∫ ω, hyperplanePrice c H μ ω ∂η = c + H (embed η - embed μ) := by
  have hHi : Integrable (fun ω => H (delta ω)) η := H.integrable_comp (integrable_delta η)
  have h2 : Integrable (fun ω => H (delta ω) - H (embed μ)) η := hHi.sub (integrable_const _)
  simp only [hyperplanePrice, map_sub]
  rw [integral_add (integrable_const _) h2,
    integral_sub hHi (integrable_const _), H.integral_comp_comm (integrable_delta η)]
  simp [embed]

end hyperplanePrice

variable {μ : Measure ℝ} [IsProbabilityMeasure μ] (hμ : ∀ᵐ x ∂μ, x ∈ Icc (0 : ℝ) 1)
  (hv : IsPayoff v) (hvu : UpperSemicontinuous v)
include hμ hv hvu

omit hvu in
/-- Every state price costs at least the dual value: the costs are bounded below by the value of
the uninformative signal. -/
lemma stateValue_le {p : ℝ → ℝ} (hp : IsStatePrice v p) : stateValue v μ ≤ ∫ x, p x ∂μ :=
  ciInf_le ⟨(silent hμ).value v, by
    rintro _ ⟨q, rfl⟩
    exact ((silent hμ).value_le_statePrice hv q.2).trans_eq (by rw [silent_prior hμ])⟩
    (⟨p, hp⟩ : {p // IsStatePrice v p})

/-- (i) ⇒ (ii), DK Lemma 6: an optimal state price is a supergradient. -/
lemma superdifferentiable_of_optimal {p : ℝ → ℝ} (hp : IsStatePrice v p)
    (hopt : ∫ x, p x ∂μ = stateValue v μ) : Superdifferentiable v μ := by
  obtain ⟨-, -, -, -, h⟩ := concaveClosure_spec hμ hv hvu
  refine ⟨p, hp.lipschitz, hp.measurable, h.trans hopt.symm, fun η _ hη => ?_⟩
  obtain ⟨-, -, -, -, hη'⟩ := concaveClosure_spec hη hv hvu
  exact hη' ▸ stateValue_le hη hv hp

/-- (ii) ⇒ (i), DK Lemma 6: a supergradient is an optimal state price. -/
lemma optimal_of_superdifferentiable (h : Superdifferentiable v μ) :
    ∃ p, IsStatePrice v p ∧ ∫ x, p x ∂μ = stateValue v μ := by
  obtain ⟨p, hK, hm, heq, hle⟩ := h
  obtain ⟨-, -, -, -, h⟩ := concaveClosure_spec hμ hv hvu
  -- `v(E_ν ω) ≤ V̂(ν) ≤ ∫ p dν`: a supergradient is a state price
  exact ⟨p, ⟨hK, hm, fun ν _ hν => (le_concaveClosure hν hv hvu).trans (hle ν inferInstance hν)⟩,
    heq.symm.trans h⟩

omit hv hvu in
/-- A difference of expectations is bounded by the norm of the embedded difference. -/
lemma integral_sub_le_norm {η : Measure ℝ} [IsProbabilityMeasure η]
    (hη : ∀ᵐ x ∂η, x ∈ Icc (0 : ℝ) 1) (f : TestFn) :
    ∫ x, f.1 x ∂η - ∫ x, f.1 x ∂μ ≤ ‖embed η - embed μ‖ := by
  rw [← embed_apply hη, ← embed_apply hμ]
  exact (le_abs_self _).trans (by simpa using norm_coe_le_norm (embed η - embed μ) f)

omit hv hvu in
lemma le_krDist {η : Measure ℝ} [IsProbabilityMeasure η] (hη : ∀ᵐ x ∂η, x ∈ Icc (0 : ℝ) 1)
    (f : TestFn) : ∫ x, f.1 x ∂η - ∫ x, f.1 x ∂μ ≤ krDist η μ :=
  le_ciSup ⟨_, by rintro _ ⟨g, rfl⟩; exact integral_sub_le_norm hμ hη g⟩ f

omit hμ hv hvu in
/-- A function Lipschitz on `[0, 1]`, extended by its endpoint values, is Lipschitz on `ℝ`. -/
lemma lipschitzWith_extend {p : ℝ → ℝ} {K : NNReal} (hK : LipschitzOnWith K p (Icc 0 1)) :
    LipschitzWith K fun x => p (projIcc (0 : ℝ) 1 zero_le_one x) :=
  LipschitzWith.of_dist_le_mul fun x y => (hK.dist_le_mul _ (projIcc (0 : ℝ) 1 _ x).2 _
    (projIcc (0 : ℝ) 1 _ y).2).trans (mul_le_mul_of_nonneg_left (by
      simpa [Subtype.dist_eq] using (LipschitzWith.projIcc (zero_le_one' ℝ)).dist_le_mul x y)
      K.2)

omit hμ hv hvu in
/-- An `L`-Lipschitz function, recentred at `0` and divided by `L > 0`, is a test function. -/
noncomputable def TestFn.ofLip {P : ℝ → ℝ} {L : ℝ} (hP : ∀ x y, P x ≤ P y + L * |x - y|) (hL : 0 < L) :
    TestFn :=
  ⟨fun x => (P x - P 0) / L, LipschitzWith.of_dist_le_mul fun x y => by
    have h2 := hP y x
    rw [abs_sub_comm] at h2
    rw [Real.dist_eq, Real.dist_eq, ← sub_div, sub_sub_sub_cancel_right, abs_div,
      abs_of_pos hL, NNReal.coe_one, one_mul, div_le_iff₀ hL, _root_.abs_le]
    constructor <;> linarith [hP x y], by simp⟩

omit hv hvu in
/-- **An `L`-Lipschitz price moves by at most `L` times the distance**: rescaled, it is a test
function. -/
lemma integral_sub_le_mul_krDist {P : ℝ → ℝ} {L : ℝ} (hP : ∀ x y, P x ≤ P y + L * |x - y|)
    {η : Measure ℝ} [IsProbabilityMeasure η] (hη : ∀ᵐ x ∂η, x ∈ Icc (0 : ℝ) 1) :
    ∫ x, P x ∂η - ∫ x, P x ∂μ ≤ L * krDist η μ := by
  have hL : 0 ≤ L := by
    have h1 := hP 0 1
    have h2 := hP 1 0
    norm_num at h1 h2; linarith
  rcases hL.eq_or_lt with rfl | hL
  · -- a `0`-Lipschitz price is constant
    have hc : P = fun _ => P 0 := funext fun x => le_antisymm (by simpa using hP x 0)
      (by simpa using hP 0 x)
    rw [hc]; simp
  have hPc : Continuous P :=
    (LipschitzWith.of_le_add_mul' L fun x y => by simpa [Real.dist_eq] using hP x y).continuous
  set f := TestFn.ofLip hP hL
  have hint : ∀ ν : Measure ℝ, IsProbabilityMeasure ν → (∀ᵐ x ∂ν, x ∈ Icc (0 : ℝ) 1) →
      ∫ x, f.1 x ∂ν = (∫ x, P x ∂ν - P 0) / L := fun ν _ hν => by
    simp only [f, TestFn.ofLip]
    rw [integral_div, integral_sub (integrable_of_mem hν (.of_continuous hPc))
      (integrable_const _), integral_const]
    simp
  have h1 := le_krDist hμ hη f
  rw [hint η inferInstance hη, hint μ inferInstance hμ, ← sub_div, sub_sub_sub_cancel_right,
    div_le_iff₀ hL] at h1
  linarith

omit hv hvu in
/-- (ii) ⇒ (iii): a `K`-Lipschitz supergradient bounds the steepness by `K`. -/
lemma boundedSteepness_of_superdifferentiable (h : Superdifferentiable v μ) :
    BoundedSteepness v μ := by
  obtain ⟨p, ⟨K, hK⟩, -, heq, hle⟩ := h
  -- extend `p` from `[0, 1]` by its endpoint values; integrals do not change
  set P := fun x => p (projIcc (0 : ℝ) 1 zero_le_one x)
  have hP := lipschitzWith_extend hK
  have hint : ∀ η : Measure ℝ, (∀ᵐ x ∂η, x ∈ Icc (0 : ℝ) 1) → ∫ x, P x ∂η = ∫ x, p x ∂η :=
    fun η hη => integral_congr_ae (hη.mono fun x hx => by simp [P, projIcc_of_mem _ hx])
  refine ⟨K, fun η _ hη => ?_⟩
  have := integral_sub_le_mul_krDist hμ (P := P) (L := K) (fun x y => by
    have := hP.dist_le_mul x y
    rw [Real.dist_eq, Real.dist_eq] at this
    linarith [le_abs_self (P x - P y)]) hη
  rw [hint η hη, hint μ hμ] at this
  linarith [hle η inferInstance hη, heq]

/-- The **hypograph** of `V̂` in the embedded space: pairs `(embed η, t)` with `t ≤ V̂(η)`. -/
def hypograph (v : ℝ → ℝ) : Set ((TestFn →ᵇ ℝ) × ℝ) :=
  {a | ∃ η : Measure ℝ, IsProbabilityMeasure η ∧ (∀ᵐ x ∂η, x ∈ Icc (0 : ℝ) 1) ∧
    a.1 = embed η ∧ a.2 ≤ concaveClosure v η}

omit hμ in
/-- The hypograph is convex, because mixing optimal signals shows `V̂` is concave. -/
lemma convex_hypograph : Convex ℝ (hypograph v) := by
  rintro ⟨_, t₁⟩ ⟨η₁, _, hη₁, rfl, ht₁⟩ ⟨_, t₂⟩ ⟨η₂, _, hη₂, rfl, ht₂⟩ a b ha hb hab
  have ha1 : a ∈ Icc (0 : ℝ) 1 := ⟨ha, by linarith⟩
  have hb' : b = 1 - a := by linarith
  subst hb'
  obtain ⟨S₁, hS₁, hv₁, -⟩ := concaveClosure_spec hη₁ hv hvu
  obtain ⟨S₂, hS₂, hv₂, -⟩ := concaveClosure_spec hη₂ hv hvu
  set η := ENNReal.ofReal a • η₁ + ENNReal.ofReal (1 - a) • η₂
  have hprior : (S₁.mix S₂ ha1).prior = η := by rw [Signal.mix_prior, hS₁, hS₂]
  have : IsProbabilityMeasure η := ⟨by
    simp only [η, Measure.add_apply, Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
    rw [← ENNReal.ofReal_add ha (by linarith), add_sub_cancel, ENNReal.ofReal_one]⟩
  have hη : ∀ᵐ x ∂η, x ∈ Icc (0 : ℝ) 1 := ae_add_measure_iff.2
    ⟨Measure.smul_absolutelyContinuous.ae_le hη₁, Measure.smul_absolutelyContinuous.ae_le hη₂⟩
  obtain ⟨-, -, -, hle, -⟩ := concaveClosure_spec hη hv hvu
  refine ⟨η, inferInstance, hη, ?_, ?_⟩
  · have : IsFiniteMeasure (ENNReal.ofReal a • η₁) := Measure.smul_finite _ ENNReal.ofReal_ne_top
    have : IsFiniteMeasure (ENNReal.ofReal (1 - a) • η₂) :=
      Measure.smul_finite _ ENNReal.ofReal_ne_top
    simp only [Prod.fst_add, Prod.smul_fst, η]
    rw [embed_add, embed_smul _ ha, embed_smul _ (show (0 : ℝ) ≤ 1 - a by linarith)]
  · have := hle _ hprior
    rw [Signal.mix_value ha1 hv, hv₁, hv₂] at this
    simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul]
    nlinarith [mul_le_mul_of_nonneg_left ht₁ ha, mul_le_mul_of_nonneg_left ht₂
      (show (0 : ℝ) ≤ 1 - a by linarith)]

/-- (iii) ⇒ (ii), **Gale's theorem**: bounded steepness gives a Lipschitz supergradient, read off
the supporting hyperplane at point masses, `p(ω) = V̂(μ) + H(δ_ω - μ)`. -/
lemma superdifferentiable_of_boundedSteepness (h : BoundedSteepness v μ) :
    Superdifferentiable v μ := by
  obtain ⟨L, hL⟩ := h
  set L' := max L 0
  have hkr : ∀ η : Measure ℝ, IsProbabilityMeasure η → (∀ᵐ x ∂η, x ∈ Icc (0 : ℝ) 1) →
      0 ≤ krDist η μ := fun η _ hη => by
    simpa using le_krDist hμ hη ⟨fun _ => 0, LipschitzWith.const' 0, rfl⟩
  obtain ⟨H, hH, hHL⟩ := gale (convex_hypograph hv hvu) (le_max_right L 0)
    (⟨μ, inferInstance, hμ, rfl, le_rfl⟩ : (embed μ, concaveClosure v μ) ∈ hypograph v)
    (by
      rintro ⟨_, t⟩ ⟨η, _, hη, rfl, ht⟩
      have := hL η inferInstance hη
      have := mul_le_mul_of_nonneg_right (le_max_left L 0) (hkr η inferInstance hη)
      have := mul_le_mul_of_nonneg_left (krDist_le hη hμ) (le_max_right L 0)
      simp only at ht ⊢; linarith)
  -- the price `p(ω) = V̂(μ) + H(δ_ω - μ)` is `L'`-Lipschitz, and integrates to `V̂(μ) + H(η - μ)`
  have hHL' : ∀ x, H x ≤ L' * ‖x‖ := hHL
  have hpl := lipschitzWith_hyperplanePrice (c := concaveClosure v μ) (μ := μ) (le_max_right L 0)
    fun x => abs_le.2 ⟨by have := hHL' (-x); rw [map_neg, norm_neg] at this; linarith, hHL' x⟩
  refine ⟨_, ⟨_, hpl.lipschitzOnWith⟩, hpl.continuous.measurable,
    by simp [integral_hyperplanePrice], fun η _ hη => ?_⟩
  rw [integral_hyperplanePrice]
  simpa using hH (embed η, concaveClosure v η) ⟨η, inferInstance, hη, rfl, le_rfl⟩

/-- **Theorem 3 (dual attainment)** of Dworczak–Kolotilin: for a bounded upper semicontinuous
payoff, the dual (D) has an optimal state price if and only if the concave closure is
superdifferentiable at the prior, if and only if it has bounded steepness there. -/
theorem dual_attainment_tfae :
    [∃ p, IsStatePrice v p ∧ ∫ x, p x ∂μ = stateValue v μ, Superdifferentiable v μ,
      BoundedSteepness v μ].TFAE := by
  tfae_have 1 → 2 := fun ⟨p, hp, hopt⟩ => superdifferentiable_of_optimal hμ hv hvu hp hopt
  tfae_have 2 → 1 := optimal_of_superdifferentiable hμ hv hvu
  tfae_have 2 → 3 := boundedSteepness_of_superdifferentiable hμ
  tfae_have 3 → 2 := superdifferentiable_of_boundedSteepness hμ hv hvu
  tfae_finish

end MeanPersuasion
