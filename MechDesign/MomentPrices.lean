/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import MechDesign.DualAttainment
import MechDesign.PriceAttainment
import Mathlib.MeasureTheory.Measure.Support

/-!
# Dworczak–Kolotilin, Section 4: prices for moments

One-dimensional moment persuasion: states and posterior means lie in `X = [0, 1]`, and the
payoff `v` is `L`-Lipschitz on `[0, 1]`.

* **Corollary 2** (`exists_optimal_statePrice`): the dual (D) has an optimal state price.
* **Lemma 7** (`IsStatePrice.exists_line`): through every point `(x, v x)` passes a line of
  slope in `[-L, L]` that stays below a given state price on `[0, 1]`.
* **Theorem 5** (`momentPrice_spec`, with converses `optimal_of_momentPrice` and
  `optimal_of_momentSlope`): an optimal state price `p` extends from the support of the prior
  to a convex `L`-Lipschitz price for moments `pM ≥ v` (DK's `p̄`). This price is a supremum
  of lines `v x + q x (y - x)` with `|q| ≤ L`. Every optimal signal pays `∫ pM dμ₀` and has its
  states on these lines; either property alone certifies optimality.
* **Theorem 4** (`concaveClosure_lip`): the concave closure is `L`-Lipschitz in the
  Kantorovich–Rubinstein distance, so it has bounded steepness.

**Proof.** DK prove Theorem 4 first, by perturbing posteriors, and obtain Corollary 2 from
Theorem 3. In one dimension we go the other way round. Corollary 2 is the attainment of the
best convex price (`exists_optimal_price`), because convex prices are state prices and the two
dual values agree. For Lemma 7, DK separate `(x, v x)` from the epigraph of the convex roof and
project onto the set of supporting slopes. On the line, two-point beliefs show that every
secant from the left lies below every secant to the right, so the steepest left secant is a
slope. The hull of these lines is a price, and its clamped right derivative is a measurable `q`
(DK use the measurable maximum theorem). Theorem 4 then follows from Theorem 5: `pM` is an
`L`-Lipschitz supergradient at every prior.
-/

open MeasureTheory Set unitInterval BoundedContinuousFunction Filter Topology

namespace MeanPersuasion

variable {v p : ℝ → ℝ} {L : ℝ}

/-! ### Only the payoff on `[0, 1]` matters -/

section congr

variable {w : ℝ → ℝ} (h : EqOn v w (Icc 0 1))
include h

omit h in
/-- A state price for `v` is one for any payoff equal to `v` on `[0, 1]`. -/
lemma isStatePrice_of_eqOn (h : EqOn v w (Icc 0 1)) (hp : IsStatePrice v p) :
    IsStatePrice w p :=
  ⟨hp.lipschitz, hp.measurable, fun ν _ hν =>
    (h (priorMean_mem hν)).symm.trans_le (hp.le ν inferInstance hν)⟩

lemma isStatePrice_congr : IsStatePrice v = IsStatePrice w :=
  funext fun _ => propext ⟨isStatePrice_of_eqOn h, isStatePrice_of_eqOn h.symm⟩

lemma isPrice_congr : IsPrice v = IsPrice w :=
  funext fun _ => propext ⟨fun hp => ⟨hp.convex, fun x hx => (h hx).symm.trans_le (hp.le x hx)⟩,
    fun hp => ⟨hp.convex, fun x hx => (h hx).trans_le (hp.le x hx)⟩⟩

lemma Signal.value_congr (S : Signal) : S.value v = S.value w :=
  integral_congr_ae (S.mean_mem.mono fun _ hz => h hz)

lemma stateValue_congr (μ : Measure ℝ) : stateValue v μ = stateValue w μ := by
  rw [stateValue, stateValue, isStatePrice_congr h]

lemma priceValue_congr (μ : Measure ℝ) : priceValue v μ = priceValue w μ := by
  rw [priceValue, priceValue, isPrice_congr h]

lemma concaveClosure_congr (η : Measure ℝ) : concaveClosure v η = concaveClosure w η := by
  simp only [concaveClosure, Signal.value_congr h]

end congr

/-- `v` extended from `[0, 1]` by its endpoint values. -/
noncomputable def extendI (v : ℝ → ℝ) (x : ℝ) : ℝ := v (projIcc (0 : ℝ) 1 zero_le_one x)

lemma eqOn_extendI : EqOn v (extendI v) (Icc 0 1) := fun x hx => by
  simp [extendI, projIcc_of_mem _ hx]

section lip

variable (hLip : ∀ x ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (0 : ℝ) 1, v y ≤ v x + L * |x - y|)
include hLip

/-- A payoff Lipschitz on `[0, 1]` extends to a continuous one; this is what makes the
upper semicontinuous theory (Theorems 2 and 3) apply. -/
lemma continuous_extendI : Continuous (extendI v) :=
  (lipschitzWith_extend (LipschitzOnWith.of_dist_le' (K := L) fun x hx y hy => by
    have h1 := hLip y hy x hx
    have h2 := hLip x hx y hy
    rw [abs_sub_comm] at h1
    rw [Real.dist_eq, Real.dist_eq, abs_le]; constructor <;> linarith)).continuous

variable {μ : Measure ℝ} [IsProbabilityMeasure μ] (hμ : ∀ᵐ θ ∂μ, θ ∈ Icc (0 : ℝ) 1)
include hμ

/-- **Theorem 2** of DK for a payoff Lipschitz on `[0, 1]`. -/
lemma exists_optimal_signal_of_lip :
    ∃ S : Signal, S.prior = μ ∧ (∀ S' : Signal, S'.prior = μ → S'.value v ≤ S.value v) ∧
      S.value v = stateValue v μ := by
  have hc := continuous_extendI hLip
  have hw := eqOn_extendI (v := v)
  obtain ⟨S, hS, hopt, hval⟩ :=
    exists_optimal_signal_stateValue hμ (.of_continuous hc) hc.upperSemicontinuous
  refine ⟨S, hS, fun S' hS' => ?_, ?_⟩
  · rw [Signal.value_congr hw S', Signal.value_congr hw S]; exact hopt S' hS'
  · rw [Signal.value_congr hw S, stateValue_congr hw]; exact hval

/-- The best state price and the best convex price cost the same. -/
lemma stateValue_eq_priceValue_of_lip : stateValue v μ = priceValue v μ := by
  have hc := continuous_extendI hLip
  rw [stateValue_congr eqOn_extendI, priceValue_congr eqOn_extendI]
  obtain ⟨S, hS, hval, hopt⟩ := exists_optimal_signal hμ (.of_continuous hc) hc.upperSemicontinuous
  obtain ⟨S', hS', hopt', hval'⟩ :=
    exists_optimal_signal_stateValue hμ (.of_continuous hc) hc.upperSemicontinuous
  rw [← hval, ← hval']
  exact le_antisymm (hopt S' hS') (hopt' S hS)

lemma concaveClosure_eq_of_lip : concaveClosure v μ = stateValue v μ := by
  have hc := continuous_extendI hLip
  rw [concaveClosure_congr eqOn_extendI, stateValue_congr eqOn_extendI]
  obtain ⟨-, -, -, -, h⟩ := concaveClosure_spec hμ (.of_continuous hc) hc.upperSemicontinuous
  exact h

/-- **Corollary 2 (strong duality)** of DK, in one dimension: for a payoff that is Lipschitz on
`[0, 1]`, some state price is optimal for the dual (D). -/
theorem exists_optimal_statePrice (hv : IsPayoff v) :
    ∃ p, IsStatePrice v p ∧ ∫ x, p x ∂μ = stateValue v μ := by
  obtain ⟨p, hp, hcost⟩ := exists_optimal_price hμ hv hLip
  exact ⟨p, hp.isStatePrice, hcost.trans (stateValue_eq_priceValue_of_lip hLip hμ).symm⟩

/-- An optimal signal achieves the dual value. -/
lemma Signal.value_eq_stateValue_of_lip (hv : IsPayoff v) {S : Signal} (hS : S.prior = μ)
    (hopt : ∀ S' : Signal, S'.prior = μ → S'.value v ≤ S.value v) :
    S.value v = stateValue v μ := by
  obtain ⟨S₀, hS₀, -, hval⟩ := exists_optimal_signal_of_lip hLip hμ
  obtain ⟨B, hB⟩ := exists_isPrice_const hv
  have : Nonempty {p // IsStatePrice v p} := ⟨⟨_, hB.isStatePrice⟩⟩
  exact le_antisymm (le_ciInf fun q => hS ▸ S.value_le_statePrice hv q.2)
    (hval ▸ hopt S₀ hS₀)

end lip

/-! ### Lemma 7: supporting lines through `v` -/

/-- The belief that puts weight `a` on `y` and `1 - a` on `z`. -/
noncomputable def twoPoint (a y z : ℝ) : Measure ℝ :=
  ENNReal.ofReal a • Measure.dirac y + ENNReal.ofReal (1 - a) • Measure.dirac z

section twoPoint

variable {a : ℝ} (ha : a ∈ Icc (0 : ℝ) 1) (y z : ℝ)
include ha

lemma integral_twoPoint (f : ℝ → ℝ) :
    ∫ x, f x ∂twoPoint a y z = a * f y + (1 - a) * f z := by
  have hi : ∀ t, Integrable f (Measure.dirac t) := fun _ => integrable_dirac enorm_lt_top
  rw [twoPoint, integral_add_measure ((hi y).smul_measure ENNReal.ofReal_ne_top)
      ((hi z).smul_measure ENNReal.ofReal_ne_top), integral_smul_measure, integral_smul_measure,
    integral_dirac, integral_dirac, ENNReal.toReal_ofReal ha.1,
    ENNReal.toReal_ofReal (by linarith [ha.2]), smul_eq_mul, smul_eq_mul]

lemma isProbabilityMeasure_twoPoint : IsProbabilityMeasure (twoPoint a y z) := ⟨by
  simp only [twoPoint, Measure.add_apply, Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_add ha.1 (by linarith [ha.2]), add_sub_cancel, ENNReal.ofReal_one]⟩

omit ha in
lemma twoPoint_mem (hy : y ∈ Icc (0 : ℝ) 1) (hz : z ∈ Icc (0 : ℝ) 1) :
    ∀ᵐ x ∂twoPoint a y z, x ∈ Icc (0 : ℝ) 1 :=
  ae_add_measure_iff.2
    ⟨Measure.smul_absolutelyContinuous.ae_le ((ae_dirac_iff measurableSet_Icc).2 hy),
      Measure.smul_absolutelyContinuous.ae_le ((ae_dirac_iff measurableSet_Icc).2 hz)⟩

end twoPoint

/-- **Two-point beliefs**: on `[0, 1]`, `v` lies below every chord of a state price,
`(z - y) v x ≤ (z - x) p y + (x - y) p z` for `y ≤ x ≤ z`, `y < z`. -/
lemma IsStatePrice.le_chord (hp : IsStatePrice v p) {y x z : ℝ} (hy : 0 ≤ y) (hyx : y ≤ x)
    (hxz : x ≤ z) (hz : z ≤ 1) (hyz : y < z) :
    (z - y) * v x ≤ (z - x) * p y + (x - y) * p z := by
  have hzy : 0 < z - y := sub_pos.2 hyz
  set a := (z - x) / (z - y)
  have ha : a ∈ Icc (0 : ℝ) 1 :=
    ⟨div_nonneg (by linarith) hzy.le, (div_le_one hzy).2 (by linarith)⟩
  have hw : (z - y) * a = z - x := by simp only [a]; field_simp [hzy.ne']
  -- the belief with weights `a` on `y` and `1 - a` on `z` has mean `x`
  have : IsProbabilityMeasure (twoPoint a y z) := isProbabilityMeasure_twoPoint ha y z
  have h := hp.le _ this (twoPoint_mem (a := a) y z ⟨hy, by linarith⟩ ⟨by linarith, hz⟩)
  rw [integral_twoPoint ha, integral_twoPoint ha,
    show a * y + (1 - a) * z = x by linear_combination (-1 : ℝ) * hw] at h
  calc (z - y) * v x ≤ (z - y) * (a * p y + (1 - a) * p z) := by gcongr
    _ = _ := by linear_combination (p y - p z) * hw

section line

variable (hp : IsStatePrice v p)
  (hLip : ∀ x ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (0 : ℝ) 1, v y ≤ v x + L * |x - y|)
  {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1)
include hp hLip hx

/-- A secant from the left, from `(y, p y)` up to `(x, v x)`, has slope at most `L`. -/
lemma IsStatePrice.secant_le {y : ℝ} (hy : y ∈ Icc (0 : ℝ) 1) (hyx : y < x) :
    (v x - p y) / (x - y) ≤ L := by
  have h := hLip y hy x hx
  rw [abs_of_neg (by linarith)] at h
  rw [div_le_iff₀ (sub_pos.2 hyx)]
  linarith [hp.le_apply hy]

/-- The secants from the left, together with `-L`, lie below every secant to the right. -/
lemma IsStatePrice.le_secant {z : ℝ} (hz : z ∈ Icc (0 : ℝ) 1) (hxz : x < z) {b : ℝ}
    (hb : b ∈ insert (-L) ((fun y => (v x - p y) / (x - y)) '' {y | 0 ≤ y ∧ y < x})) :
    b * (z - x) ≤ p z - v x := by
  rcases hb with rfl | ⟨y, ⟨hy, hyx⟩, rfl⟩
  · -- `p z ≥ v z ≥ v x - L (z - x)`
    have h := hLip z hz x hx
    rw [abs_of_pos (by linarith)] at h
    linarith [hp.le_apply hz]
  · -- the chord over `[y, z]` passes above `(x, v x)`
    have := hp.le_chord hy hyx.le hxz.le hz.2 (by linarith)
    rw [div_mul_eq_mul_div, div_le_iff₀ (sub_pos.2 hyx)]
    nlinarith

/-- **Lemma 7** of DK, in one dimension: through `(x, v x)` passes a line of slope in `[-L, L]`
below the state price on `[0, 1]`. Its slope is the steepest secant from the left. -/
lemma IsStatePrice.exists_line :
    ∃ b ∈ Icc (-L) L, ∀ y ∈ Icc (0 : ℝ) 1, v x + b * (y - x) ≤ p y := by
  have hL := nonneg_of_lip hLip
  set A := insert (-L) ((fun y => (v x - p y) / (x - y)) '' {y | 0 ≤ y ∧ y < x})
  have hbdd : BddAbove A := ⟨L, by
    rintro _ (rfl | ⟨y, ⟨hy, hyx⟩, rfl⟩)
    · linarith
    · exact hp.secant_le hLip hx ⟨hy, by linarith [hx.2]⟩ hyx⟩
  refine ⟨sSup A, ⟨le_csSup hbdd (mem_insert _ _), csSup_le (insert_nonempty _ _) ?_⟩,
    fun y hy => ?_⟩
  · rintro _ (rfl | ⟨y, ⟨hy, hyx⟩, rfl⟩)
    · linarith
    · exact hp.secant_le hLip hx ⟨hy, by linarith [hx.2]⟩ hyx
  rcases lt_trichotomy y x with h | rfl | h
  · -- to the left: the slope is at least the secant through `y`
    have := le_csSup hbdd (mem_insert_of_mem _ ⟨y, ⟨hy.1, h⟩, rfl⟩)
    rw [div_le_iff₀ (sub_pos.2 h)] at this
    linarith
  · simpa using hp.le_apply hx
  · -- to the right: every left secant is below the secant through `y`
    have := csSup_le (insert_nonempty _ _) fun b hb =>
      (le_div_iff₀ (sub_pos.2 h)).2 (hp.le_secant hLip hx hy h hb)
    rw [le_div_iff₀ (sub_pos.2 h)] at this
    linarith

end line

/-- **Measurable supporting slopes**: some measurable `q` with `|q| ≤ L` has all its lines
through `v` below the state price on `[0, 1]`. It is the clamped right derivative of the hull of
the lines of Lemma 7. -/
lemma IsStatePrice.exists_slope (hp : IsStatePrice v p) (hv : IsPayoff v)
    (hLip : ∀ x ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (0 : ℝ) 1, v y ≤ v x + L * |x - y|) :
    ∃ q : ℝ → ℝ, Measurable q ∧ (∀ x, |q x| ≤ L) ∧
      ∀ y ∈ Icc (0 : ℝ) 1, lineSup I v q y ≤ p y := by
  have hL := nonneg_of_lip hLip
  obtain ⟨B, hB⟩ := hv.bdd
  obtain ⟨K, hK⟩ := hp.lipschitz
  set g := toB _ (lipschitzWith_extend hK).continuous
  have hg : ∀ y : I, g y = p y := fun y => by simp [g, projIcc_of_mem _ y.2]
  -- the lines of Lemma 7 support `g`, so their hull is a price below `p`
  have hh := isPrice_lowerHull hL (g := g) fun x => by
    obtain ⟨b, hb, hline⟩ := hp.exists_line hLip x.2
    exact ⟨b, hb, fun y => (hline y y.2).trans_eq (hg y).symm⟩
  refine ⟨clampSlope L (lowerHull L g),
    measurable_const.max ((subgrad_mono hh.convex).measurable.min measurable_const),
    abs_clampSlope_le hL, fun y hy => ?_⟩
  -- the clamped lines through `v` stay below the hull
  calc lineSup I v _ y ≤ lowerHull L g y := (lipPrice_spec hB hL hLip hh).2 y hy
    _ ≤ g ⟨y, hy⟩ := lowerHull_le hL g ⟨y, hy⟩
    _ = p y := hg _

/-! ### Theorem 5 -/

/-- Continuous functions that agree almost everywhere agree on the support. -/
lemma eqOn_support_of_ae_eq {μ : Measure ℝ} {F G : ℝ → ℝ} (hF : Continuous F)
    (hG : Continuous G) (h : F =ᵐ[μ] G) : EqOn F G μ.support := fun x hx => by
  by_contra hne
  exact ((Measure.mem_support_iff_forall x).1 hx _
    ((isOpen_ne_fun hF hG).mem_nhds hne)).ne' (ae_iff.1 h)

/-- Functions that agree on the support agree almost everywhere. -/
lemma ae_eq_of_eqOn_support {μ : Measure ℝ} {F G : ℝ → ℝ} (h : EqOn F G μ.support) :
    F =ᵐ[μ] G :=
  (show ∀ᵐ x ∂μ, x ∈ μ.support from Measure.support_mem_ae).mono fun _ hx => h hx

variable {μ : Measure ℝ} [IsProbabilityMeasure μ] (hμ : ∀ᵐ θ ∂μ, θ ∈ Icc (0 : ℝ) 1)
  (hv : IsPayoff v)
include hμ hv

/-- **A price below an optimal one agrees with it on the support of the prior**: it costs no
more, so it costs the same, so the gap vanishes almost surely. -/
lemma eqOn_support_of_le (hp : IsStatePrice v p) (hopt : ∫ x, p x ∂μ = stateValue v μ)
    {p' : ℝ → ℝ} (hp' : IsStatePrice v p') (hc : Continuous p')
    (hle : ∀ x ∈ Icc (0 : ℝ) 1, p' x ≤ p x) : EqOn p' p μ.support := by
  obtain ⟨K, hK⟩ := hp.lipschitz
  set P := fun x => p (projIcc (0 : ℝ) 1 zero_le_one x)
  have hP : P =ᵐ[μ] p := hμ.mono fun x hx => by simp [P, projIcc_of_mem _ hx]
  have hi := integrable_of_mem hμ (.of_continuous hc)
  -- `∫ p' = ∫ p`, so `p' = p` almost surely
  have hae : p' =ᵐ[μ] P := ((integral_eq_iff_of_ae_le hi (integrable_of_mem hμ hp.isPayoff)
      (hμ.mono hle)).1 (le_antisymm (integral_mono_ae hi (integrable_of_mem hμ hp.isPayoff)
        (hμ.mono hle)) (hopt ▸ stateValue_le hμ hv hp'))).trans hP.symm
  intro x hx
  have hxI := Measure.support_subset_of_isClosed isClosed_Icc hμ hx
  simpa [P, projIcc_of_mem _ hxI] using
    eqOn_support_of_ae_eq hc (lipschitzWith_extend hK).continuous hae hx

omit [IsProbabilityMeasure μ] hμ in
/-- **Unbiased lines**: if the states of a signal lie on lines `v m + q m (θ - m)` through its
posterior means, its value is the cost of the price. -/
lemma value_eq_of_ae_line {S : Signal} {pM q : ℝ → ℝ} (hc : Continuous pM) (hq : Measurable q)
    (hqL : ∀ x, |q x| ≤ L) (hae : ∀ᵐ z ∂S.π, pM z.1 = v z.2 + q z.2 * (z.1 - z.2)) :
    S.value v = ∫ θ, pM θ ∂S.prior := by
  rw [Signal.integral_prior hc, integral_congr_ae hae,
    Signal.integral_add_mul_sub (Signal.integrable_payoff hv) hq hqL]
  rfl

omit [IsProbabilityMeasure μ] hμ in
/-- **Tight lines**: if lines `v m + q m (θ - m)` stay below a price, and a signal pays its full
cost, then the states lie on the lines almost surely. -/
lemma ae_line_eq_of_le {S : Signal} {pM q : ℝ → ℝ} (hc : Continuous pM) (hq : Measurable q)
    (hqL : ∀ x, |q x| ≤ L) (hle : ∀ᵐ z ∂S.π, v z.2 + q z.2 * (z.1 - z.2) ≤ pM z.1)
    (h : S.value v = ∫ θ, pM θ ∂S.prior) :
    ∀ᵐ z ∂S.π, pM z.1 = v z.2 + q z.2 * (z.1 - z.2) := by
  have hi : Integrable (fun z : ℝ × ℝ => v z.2 + q z.2 * (z.1 - z.2)) S.π :=
    (Signal.integrable_payoff hv).add (Signal.integrable_mul_sub hq hqL)
  -- the lines integrate to the value, the price to its cost: the gap vanishes
  refine ((integral_eq_iff_of_ae_le hi (Signal.integrable_comp hc continuous_fst S.state_mem)
    hle).1 ?_).mono fun z hz => hz.symm
  rw [Signal.integral_add_mul_sub (Signal.integrable_payoff hv) hq hqL,
    ← Signal.integral_prior hc]
  exact h

/-- **Theorem 5** of Dworczak–Kolotilin, in one dimension. Let `v` be `L`-Lipschitz and `p` an
optimal state price. There is a price for moments `pM` that coincides with `p` on the support of
the prior, with:
* (i) `pM` convex, `L`-Lipschitz and above `v`;
* (ii) `pM(y) = sup_x (v x + q x (y - x))` for a measurable `q` with `|q| ≤ L`;
and every optimal signal pays `∫ pM dμ₀` and has `pM(θ) = v m + q m (θ - m)` almost surely. -/
theorem momentPrice_spec
    (hLip : ∀ x ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (0 : ℝ) 1, v y ≤ v x + L * |x - y|)
    (hp : IsStatePrice v p) (hopt : ∫ x, p x ∂μ = stateValue v μ) :
    ∃ pM q : ℝ → ℝ, EqOn pM p μ.support ∧
      (ConvexOn ℝ univ pM ∧ (∀ x y, pM x ≤ pM y + L * |x - y|) ∧
        ∀ x ∈ Icc (0 : ℝ) 1, v x ≤ pM x) ∧
      (Measurable q ∧ (∀ x, |q x| ≤ L) ∧ ∀ y, pM y = ⨆ x : I, (v x + q x * (y - x))) ∧
      ∀ S : Signal, S.prior = μ → (∀ S' : Signal, S'.prior = μ → S'.value v ≤ S.value v) →
        S.value v = ∫ ω, pM ω ∂μ ∧ ∀ᵐ z ∂S.π, pM z.1 = v z.2 + q z.2 * (z.1 - z.2) := by
  obtain ⟨B, hB⟩ := hv.bdd
  obtain ⟨q, hq, hqL, hle⟩ := hp.exists_slope hv hLip
  have hpr := isPrice_lineSup hB hqL
  have hc := continuous_of_convexOn hpr.convex
  -- `pM = lineSup I v q` is a price below `p`, hence equal to it on the support
  have heq := eqOn_support_of_le hμ hv hp hopt hpr.isStatePrice hc hle
  have hcost : ∫ ω, lineSup I v q ω ∂μ = ∫ ω, p ω ∂μ :=
    integral_congr_ae (ae_eq_of_eqOn_support heq)
  refine ⟨lineSup I v q, q, heq, ⟨hpr.convex, lineSup_lip subset_rfl hB hqL, hpr.le⟩,
    ⟨hq, hqL, fun _ => rfl⟩,
    fun S hS hSopt => ?_⟩
  -- an optimal signal achieves the dual value, which is the cost of `pM`
  have hval : S.value v = ∫ ω, lineSup I v q ω ∂μ := by
    rw [hcost, hopt, S.value_eq_stateValue_of_lip hLip hμ hv hS hSopt]
  exact ⟨hval, ae_line_eq_of_le hv hc hq hqL
    (S.mean_mem.mono fun z hz => line_le_lineSup subset_rfl hB hqL ⟨z.2, hz⟩ z.1) (hS ▸ hval)⟩

omit [IsProbabilityMeasure μ] hμ in
/-- **Theorem 5, converse via (i)**: a convex price for moments above `v` that a signal pays in
full certifies the signal optimal. (DK note that `v` need only be measurable and bounded.) -/
theorem optimal_of_momentPrice {S : Signal} {pM : ℝ → ℝ}
    (hconv : ConvexOn ℝ univ pM) (hle : ∀ x ∈ Icc (0 : ℝ) 1, v x ≤ pM x)
    (heq : S.value v = ∫ ω, pM ω ∂μ) :
    ∀ S' : Signal, S'.prior = μ → S'.value v ≤ S.value v := fun S' hS' =>
  heq ▸ hS' ▸ S'.value_le hv ⟨hconv, hle⟩

omit [IsProbabilityMeasure μ] hμ in
/-- **Theorem 5, converse via (ii)**: if a signal's states lie on the lines
`v m + q m (θ - m)` that make up a price for moments `pM`, the signal is optimal. -/
theorem optimal_of_momentSlope {S : Signal} (hS : S.prior = μ) {pM q : ℝ → ℝ}
    (hq : Measurable q) (hqL : ∀ x, |q x| ≤ L) (hpM : ∀ y, pM y = ⨆ x : I, (v x + q x * (y - x)))
    (hae : ∀ᵐ z ∂S.π, pM z.1 = v z.2 + q z.2 * (z.1 - z.2)) :
    ∀ S' : Signal, S'.prior = μ → S'.value v ≤ S.value v := by
  obtain ⟨B, hB⟩ := hv.bdd
  have hpM' : pM = lineSup I v q := funext hpM
  subst hpM'
  have hpr := isPrice_lineSup hB hqL
  -- the lines are unbiased, so the signal pays the cost of `pM`
  exact optimal_of_momentPrice hv hpr.convex hpr.le
    (hS ▸ value_eq_of_ae_line hv (continuous_of_convexOn hpr.convex) hq hqL hae)

/-! ### Theorem 4 -/

omit hμ in
/-- **Theorem 4 (Lipschitz preservation)** of DK, in one dimension: if `v` is `L`-Lipschitz on
`[0, 1]`, the concave closure is `L`-Lipschitz in the Kantorovich–Rubinstein distance. -/
theorem concaveClosure_lip
    (hLip : ∀ x ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (0 : ℝ) 1, v y ≤ v x + L * |x - y|)
    (hμ : ∀ᵐ θ ∂μ, θ ∈ Icc (0 : ℝ) 1) {η : Measure ℝ} [IsProbabilityMeasure η]
    (hη : ∀ᵐ θ ∂η, θ ∈ Icc (0 : ℝ) 1) :
    concaveClosure v η - concaveClosure v μ ≤ L * krDist η μ := by
  -- an `L`-Lipschitz supergradient at `μ`: the price for moments of Theorem 5
  obtain ⟨p, hp, hopt⟩ := exists_optimal_statePrice hLip hμ hv
  obtain ⟨pM, -, heq, ⟨hconv, hlip, hle⟩, -⟩ := momentPrice_spec hμ hv hLip hp hopt
  have hcost : ∫ ω, pM ω ∂μ = concaveClosure v μ := by
    rw [concaveClosure_eq_of_lip hLip hμ, ← hopt]
    exact integral_congr_ae (ae_eq_of_eqOn_support heq)
  have hη' : concaveClosure v η ≤ ∫ ω, pM ω ∂η := by
    rw [concaveClosure_eq_of_lip hLip hη]
    exact stateValue_le hη hv (IsPrice.isStatePrice ⟨hconv, hle⟩)
  linarith [integral_sub_le_mul_krDist hμ hlip hη]

omit hμ in
/-- Consequently, `v` Lipschitz on `[0, 1]` gives **bounded steepness** at every prior. -/
theorem boundedSteepness_of_lip
    (hLip : ∀ x ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (0 : ℝ) 1, v y ≤ v x + L * |x - y|)
    (hμ : ∀ᵐ θ ∂μ, θ ∈ Icc (0 : ℝ) 1) : BoundedSteepness v μ :=
  ⟨L, fun _ _ hη => concaveClosure_lip hv hLip hμ hη⟩

end MeanPersuasion
