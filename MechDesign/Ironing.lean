/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import MechDesign.Auction
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Ironing: monotone allocations are averages of thresholds

Myerson's treatment of non-regular distributions rests on one observation: a nondecreasing
allocation rule `Q : [a, b] → [0, 1]` is an average of *threshold* rules. Writing
`p(s)` for the type at which `Q` first reaches level `s`,

  `∫ₐᵇ Q g = ∫₀¹ (∫_{p(s)}^b g) ds`        (`integral_mul_eq_threshold`).

So `∫ Q g` is an average of tail integrals of `g`, and is bounded by their supremum.
-/

open MeasureTheory Set intervalIntegral

namespace Ironing

variable {a b s θ : ℝ} {Q g : ℝ → ℝ}

/-- The **threshold** at which `Q` first reaches level `s` on `[a, b]` (or `b` if never). -/
noncomputable def threshold (Q : ℝ → ℝ) (a b s : ℝ) : ℝ :=
  sInf (insert b {θ | θ ∈ Icc a b ∧ s ≤ Q θ})

lemma threshold_mem (hab : a ≤ b) : threshold Q a b s ∈ Icc a b := by
  have hbdd : BddBelow (insert b {θ | θ ∈ Icc a b ∧ s ≤ Q θ}) :=
    ⟨a, by rintro θ (rfl | ⟨hθ, -⟩); exacts [hab, hθ.1]⟩
  refine ⟨le_csInf (insert_nonempty _ _) ?_, csInf_le hbdd (mem_insert _ _)⟩
  rintro θ (rfl | ⟨hθ, -⟩); exacts [hab, hθ.1]

lemma threshold_le (hθ : θ ∈ Icc a b) (hs : s ≤ Q θ) : threshold Q a b s ≤ θ :=
  csInf_le ⟨a, by rintro x (rfl | ⟨hx, -⟩); exacts [hθ.1.trans hθ.2, hx.1]⟩
    (mem_insert_of_mem _ ⟨hθ, hs⟩)

/-- Above the threshold, a monotone `Q` has reached level `s`. -/
lemma le_of_threshold_lt (hQ : MonotoneOn Q (Icc a b)) (hθ : θ ∈ Icc a b)
    (h : threshold Q a b s < θ) : s ≤ Q θ := by
  obtain ⟨x, hx, hxθ⟩ := exists_lt_of_csInf_lt (insert_nonempty _ _) h
  rcases hx with rfl | ⟨hx, hsx⟩
  · exact absurd hθ.2 (not_le.2 hxθ)
  · exact hsx.trans (hQ hx hθ hxθ.le)

/-- Off the threshold itself, reaching level `s` means lying above the threshold. -/
lemma le_iff_threshold_lt (hQ : MonotoneOn Q (Icc a b)) (hθ : θ ∈ Icc a b)
    (hne : θ ≠ threshold Q a b s) : s ≤ Q θ ↔ threshold Q a b s < θ :=
  ⟨fun h => (threshold_le hθ h).lt_of_ne (Ne.symm hne), le_of_threshold_lt hQ hθ⟩

lemma threshold_mono (hab : a ≤ b) (hQ : MonotoneOn Q (Icc a b)) :
    Monotone fun s => threshold Q a b s := by
  intro s s' hss
  refine le_csInf (insert_nonempty _ _) ?_
  rintro θ (rfl | ⟨hθ, hs⟩)
  · exact (threshold_mem hab).2
  · exact threshold_le hθ (hss.trans hs)

/-- A value `c ∈ [0, 1]` is the length of `{s ∈ (0, 1] | s ≤ c}`. -/
lemma integral_level {c : ℝ} (hc : c ∈ Icc (0 : ℝ) 1) :
    ∫ s in Ioc (0 : ℝ) 1, (if s ≤ c then (1 : ℝ) else 0) = c := by
  have : (fun s : ℝ => if s ≤ c then (1 : ℝ) else 0) = (Iic c).indicator 1 := by
    ext s; simp [Set.indicator_apply]
  rw [this, setIntegral_indicator measurableSet_Iic, Ioc_inter_Iic, min_eq_right hc.2]
  simp [hc.1]

/-- Below the threshold the level indicator vanishes, above it it is one (except at the
threshold itself, a null set). -/
lemma integral_level_mul (hab : a ≤ b) (hQ : MonotoneOn Q (Icc a b)) (s : ℝ) :
    ∫ θ in Ioc a b, (if s ≤ Q θ then 1 else 0) * g θ = ∫ θ in threshold Q a b s..b, g θ := by
  have hp := threshold_mem (Q := Q) (s := s) hab
  have hset : Ioc a b ∩ Ioi (threshold Q a b s) = Ioc (threshold Q a b s) b := by
    rw [Ioc_inter_Ioi, max_eq_right hp.1]
  rw [integral_of_le hp.2, ← hset, ← setIntegral_indicator measurableSet_Ioi]
  refine setIntegral_congr_ae measurableSet_Ioc ?_
  have hne : ∀ᵐ θ ∂volume, θ ≠ threshold Q a b s := by
    simp [ae_iff, measure_singleton]
  filter_upwards [hne] with θ hne hθ
  have := le_iff_threshold_lt hQ (Ioc_subset_Icc_self hθ) hne
  by_cases h : s ≤ Q θ
  · simp [h, this.1 h]
  · simp [h, mt this.2 h]

/-- **A monotone allocation is an average of thresholds** (the layer-cake identity):
`∫ₐᵇ Q g = ∫₀¹ ∫_{p(s)}^b g ds`, where `p(s)` is the threshold of level `s`. -/
theorem integral_mul_eq_threshold (hab : a ≤ b) (hQ : MonotoneOn Q (Icc a b))
    (h01 : ∀ θ ∈ Icc a b, Q θ ∈ Icc (0 : ℝ) 1) (hg : ContinuousOn g (Icc a b)) :
    ∫ θ in a..b, Q θ * g θ = ∫ s in (0 : ℝ)..1, ∫ θ in threshold Q a b s..b, g θ := by
  -- extend `Q` monotonically to `ℝ`, to make it measurable
  set Q' : ℝ → ℝ := fun θ => Q (projIcc a b hab θ)
  have hQ'm : Monotone Q' := fun x y h =>
    hQ (projIcc a b hab x).2 (projIcc a b hab y).2 (monotone_projIcc hab h)
  have hQQ' : ∀ θ ∈ Icc a b, Q' θ = Q θ := fun θ hθ => by simp [Q', projIcc_of_mem hab hθ]
  have hthr : ∀ s, threshold Q' a b s = threshold Q a b s := fun s => by
    unfold threshold; congr 2; ext θ; exact and_congr_right fun hθ => by rw [hQQ' θ hθ]
  -- the integrand of the swapped integral is integrable on the product
  have hgi : Integrable g (volume.restrict (Ioc a b)) :=
    (hg.integrableOn_Icc).mono_set Ioc_subset_Icc_self
  have hint : Integrable (Function.uncurry fun θ s => (if s ≤ Q' θ then (1 : ℝ) else 0) * g θ)
      ((volume.restrict (Ioc a b)).prod (volume.restrict (Ioc (0 : ℝ) 1))) := by
    refine (hgi.norm.mul_prod (integrable_const (1 : ℝ))).mono' ?_ (ae_of_all _ fun z => ?_)
    · exact (Measurable.ite (measurableSet_le measurable_snd (hQ'm.measurable.comp
        measurable_fst)) measurable_const measurable_const).aestronglyMeasurable.mul
        ((hg.mono Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc).comp_fst
    · change ‖(if z.2 ≤ Q' z.1 then (1 : ℝ) else 0) * g z.1‖ ≤ ‖g z.1‖ * 1
      rw [norm_mul]; split_ifs <;> simp
  calc ∫ θ in a..b, Q θ * g θ
      = ∫ θ in Ioc a b, ∫ s in Ioc (0 : ℝ) 1, (if s ≤ Q' θ then 1 else 0) * g θ := by
        rw [integral_of_le hab]
        refine setIntegral_congr_fun measurableSet_Ioc fun θ hθ => ?_
        rw [MeasureTheory.integral_mul_const, integral_level (hQQ' θ (Ioc_subset_Icc_self hθ) ▸
          h01 θ (Ioc_subset_Icc_self hθ)), hQQ' θ (Ioc_subset_Icc_self hθ)]
    _ = ∫ s in Ioc (0 : ℝ) 1, ∫ θ in Ioc a b, (if s ≤ Q' θ then 1 else 0) * g θ :=
        integral_integral_swap hint
    _ = _ := by
        rw [integral_of_le zero_le_one]
        exact setIntegral_congr_fun measurableSet_Ioc fun s _ => by
          rw [integral_level_mul hab (hQ'm.monotoneOn _), hthr]

/-- The tail integral `p ↦ ∫ₚᵇ g`, read off at the thresholds, is integrable in the level. -/
lemma intervalIntegrable_tail_threshold (hab : a ≤ b) (hQ : MonotoneOn Q (Icc a b))
    (hg : ContinuousOn g (Icc a b)) :
    IntervalIntegrable (fun s => ∫ θ in threshold Q a b s..b, g θ) volume 0 1 := by
  have hT : ContinuousOn (fun p => ∫ θ in p..b, g θ) (Icc a b) := by
    have := continuousOn_primitive_interval_left (μ := volume) (f := g) (a := a) (b := b)
      (by rw [uIcc_of_le hab]; exact hg.integrableOn_Icc)
    rwa [uIcc_of_le hab] at this
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hT
  -- the threshold is monotone in the level, hence measurable
  have hT' := hT.comp_continuous (continuous_subtype_val.comp (continuous_projIcc (h := hab)))
    fun x => (projIcc a b hab x).2
  have hmeas : Measurable fun s => ∫ θ in threshold Q a b s..b, g θ := by
    convert hT'.measurable.comp (threshold_mono hab hQ).measurable using 2 with s
    simp [projIcc_of_mem hab (threshold_mem hab)]
  exact (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).2
    (.of_bound measure_Ioc_lt_top hmeas.aestronglyMeasurable M
      (ae_of_all _ fun s => hM _ (threshold_mem hab)))

/-- **An average of thresholds is bounded by the best threshold**: if every tail integral
`∫ₚᵇ g` is at most `C`, so is `∫ₐᵇ Q g`. -/
theorem integral_mul_le (hab : a ≤ b) (hQ : MonotoneOn Q (Icc a b))
    (h01 : ∀ θ ∈ Icc a b, Q θ ∈ Icc (0 : ℝ) 1) (hg : ContinuousOn g (Icc a b)) {C : ℝ}
    (hC : ∀ p ∈ Icc a b, ∫ θ in p..b, g θ ≤ C) : ∫ θ in a..b, Q θ * g θ ≤ C := by
  rw [integral_mul_eq_threshold hab hQ h01 hg]
  calc _ ≤ ∫ _ in (0 : ℝ)..1, C := integral_mono_on zero_le_one
          (intervalIntegrable_tail_threshold hab hQ hg) intervalIntegrable_const
          fun s _ => hC _ (threshold_mem hab)
    _ = C := by simp

/-! ### One buyer: posted prices are optimal without regularity -/

/-- The threshold rule at `p` has threshold `p` at every positive level. -/
lemma threshold_step {p : ℝ} (hp : p ∈ Icc a b) (hs : s ∈ Ioc (0 : ℝ) 1) :
    threshold (fun θ => if p ≤ θ then 1 else 0) a b s = p := by
  have : insert b {θ | θ ∈ Icc a b ∧ s ≤ if p ≤ θ then (1 : ℝ) else 0} = Icc p b := by
    ext θ
    simp only [mem_insert_iff, mem_ofPred_eq, mem_Icc]
    constructor
    · rintro (rfl | ⟨hθ, h⟩)
      · exact ⟨hp.2, le_rfl⟩
      · split_ifs at h with h'
        · exact ⟨h', hθ.2⟩
        · linarith [hs.1]
    · rintro ⟨h₁, h₂⟩
      exact Or.inr ⟨⟨hp.1.trans h₁, h₂⟩, by simp [h₁, hs.2]⟩
  rw [threshold, this, csInf_Icc hp.2]

lemma monotone_step (p : ℝ) : Monotone fun θ : ℝ => if p ≤ θ then (1 : ℝ) else 0 :=
  fun x y h => by
    dsimp only; split_ifs with h₁ h₂ <;> first | exact absurd (h₁.trans h) h₂ | norm_num

/-- **A threshold rule integrates the tail**: `∫ₐᵇ 1[θ ≥ p] g = ∫ₚᵇ g`. -/
lemma integral_step_mul {p : ℝ} (hp : p ∈ Icc a b) (hg : ContinuousOn g (Icc a b)) :
    ∫ θ in a..b, (if p ≤ θ then 1 else 0) * g θ = ∫ θ in p..b, g θ := by
  have hab := hp.1.trans hp.2
  rw [integral_mul_eq_threshold hab ((monotone_step p).monotoneOn _)
    (fun θ _ => by split_ifs <;> norm_num) hg,
    integral_congr_ae (g := fun _ => ∫ θ in p..b, g θ) (ae_of_all _ fun s hs => by
      rw [uIoc_of_le zero_le_one] at hs; simp only [threshold_step hp hs])]
  simp

open Myerson

variable {f : ℝ → ℝ}

/-- The revenue of a posted price is the price times the probability of sale. -/
theorem revenue_postedPrice {p : ℝ} (hp : p ∈ Icc a b) (hf : ContinuousOn f (Icc a b))
    (hF : ∫ s in a..b, f s = 1) : revenue f a b (postedPrice p) = p * (1 - cdf f a p) := by
  have hab := hp.1.trans hp.2
  have hfi := hf.intervalIntegrable_of_Icc (μ := volume) hab
  calc revenue f a b (postedPrice p)
      = ∫ θ in a..b, (if p ≤ θ then 1 else 0) * (p * f θ) :=
        integral_congr fun θ _ => by simp only [postedPrice]; split_ifs <;> ring
    _ = p * (1 - cdf f a p) := by
        rw [integral_step_mul (g := fun θ => p * f θ) hp (continuousOn_const.mul hf),
          intervalIntegral.integral_const_mul, cdf,
          ← hF, integral_interval_sub_left hfi (hfi.mono_set (by
            rw [uIcc_of_le hab, uIcc_of_le hp.1]; exact Icc_subset_Icc_right hp.2))]

/-- The tail of the virtual surplus is the revenue of the posted price at its start. -/
lemma tail_J_eq {p : ℝ} (hp : p ∈ Icc a b) (hf : ContinuousOn f (Icc a b))
    (hF : ∫ s in a..b, f s = 1) : ∫ θ in p..b, J f a θ = revenue f a b (postedPrice p) := by
  have hab := hp.1.trans hp.2
  rw [revenue_eq_virtualSurplus hab hf hF (postedPrice_IC p), postedPrice_U,
    max_eq_right (by linarith [hp.1]), sub_zero, ← integral_step_mul hp
      ((J_continuousOn hab hf).mono (by rw [uIcc_of_le hab]))]
  rfl

/-- **Posted prices are optimal for any distribution** (Riley–Zeckhauser 1983; the
one-buyer case of Myerson's ironing). Some posted price earns at least as much as every
IC, IR mechanism. Proof: an IC allocation is an average of threshold rules, and each
threshold rule earns at most the best posted price. -/
theorem exists_postedPrice_optimal (hab : a ≤ b) (hf : ContinuousOn f (Icc a b))
    (hF : ∫ s in a..b, f s = 1) :
    ∃ p ∈ Icc a b, ∀ m : Mech, m.IC a b → m.IR a b → (∀ θ ∈ Icc a b, m.q θ ∈ Icc (0 : ℝ) 1) →
      revenue f a b m ≤ revenue f a b (postedPrice p) := by
  have hJ : ContinuousOn (J f a) (Icc a b) := by
    simpa [uIcc_of_le hab] using J_continuousOn hab hf
  -- the best posted price exists: revenue is continuous in the price
  have hR : ContinuousOn (fun p => ∫ θ in p..b, J f a θ) (Icc a b) := by
    have := continuousOn_primitive_interval_left (μ := volume) (f := J f a) (a := a) (b := b)
      (by rw [uIcc_of_le hab]; exact hJ.integrableOn_Icc)
    rwa [uIcc_of_le hab] at this
  obtain ⟨p, hp, hmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.2 hab) hR
  refine ⟨p, hp, fun m hIC hIR hq => ?_⟩
  -- an IC allocation is an average of thresholds, each worth at most the best price
  rw [revenue_eq_virtualSurplus hab hf hF hIC, ← tail_J_eq hp hf hF]
  have := integral_mul_le hab hIC.monotoneOn hq hJ fun p' hp' => hmax hp'
  linarith [hIR a ⟨le_rfl, hab⟩]

/-! ### Ironed virtual values -/

variable {f φ : ℝ → ℝ}

/-- The **ironing gap** `D(p) = ∫ₐᵖ (J - φ f)` between the virtual surplus and the score
`φ` (weighted by the density). -/
noncomputable def gap (f : ℝ → ℝ) (a : ℝ) (φ : ℝ → ℝ) (p : ℝ) : ℝ :=
  ∫ θ in a..p, J f a θ - φ θ * f θ

/-- `φ` **irons** the virtual value of the density `f` on `[a, b]`: it is monotone, the gap is
nonnegative and closes at `b`, and `φ` is flat wherever the gap is open. (This is the
derivative of the convex hull of the revenue curve; when the virtual value is itself monotone,
it irons itself with zero gap: `ironed_virtualValue`.) -/
structure Ironed (f : ℝ → ℝ) (a b : ℝ) (φ : ℝ → ℝ) : Prop where
  mono : Monotone φ
  bddMeas : Auction.BddMeas φ
  cont : ContinuousOn φ (Icc a b)
  gap_nonneg : ∀ p ∈ Icc a b, 0 ≤ gap f a φ p
  gap_right : gap f a φ b = 0
  flat : ∀ p ∈ Ioo a b, 0 < gap f a φ p → ∃ ε > 0, ∀ x ∈ Ioo (p - ε) (p + ε), φ x = φ p

lemma gap_integrand_continuousOn (hab : a ≤ b) (hI : Ironed f a b φ)
    (hf : ContinuousOn f (Icc a b)) : ContinuousOn (fun θ => J f a θ - φ θ * f θ) (Icc a b) := by
  have hJ : ContinuousOn (J f a) (Icc a b) := by simpa [uIcc_of_le hab] using J_continuousOn hab hf
  exact hJ.sub (hI.cont.mul hf)

/-- The tail of the gap integrand is minus the gap. -/
lemma tail_gap (hI : Ironed f a b φ) (hf : ContinuousOn f (Icc a b)) {p : ℝ}
    (hp : p ∈ Icc a b) : ∫ θ in p..b, (J f a θ - φ θ * f θ) = -gap f a φ p := by
  have hab := hp.1.trans hp.2
  have hg := gap_integrand_continuousOn hab hI hf
  have hi : ∀ x ∈ Icc a b, IntervalIntegrable (fun θ => J f a θ - φ θ * f θ) volume a x :=
    fun x hx => (hg.mono (by rw [uIcc_of_le hx.1]; exact Icc_subset_Icc_right hx.2))
      |>.intervalIntegrable
  rw [← integral_interval_sub_left (hi b ⟨hab, le_rfl⟩) (hi p hp)]
  simp [gap, ← hI.gap_right]

/-- **Ironing only costs revenue**: for a monotone allocation, `∫ Q (J - φ f) ≤ 0`. -/
lemma gapTerm_nonpos (hab : a ≤ b) (hI : Ironed f a b φ) (hf : ContinuousOn f (Icc a b))
    (hQ : MonotoneOn Q (Icc a b)) (h01 : ∀ θ ∈ Icc a b, Q θ ∈ Icc (0 : ℝ) 1) :
    ∫ θ in a..b, Q θ * (J f a θ - φ θ * f θ) ≤ 0 :=
  integral_mul_le hab hQ h01 (gap_integrand_continuousOn hab hI hf) fun p hp => by
    rw [tail_gap hI hf hp]; linarith [hI.gap_nonneg p hp]

/-- **Complementary slackness**: if `Q` depends on the type only through `φ`, the gap costs
nothing, because no threshold of `Q` lies inside an ironing interval. -/
lemma gapTerm_eq_zero (hab : a ≤ b) (hI : Ironed f a b φ) (hf : ContinuousOn f (Icc a b))
    (hQ : MonotoneOn Q (Icc a b)) (h01 : ∀ θ ∈ Icc a b, Q θ ∈ Icc (0 : ℝ) 1)
    (hfac : ∀ x ∈ Icc a b, ∀ y ∈ Icc a b, φ x = φ y → Q x = Q y) :
    ∫ θ in a..b, Q θ * (J f a θ - φ θ * f θ) = 0 := by
  rw [integral_mul_eq_threshold hab hQ h01 (gap_integrand_continuousOn hab hI hf)]
  refine (integral_congr_ae (g := fun _ => 0) (ae_of_all _ fun s hs => ?_)).trans (by simp)
  rw [uIoc_of_le zero_le_one] at hs
  have hp := threshold_mem (Q := Q) (s := s) hab
  set p := threshold Q a b s
  rw [tail_gap hI hf hp, neg_eq_zero]
  by_contra hne
  have hpos : 0 < gap f a φ p := (hI.gap_nonneg p hp).lt_of_ne (Ne.symm hne)
  have hap : a < p := hp.1.lt_of_ne fun h => by simp [← h, gap] at hpos
  have hpb : p < b := hp.2.lt_of_ne fun h => by rw [h, hI.gap_right] at hpos; exact hpos.false
  obtain ⟨ε, hε, hflat⟩ := hI.flat p ⟨hap, hpb⟩ hpos
  -- `φ` is flat around the threshold, so `Q` is too: a point just above it has reached level
  -- `s`, hence so has a point just below it, which contradicts the threshold's minimality
  set y := min (p + ε / 2) b
  set z := max (p - ε / 2) ((a + p) / 2)
  have hy : y ∈ Icc a b := ⟨by simp [y]; constructor <;> linarith, min_le_right _ _⟩
  have hz : z ∈ Icc a b := ⟨le_max_of_le_right (by linarith), max_le (by linarith) (by linarith)⟩
  have hpy : p < y := lt_min (by linarith) hpb
  have hzp : z < p := max_lt (by linarith) (by linarith)
  have hyε : y ∈ Ioo (p - ε) (p + ε) := ⟨by linarith, by simp [y]; left; linarith⟩
  have hzε : z ∈ Ioo (p - ε) (p + ε) := ⟨by simp [z]; left; linarith, by linarith⟩
  have hQyz : Q y = Q z := hfac y hy z hz (by rw [hflat y hyε, hflat z hzε])
  have hsz : s ≤ Q z := hQyz ▸ le_of_threshold_lt hQ hy hpy
  exact absurd (threshold_le hz hsz) (not_le.2 hzp)

end Ironing

/-! ### The ironed Myerson auction -/

namespace Auction

open Ironing Function Finset
open scoped Classical

set_option linter.unusedSectionVars false

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] {ν : ι → Measure ℝ}
  [∀ i, IsProbabilityMeasure (ν i)] {a b : ℝ} {f : ι → ℝ → ℝ}

lemma wins_congr {φ : ι → ℝ → ℝ} {θ θ' : ι → ℝ} (h : ∀ j, φ j (θ j) = φ j (θ' j)) (i : ι) :
    Wins φ θ i ↔ Wins φ θ' i := by
  simp only [Wins, h]

/-- In a highest-score auction, a bidder's interim allocation depends on its type only
through its score. -/
lemma highestScore_interim_congr {φ : ι → ℝ → ℝ} (i : ι) {x y : ℝ} (h : φ i x = φ i y) :
    ((highestScore φ a b).interim ν i).q x = ((highestScore φ a b).interim ν i).q y := by
  refine integral_congr_ae (ae_of_all _ fun θ => ?_)
  have : Wins φ (update θ i x) i ↔ Wins φ (update θ i y) i := wins_congr (fun j => by
    by_cases hj : j = i
    · subst hj; simp [h]
    · simp [hj]) i
  simp only [highestScore, this]

variable (a b) in
/-- **The ironed Myerson auction**: the highest nonnegative ironed virtual value wins, at the
threshold price. -/
noncomputable def ironedAuction (φ : ι → ℝ → ℝ) : Mechanism ι := highestScore φ a b

/-- **Myerson's optimal auction, general case** (Myerson 1981, §6). If `φ i` irons bidder
`i`'s virtual value, the ironed auction is bounded measurable, feasible, BIC and interim IR,
and earns at least as much as any other such auction. -/
theorem ironed_optimal (P : Prior ν f a b) {φ : ι → ℝ → ℝ}
    (hI : ∀ i, Ironed (f i) a b (φ i)) :
    (ironedAuction a b φ).BddMeasurable ∧ (ironedAuction a b φ).Feasible ∧
      (ironedAuction a b φ).BIC ν a b ∧ (∀ i, ((ironedAuction a b φ).interim ν i).IR a b) ∧
      ∀ M : Mechanism ι, M.BddMeasurable → M.Feasible → M.BIC ν a b →
        (∀ i, (M.interim ν i).IR a b) → M.revenue ν ≤ (ironedAuction a b φ).revenue ν := by
  have hφ i := (hI i).bddMeas
  obtain ⟨hA, hAF, hAIC, hAIR, hAU⟩ :=
    highestScore_properties (ν := ν) P.hab hφ fun i => (hI i).mono
  refine ⟨hA, hAF, hAIC, hAIR, fun M hM hF hIC hIR => ?_⟩
  -- any auction: the ironing gap only costs revenue, and the score surplus is at most the top
  have hle : M.revenue ν ≤ ∫ θ, topScore φ θ ∂Measure.pi ν := by
    rw [M.revenue_eq_score P hM hIC hφ]
    have h₁ := sum_nonpos fun i (_ : i ∈ Finset.univ) => gapTerm_nonpos P.hab (hI i)
      (P.cont i).continuousOn (hIC i).monotoneOn fun x _ => Mechanism.interim_q_mem hM hF i x
    have h₂ := sum_nonneg fun i (_ : i ∈ Finset.univ) => hIR i a ⟨le_rfl, P.hab⟩
    have h₃ := integral_mono (integrable_finsetSum _ fun i _ =>
      ((hM i).1.mul ((hφ i).comp_eval i)).integrable)
      ((topScore_bddMeas hφ).integrable (μ := Measure.pi ν)) (Mechanism.sum_le_topScore hF φ)
    linarith
  -- the ironed auction: the gap closes, no rent at the bottom, and it earns the top score
  refine hle.trans_eq ?_
  unfold ironedAuction
  rw [Mechanism.revenue_eq_score P hA hAIC hφ, sum_eq_zero fun i _ => gapTerm_eq_zero P.hab
      (hI i) (P.cont i).continuousOn (hAIC i).monotoneOn
      (fun x _ => Mechanism.interim_q_mem hA hAF i x)
      (fun x _ y _ h => highestScore_interim_congr i h),
    sum_eq_zero fun i _ => hAU i, add_zero, sub_zero]
  exact integral_congr_ae (ae_of_all _ fun θ => (highestScore_sum θ).symm)

/-! ### The regular case -/

/-- Under regularity the virtual value irons itself, with zero gap. -/
lemma ironed_virtualValue (P : Prior ν f a b)
    (hreg : ∀ i, MonotoneOn (virtualValue (f i) a b) (Icc a b)) (i : ι) :
    Ironed (f i) a b (virtualValue (f i) a b) := by
  have hab := P.hab
  -- on `[a, b]` the virtual value is `J / f`, so the gap integrand vanishes
  have hgap : ∀ p ∈ Icc a b, gap (f i) a (virtualValue (f i) a b) p = 0 := fun p hp =>
    (intervalIntegral.integral_congr fun θ hθ => by
      rw [uIcc_of_le hp.1] at hθ
      have hθ' : θ ∈ Icc a b := ⟨hθ.1, hθ.2.trans hp.2⟩
      simp [J_eq_virtualValue_mul hθ' (P.pos i θ hθ').ne']).trans intervalIntegral.integral_zero
  have hJ : ContinuousOn (Myerson.J (f i) a) (Icc a b) := by
    simpa [uIcc_of_le hab] using Myerson.J_continuousOn hab (P.cont i).continuousOn
  refine ⟨virtualValue_monotone hab (hreg i), P.virtualValue_bddMeas' i,
    (hJ.div (P.cont i).continuousOn fun θ hθ => (P.pos i θ hθ).ne').congr fun θ hθ => ?_,
    fun p hp => (hgap p hp).ge, hgap b ⟨hab, le_rfl⟩, fun p hp hpos => ?_⟩
  · simp [virtualValue, min_eq_left hθ.2, max_eq_right hθ.1]
  · exact absurd (hgap p (Ioo_subset_Icc_self hp)) hpos.ne'

variable (a b f) in
/-- **The Myerson auction**: highest nonnegative virtual value wins, at the threshold price. -/
noncomputable def myersonAuction : Mechanism ι :=
  ironedAuction a b fun i => virtualValue (f i) a b

/-- **Myerson's optimal auction, regular case** (1981). Under regularity (virtual values
nondecreasing) no ironing is needed: the Myerson auction is bounded measurable, feasible, BIC
and interim IR, and earns at least as much as any other such auction. -/
theorem myerson_optimal (P : Prior ν f a b)
    (hreg : ∀ i, MonotoneOn (virtualValue (f i) a b) (Icc a b)) :
    (myersonAuction a b f).BddMeasurable ∧ (myersonAuction a b f).Feasible ∧
      (myersonAuction a b f).BIC ν a b ∧ (∀ i, ((myersonAuction a b f).interim ν i).IR a b) ∧
      ∀ M : Mechanism ι, M.BddMeasurable → M.Feasible → M.BIC ν a b →
        (∀ i, (M.interim ν i).IR a b) → M.revenue ν ≤ (myersonAuction a b f).revenue ν :=
  ironed_optimal P (ironed_virtualValue P hreg)

end Auction
