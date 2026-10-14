/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import MechDesign.Myerson
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Myerson's optimal auction (n bidders)

Bidders `i : ι` have independent types `θ i ∈ [a, b]` with laws `ν i`, so the profile has law
`μ = Measure.pi ν`. An auction assigns to each profile allocation probabilities `q i θ` and
payments `t i θ`. Bidder `i`'s **interim** rule averages these over the other bidders' types:
`Q i s = E[q i (θ with θ i := s)]`. Bayesian incentive compatibility means that each interim
rule is an incentive-compatible single-agent mechanism, so the one-bidder theory
(`MechDesign.Myerson`) applies bidder by bidder.

The only new probabilistic fact needed is **resampling** (`map_update`): redrawing one
bidder's type leaves the joint law unchanged. With it, we prove

* `revenue_eq`: expected revenue is expected virtual surplus,
  `E[∑ᵢ qᵢ φᵢ(θᵢ)] - ∑ᵢ Uᵢ(a)`;
* `revenue_le`: **Myerson's bound**: a feasible, BIC and interim-IR auction earns at most
  `E[max(0, maxᵢ φᵢ(θᵢ))]`.
-/

open MeasureTheory Set Function Finset

set_option linter.unusedSectionVars false

namespace Auction

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (ν : ι → Measure ℝ)
  [∀ i, IsProbabilityMeasure (ν i)]

/-! ### Resampling one coordinate of a product measure -/

/-- **Resampling.** Redrawing bidder `i`'s type independently leaves the joint law of types
unchanged. -/
lemma map_update (i : ι) :
    ((Measure.pi ν).prod (ν i)).map (fun p => update p.1 i p.2) = Measure.pi ν := by
  symm
  refine Measure.pi_eq fun S hS => ?_
  rw [Measure.map_apply (by fun_prop) (MeasurableSet.univ_pi hS)]
  have : (fun p : (ι → ℝ) × ℝ => update p.1 i p.2) ⁻¹' Set.univ.pi S =
      Set.univ.pi (update S i Set.univ) ×ˢ S i := by
    ext ⟨θ, s⟩
    simp only [Set.mem_preimage, mem_univ_pi, Set.mem_prod]
    constructor
    · intro h; refine ⟨fun j => ?_, by simpa using h i⟩
      by_cases hj : j = i
      · subst hj; simp
      · simpa [hj] using h j
    · rintro ⟨h, hs⟩ j
      by_cases hj : j = i
      · subst hj; simpa using hs
      · simpa [hj] using h j
  rw [this, Measure.prod_prod, Measure.pi_pi]
  have : (fun j => ν j (update S i Set.univ j)) = update (fun j => ν j (S j)) i 1 := by
    ext1 j; by_cases hj : j = i
    · subst hj; simp
    · simp [hj]
  rw [this, prod_update_of_mem (mem_univ i), ← mul_prod_erase _ _ (mem_univ i), one_mul,
    mul_comm, sdiff_singleton_eq_erase]

/-- Resampling, integrated: average first over the other bidders, then over bidder `i`. -/
lemma integral_resample (i : ι) {F : (ι → ℝ) → ℝ} (hF : Integrable F (Measure.pi ν)) :
    ∫ θ, F θ ∂Measure.pi ν = ∫ s, ∫ θ, F (update θ i s) ∂Measure.pi ν ∂ν i := by
  have hm : Measurable fun p : (ι → ℝ) × ℝ => update p.1 i p.2 := by fun_prop
  rw [← map_update ν i] at hF
  conv_lhs => rw [← map_update ν i]
  rw [integral_map hm.aemeasurable hF.aestronglyMeasurable]
  exact integral_prod_symm (fun p => F (update p.1 i p.2)) (hF.comp_measurable hm)

/-! ### Bounded measurable functions -/

/-- `g` is measurable and bounded. -/
def BddMeas {α : Type*} [MeasurableSpace α] (g : α → ℝ) : Prop :=
  Measurable g ∧ ∃ C, ∀ x, |g x| ≤ C

lemma BddMeas.integrable {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
    {g : α → ℝ} (hg : BddMeas g) : Integrable g μ :=
  let ⟨C, hC⟩ := hg.2
  .of_bound hg.1.aestronglyMeasurable C (ae_of_all _ fun x => by simpa using hC x)

lemma BddMeas.mul {α : Type*} [MeasurableSpace α] {g h : α → ℝ} (hg : BddMeas g)
    (hh : BddMeas h) : BddMeas fun x => g x * h x := by
  obtain ⟨C, hC⟩ := hg.2; obtain ⟨D, hD⟩ := hh.2
  exact ⟨hg.1.mul hh.1, C * D, fun x => by
    rw [abs_mul]; exact mul_le_mul (hC x) (hD x) (abs_nonneg _) ((abs_nonneg _).trans (hC x))⟩

lemma BddMeas.comp_eval {g : ℝ → ℝ} (hg : BddMeas g) (i : ι) : BddMeas fun θ : ι → ℝ => g (θ i) :=
  ⟨hg.1.comp (measurable_pi_apply i), hg.2.imp fun _ hC θ => hC (θ i)⟩

/-- Averaging out the other bidders preserves bounded measurability. -/
lemma BddMeas.interim {g : (ι → ℝ) → ℝ} (hg : BddMeas g) (i : ι) :
    BddMeas fun s => ∫ θ, g (update θ i s) ∂Measure.pi ν := by
  obtain ⟨C, hC⟩ := hg.2
  refine ⟨?_, C, fun s => ?_⟩
  · have : Measurable fun p : ℝ × (ι → ℝ) => g (update p.2 i p.1) := hg.1.comp (by fun_prop)
    exact this.stronglyMeasurable.integral_prod_right'.measurable
  · rw [← Real.norm_eq_abs]
    refine (norm_integral_le_of_norm_le_const (C := C) (ae_of_all _ fun θ => ?_)).trans ?_
    · simpa using hC _
    · simp

/-! ### Auctions -/

/-- An auction: allocation probabilities and payments for each bidder at each type profile. -/
structure Mechanism (ι : Type*) where
  q : ι → (ι → ℝ) → ℝ
  t : ι → (ι → ℝ) → ℝ

namespace Mechanism

variable {ν} (M : Mechanism ι)

/-- Allocations and payments are bounded and measurable. -/
def Regular : Prop := ∀ i, BddMeas (M.q i) ∧ BddMeas (M.t i)

/-- Feasibility: allocation probabilities are nonnegative and sum to at most one. -/
def Feasible : Prop := ∀ θ, (∀ i, 0 ≤ M.q i θ) ∧ ∑ i, M.q i θ ≤ 1

variable (ν) in
/-- Bidder `i`'s interim mechanism: average over the other bidders' types. -/
noncomputable def interim (i : ι) : Myerson.Mech :=
  ⟨fun s => ∫ θ, M.q i (update θ i s) ∂Measure.pi ν,
   fun s => ∫ θ, M.t i (update θ i s) ∂Measure.pi ν⟩

variable (ν) in
/-- Expected revenue. -/
noncomputable def revenue : ℝ := ∫ θ, ∑ i, M.t i θ ∂Measure.pi ν

end Mechanism

/-! ### Densities and virtual values -/

/-- `ν` has density `f` on `[a, b]`: integrating a bounded measurable `g` against `ν` is
integrating `g f` over `[a, b]`. -/
def HasDensity (ν : Measure ℝ) (f : ℝ → ℝ) (a b : ℝ) : Prop :=
  ∀ g, BddMeas g → ∫ x, g x ∂ν = ∫ x in a..b, g x * f x

/-- The hypothesis is the expected one: the law with density `g` on `[a, b]` has density
`g`. -/
lemma hasDensity_withDensity {a b : ℝ} (hab : a ≤ b) {g : ℝ → ℝ} (hg : Continuous g)
    (hpos : ∀ x ∈ Icc a b, 0 ≤ g x) :
    HasDensity ((volume.restrict (Ioc a b)).withDensity fun x => ENNReal.ofReal (g x)) g a b := by
  intro h _
  rw [integral_withDensity_eq_integral_toReal_smul hg.measurable.ennreal_ofReal
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top), intervalIntegral.integral_of_le hab]
  refine setIntegral_congr_fun measurableSet_Ioc fun x hx => ?_
  simp [ENNReal.toReal_ofReal (hpos x (Ioc_subset_Icc_self hx)), mul_comm]

/-- ... and it is a probability measure when `∫ₐᵇ g = 1`. -/
lemma isProbabilityMeasure_withDensity {a b : ℝ} (hab : a ≤ b) {g : ℝ → ℝ} (hg : Continuous g)
    (hpos : ∀ x ∈ Icc a b, 0 ≤ g x) (h1 : ∫ x in a..b, g x = 1) :
    IsProbabilityMeasure
      ((volume.restrict (Ioc a b)).withDensity fun x => ENNReal.ofReal (g x)) := by
  constructor
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal (hg.integrableOn_Icc.mono_set Ioc_subset_Icc_self)
      ((ae_restrict_iff' measurableSet_Ioc).2 (ae_of_all _ fun x hx => hpos x
        (Ioc_subset_Icc_self hx))), ← intervalIntegral.integral_of_le hab, h1,
    ENNReal.ofReal_one]

/-- Myerson's **virtual value** `φ θ = θ - (1 - F θ) / f θ`, evaluated at `θ` clamped into
`[a, b]` (types lie in `[a, b]`; clamping keeps `φ` bounded and measurable). -/
noncomputable def virtualValue (f : ℝ → ℝ) (a b θ : ℝ) : ℝ :=
  Myerson.J f a (max a (min θ b)) / f (max a (min θ b))

variable {a b : ℝ} {f : ι → ℝ → ℝ}

lemma J_eq_virtualValue_mul {g : ℝ → ℝ} {θ : ℝ} (hθ : θ ∈ Icc a b) (hg : g θ ≠ 0) :
    Myerson.J g a θ = virtualValue g a b θ * g θ := by
  simp only [virtualValue, min_eq_left hθ.2, max_eq_right hθ.1, div_mul_cancel₀ _ hg]

lemma virtualValue_bddMeas (hab : a ≤ b) {g : ℝ → ℝ} (hg : Continuous g)
    (hpos : ∀ θ ∈ Icc a b, 0 < g θ) :
    BddMeas (virtualValue g a b) := by
  have hc : Continuous fun θ => max a (min θ b) := by fun_prop
  have hJ : Continuous (Myerson.J g a) := by
    unfold Myerson.J Myerson.cdf
    exact (continuous_id.mul hg).sub (continuous_const.sub
      (intervalIntegral.continuous_primitive hg.intervalIntegrable a))
  refine ⟨((hJ.comp hc).measurable.div (hg.comp hc).measurable), ?_⟩
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := a) (b := b)).exists_bound_of_continuousOn
    (f := fun θ => Myerson.J g a θ / g θ)
    (hJ.continuousOn.div hg.continuousOn fun θ hθ => (hpos θ hθ).ne')
  exact ⟨C, fun θ => by
    simpa [virtualValue, abs_div] using
      hC (max a (min θ b)) ⟨le_max_left _ _, max_le hab (min_le_right _ _)⟩⟩

/-- The prior: independent types on `[a, b]` with continuous, positive densities. -/
structure Prior (ν : ι → Measure ℝ) (f : ι → ℝ → ℝ) (a b : ℝ) : Prop where
  hab : a ≤ b
  density : ∀ i, HasDensity (ν i) (f i) a b
  cont : ∀ i, Continuous (f i)
  pos : ∀ i, ∀ θ ∈ Icc a b, 0 < f i θ

namespace Prior

variable {ν} (P : Prior ν f a b)
include P

lemma integral_density (i : ι) : ∫ x in a..b, f i x = 1 := by
  simpa using (P.density i (fun _ => 1) ⟨measurable_const, 1, fun _ => by simp⟩).symm

lemma virtualValue_bddMeas' (i : ι) : BddMeas (virtualValue (f i) a b) :=
  virtualValue_bddMeas P.hab (P.cont i) (P.pos i)

end Prior

namespace Mechanism

variable {ν} {M : Mechanism ι}

/-- **One bidder's payments = virtual surplus.** Resample bidder `i`, apply the one-bidder
revenue formula to the interim mechanism, and resample back. -/
lemma integral_payment_eq (P : Prior ν f a b) (hM : M.Regular) (i : ι)
    (hIC : (M.interim ν i).IC a b) :
    ∫ θ, M.t i θ ∂Measure.pi ν =
      (∫ θ, M.q i θ * virtualValue (f i) a b (θ i) ∂Measure.pi ν) - (M.interim ν i).U a := by
  have hφ := P.virtualValue_bddMeas' i
  have hQφ : BddMeas fun x => (M.interim ν i).q x * virtualValue (f i) a b x :=
    ((hM i).1.interim ν i).mul hφ
  calc ∫ θ, M.t i θ ∂Measure.pi ν
      = ∫ x in a..b, (M.interim ν i).t x * f i x := by
        rw [integral_resample ν i (hM i).2.integrable]
        exact P.density i _ ((hM i).2.interim ν i)
    _ = (∫ x in a..b, (M.interim ν i).q x * Myerson.J (f i) a x) - (M.interim ν i).U a :=
        Myerson.revenue_eq_virtualSurplus P.hab (P.cont i).continuousOn
          (P.integral_density i) hIC
    _ = (∫ x in a..b, ((M.interim ν i).q x * virtualValue (f i) a b x) * f i x) -
          (M.interim ν i).U a := by
        congr 1
        refine intervalIntegral.integral_congr fun x hx => ?_
        rw [uIcc_of_le P.hab] at hx
        rw [J_eq_virtualValue_mul hx (P.pos i x hx).ne', mul_assoc]
    _ = _ := by
        rw [← P.density i _ hQφ, integral_resample ν i (F := fun θ => M.q i θ *
          virtualValue (f i) a b (θ i)) ((hM i).1.mul (hφ.comp_eval i)).integrable]
        simp [interim, integral_mul_const]

variable (ν) in
/-- The auction is Bayesian incentive compatible. -/
def BIC (M : Mechanism ι) (a b : ℝ) : Prop := ∀ i, (M.interim ν i).IC a b

/-- **Revenue = expected virtual surplus** (Myerson 1981):
`E[revenue] = E[∑ᵢ qᵢ(θ) φᵢ(θᵢ)] - ∑ᵢ Uᵢ(a)`. -/
theorem revenue_eq (P : Prior ν f a b) (hM : M.Regular) (hIC : M.BIC ν a b) :
    M.revenue ν = (∫ θ, ∑ i, M.q i θ * virtualValue (f i) a b (θ i) ∂Measure.pi ν) -
      ∑ i, (M.interim ν i).U a := by
  have hqφ : ∀ i, BddMeas fun θ => M.q i θ * virtualValue (f i) a b (θ i) := fun i =>
    (hM i).1.mul ((P.virtualValue_bddMeas' i).comp_eval i)
  rw [revenue, integral_finsetSum _ fun i _ => (hM i).2.integrable,
    integral_finsetSum _ fun i _ => (hqφ i).integrable, ← sum_sub_distrib]
  exact sum_congr rfl fun i _ => integral_payment_eq P hM i (hIC i)

variable [Nonempty ι]

variable (f a b) in
/-- The best virtual value at a profile, or zero if all are negative. -/
noncomputable def bestVirtual (θ : ι → ℝ) : ℝ :=
  max 0 (univ.sup' univ_nonempty fun i => virtualValue (f i) a b (θ i))

/-- A feasible allocation earns at most the best virtual value. -/
lemma sum_le_bestVirtual (hM : M.Feasible) (θ : ι → ℝ) :
    ∑ i, M.q i θ * virtualValue (f i) a b (θ i) ≤ bestVirtual a b f θ := by
  obtain ⟨h0, h1⟩ := hM θ
  have hb : 0 ≤ bestVirtual a b f θ := le_max_left _ _
  calc ∑ i, M.q i θ * virtualValue (f i) a b (θ i)
      ≤ ∑ i, M.q i θ * bestVirtual a b f θ := sum_le_sum fun i _ =>
        mul_le_mul_of_nonneg_left ((le_sup' (fun i => virtualValue (f i) a b (θ i))
          (mem_univ i)).trans (le_max_right _ _)) (h0 i)
    _ ≤ bestVirtual a b f θ := by rw [← sum_mul]; exact mul_le_of_le_one_left hb h1

lemma bestVirtual_bddMeas (P : Prior ν f a b) : BddMeas (bestVirtual a b f) := by
  have h := fun i => (P.virtualValue_bddMeas' i).comp_eval (ι := ι) i
  choose C hC using fun i => (h i).2
  have hm := Finset.measurable_sup' univ_nonempty fun i (_ : i ∈ Finset.univ) => (h i).1
  refine ⟨measurable_const.max (by convert hm using 1; ext θ; simp [Finset.sup'_apply]),
    ∑ i, C i, fun θ => ?_⟩
  have hC0 : ∀ i, 0 ≤ C i := fun i => (abs_nonneg _).trans (hC i θ)
  rw [abs_of_nonneg (le_max_left _ _)]
  refine max_le (sum_nonneg fun i _ => hC0 i) (sup'_le _ _ fun i _ => ?_)
  exact (le_abs_self _).trans ((hC i θ).trans
    (single_le_sum (fun j _ => hC0 j) (mem_univ i)))

/-- **Myerson's bound**: a regular, feasible, BIC and interim-IR auction earns at most
`E[max(0, maxᵢ φᵢ(θᵢ))]`. -/
theorem revenue_le (P : Prior ν f a b) (hM : M.Regular) (hF : M.Feasible)
    (hIC : M.BIC ν a b) (hIR : ∀ i, (M.interim ν i).IR a b) :
    M.revenue ν ≤ ∫ θ, bestVirtual a b f θ ∂Measure.pi ν := by
  rw [revenue_eq P hM hIC]
  have hU : 0 ≤ ∑ i, (M.interim ν i).U a :=
    sum_nonneg fun i _ => hIR i a ⟨le_rfl, P.hab⟩
  have := integral_mono ((integrable_finsetSum _ fun i _ =>
    ((hM i).1.mul ((P.virtualValue_bddMeas' i).comp_eval i)).integrable))
    ((bestVirtual_bddMeas P).integrable (μ := Measure.pi ν)) (sum_le_bestVirtual hF)
  linarith

/-! ### Dominant-strategy incentive compatibility implies BIC -/

/-- Bidder `i`'s view of the auction when the others' types are fixed at `θ`. -/
def slice (M : Mechanism ι) (i : ι) (θ : ι → ℝ) : Myerson.Mech :=
  ⟨fun s => M.q i (update θ i s), fun s => M.t i (update θ i s)⟩

lemma slice_integrable (hM : M.Regular) (i : ι) (s' : ℝ) :
    Integrable (fun θ => M.q i (update θ i s')) (Measure.pi ν) ∧
      Integrable (fun θ => M.t i (update θ i s')) (Measure.pi ν) :=
  ⟨BddMeas.integrable ⟨(hM i).1.1.comp (by fun_prop), (hM i).1.2.imp fun _ h θ => h _⟩,
   BddMeas.integrable ⟨(hM i).2.1.comp (by fun_prop), (hM i).2.2.imp fun _ h θ => h _⟩⟩

/-- The interim utility of a report is the average of the ex-post ones. -/
lemma interim_util (hM : M.Regular) (i : ι) (s s' : ℝ) :
    s * (M.interim ν i).q s' - (M.interim ν i).t s' =
      ∫ θ, s * (M.slice i θ).q s' - (M.slice i θ).t s' ∂Measure.pi ν := by
  obtain ⟨hq, ht⟩ := slice_integrable (ν := ν) hM i s'
  change _ = ∫ θ, s * M.q i (update θ i s') - M.t i (update θ i s') ∂_
  rw [integral_sub (hq.const_mul s) ht, integral_const_mul]; rfl

/-- **DSIC ⇒ BIC**: if truth-telling is optimal against every profile of the others' types,
it is optimal on average. -/
lemma bic_of_dsic (hM : M.Regular) (h : ∀ i θ, (M.slice i θ).IC a b) : M.BIC ν a b := by
  intro i s hs s' hs'
  have int := fun s s' => let h := slice_integrable (ν := ν) hM i s'
    (h.1.const_mul s).sub h.2
  rw [interim_util hM, Myerson.Mech.U, interim_util hM]
  exact integral_mono (int s s') (int s s) fun θ => h i θ s hs s' hs'

/-- Likewise ex-post IR gives interim IR, and the interim utility of the lowest type is the
average of the ex-post ones. -/
lemma interim_U (hM : M.Regular) (i : ι) (s : ℝ) :
    (M.interim ν i).U s = ∫ θ, (M.slice i θ).U s ∂Measure.pi ν :=
  interim_util hM i s s

end Mechanism

/-! ### The highest-score auction -/

section HighestScore

open scoped Classical

variable (φ : ι → ℝ → ℝ) (a b : ℝ)

/-- Tie-breaking: a fixed enumeration of the bidders. -/
noncomputable def rank (i : ι) : ℕ := Fintype.equivFin ι i

/-- Bidder `i` wins at `θ`: its score is nonnegative and beats every other score, ties going
to the lower rank. -/
def Wins (θ : ι → ℝ) (i : ι) : Prop :=
  0 ≤ φ i (θ i) ∧ ∀ j ≠ i, φ j (θ j) < φ i (θ i) ∨ (φ j (θ j) = φ i (θ i) ∧ rank i < rank j)

/-- The best nonnegative score. -/
noncomputable def topScore [Nonempty ι] (θ : ι → ℝ) : ℝ :=
  max 0 (univ.sup' univ_nonempty fun i => φ i (θ i))

/-- Clamp a report into `[a, b]`. -/
def clamp (s : ℝ) : ℝ := max a (min s b)

/-- The area under bidder `i`'s allocation curve up to its (clamped) report: the
information rent of the envelope formula. -/
noncomputable def area (i : ι) (θ : ι → ℝ) : ℝ :=
  ∫ r in Ioc a (clamp a b (θ i)), (if Wins φ (update θ i r) i then 1 else 0)

/-- **The highest-score auction**: the item goes to the winner, who pays the threshold
payment `s q(s) - ∫ₐˢ q`, so that losers and the lowest type get zero utility. -/
noncomputable def highestScore : Mechanism ι where
  q i θ := if Wins φ θ i then 1 else 0
  t i θ := clamp a b (θ i) * (if Wins φ θ i then 1 else 0) - area φ a b i θ

variable {φ a b}

lemma wins_unique {θ : ι → ℝ} {i j : ι} (hi : Wins φ θ i) (hj : Wins φ θ j) : i = j := by
  by_contra hne
  have hr : rank i ≠ rank j := fun h => hne ((Fintype.equivFin ι).injective (Fin.ext h))
  rcases hi.2 j (Ne.symm hne) with h₁ | ⟨h₁, h₁'⟩ <;>
    rcases hj.2 i hne with h₂ | ⟨h₂, h₂'⟩ <;> linarith

lemma exists_wins [Nonempty ι] {θ : ι → ℝ} (h : 0 ≤ univ.sup' univ_nonempty fun i => φ i (θ i)) :
    ∃ i, Wins φ θ i := by
  obtain ⟨k, -, hk⟩ := exists_mem_eq_sup' univ_nonempty fun i => φ i (θ i)
  set S := univ.filter fun j => φ j (θ j) = φ k (θ k)
  obtain ⟨i, hiS, hi⟩ := S.exists_min_image rank ⟨k, by simp [S]⟩
  have hi' : φ i (θ i) = φ k (θ k) := (mem_filter.1 hiS).2
  refine ⟨i, by linarith, fun j hj => ?_⟩
  have hjk : φ j (θ j) ≤ φ k (θ k) := hk ▸ le_sup' (fun i => φ i (θ i)) (mem_univ j)
  rcases hjk.lt_or_eq with h' | h'
  · exact Or.inl (by linarith)
  · refine Or.inr ⟨by linarith, (hi j (by simp [S, h'])).lt_of_ne fun h => hj ?_⟩
    exact ((Fintype.equivFin ι).injective (Fin.ext h)).symm

/-- At most one bidder wins, so the sum over bidders picks out the winner (if any). -/
lemma sum_wins (θ : ι → ℝ) (g : ι → ℝ) :
    ∑ i, (if Wins φ θ i then 1 else 0) * g i = if h : ∃ i, Wins φ θ i then g h.choose else 0 := by
  split_ifs with h
  · rw [sum_eq_single h.choose (fun j _ hj => by
      simp [show ¬Wins φ θ j from fun hw => hj (wins_unique hw h.choose_spec)]) (by simp)]
    simp [h.choose_spec]
  · push Not at h; simp [h]

lemma highestScore_feasible : (highestScore φ a b).Feasible := fun θ => by
  refine ⟨fun i => by simp only [highestScore]; split_ifs <;> norm_num, ?_⟩
  have := sum_wins (φ := φ) θ fun _ => 1
  simp only [mul_one] at this
  simp only [highestScore, this]; split_ifs <;> norm_num

/-- The highest-score auction earns, pointwise, the best nonnegative score. -/
lemma highestScore_sum [Nonempty ι] (θ : ι → ℝ) :
    ∑ i, (highestScore φ a b).q i θ * φ i (θ i) = topScore φ θ := by
  simp only [highestScore, sum_wins θ fun i => φ i (θ i), topScore]
  split_ifs with h
  · have hw := h.choose_spec
    refine (max_eq_right (hw.1.trans (le_sup' (fun i => φ i (θ i)) (mem_univ _)))).trans
      (le_antisymm (sup'_le _ _ fun j _ => ?_) (le_sup' (fun i => φ i (θ i)) (mem_univ _))) |>.symm
    by_cases hj : j = h.choose
    · rw [hj]
    · rcases hw.2 j hj with h' | ⟨h', -⟩ <;> linarith
  · refine (max_eq_left ?_).symm
    by_contra h'; exact h (exists_wins (not_le.1 h').le)

/-- Raising one's own report never turns a win into a loss (scores are monotone). -/
lemma wins_mono (hmono : ∀ i, Monotone (φ i)) {θ : ι → ℝ} {i : ι} {s s' : ℝ} (hss : s ≤ s')
    (h : Wins φ (update θ i s) i) : Wins φ (update θ i s') i := by
  have hφ : φ i s ≤ φ i s' := hmono i hss
  simp only [Wins, update_self] at h ⊢
  refine ⟨h.1.trans hφ, fun j hj => ?_⟩
  have := h.2 j hj
  simp only [update_of_ne hj] at this ⊢
  rcases this with h' | ⟨h', h''⟩
  · exact Or.inl (h'.trans_le hφ)
  · rcases hφ.lt_or_eq with hlt | heq
    · exact Or.inl (h' ▸ hlt)
    · exact Or.inr ⟨h'.trans heq, h''⟩

lemma clamp_of_mem {s : ℝ} (hs : s ∈ Icc a b) : clamp a b s = s := by
  simp [clamp, min_eq_left hs.2, max_eq_right hs.1]

/-- In each slice, utility is the area under the allocation curve. -/
lemma highestScore_slice_U {i : ι} {θ : ι → ℝ} {s : ℝ} (hs : s ∈ Icc a b) :
    ((highestScore φ a b).slice i θ).U s = ∫ r in a..s, ((highestScore φ a b).slice i θ).q r := by
  simp only [Myerson.Mech.U, Mechanism.slice, highestScore, area, update_self, update_idem,
    clamp_of_mem hs, intervalIntegral.integral_of_le hs.1]
  rw [sub_sub_cancel]

/-- **The highest-score auction is dominant-strategy IC and ex-post IR.** -/
lemma highestScore_slice_IC_IR (hmono : ∀ i, Monotone (φ i)) (i : ι) (θ : ι → ℝ) :
    ((highestScore φ a b).slice i θ).IC a b ∧ ((highestScore φ a b).slice i θ).IR a b := by
  have hq : ∀ r, 0 ≤ ((highestScore φ a b).slice i θ).q r := fun r => by
    simp only [Mechanism.slice, highestScore]; split_ifs <;> norm_num
  refine ⟨Myerson.Mech.IC_iff.2 ⟨fun s _ s' _ hss => ?_, fun s hs => ?_⟩, fun s hs => ?_⟩
  · simp only [Mechanism.slice, highestScore]
    split_ifs with h h' <;> first | exact absurd (wins_mono hmono hss h) h' | norm_num
  · have ha : a ∈ Icc a b := ⟨le_rfl, hs.1.trans hs.2⟩
    rw [highestScore_slice_U hs, highestScore_slice_U ha, intervalIntegral.integral_same,
      zero_add]
  · rw [highestScore_slice_U hs]
    exact intervalIntegral.integral_nonneg hs.1 fun r _ => hq r

section MeasurableProp

variable {α : Type*} [MeasurableSpace α] {f g : α → ℝ} (hf : Measurable f) (hg : Measurable g)
include hf hg

lemma measurable_le_prop : Measurable fun x => f x ≤ g x :=
  measurableSet_setOfPred.1 (measurableSet_le hf hg)
lemma measurable_lt_prop : Measurable fun x => f x < g x :=
  measurableSet_setOfPred.1 (measurableSet_lt hf hg)
lemma measurable_eq_prop : Measurable fun x => f x = g x :=
  measurableSet_setOfPred.1 (measurableSet_eq_fun hf hg)

end MeasurableProp

lemma measurable_wins (hφ : ∀ i, Measurable (φ i)) (i : ι) :
    Measurable fun θ : ι → ℝ => Wins φ θ i := by
  have hm : ∀ j, Measurable fun θ : ι → ℝ => φ j (θ j) := fun j => (hφ j).comp (by fun_prop)
  exact (measurable_le_prop measurable_const (hm i)).and (Measurable.forall fun j =>
    measurable_const.imp ((measurable_lt_prop (hm j) (hm i)).or
      ((measurable_eq_prop (hm j) (hm i)).and measurable_const)))

lemma abs_clamp_le (s : ℝ) : |clamp a b s| ≤ |a| + |b| := by
  have h₁ : a ≤ clamp a b s := le_max_left _ _
  have h₂ : clamp a b s ≤ max a b := max_le_max le_rfl (min_le_right _ _)
  rw [abs_le]; constructor <;> cases max_cases a b <;>
    linarith [neg_abs_le a, le_abs_self a, neg_abs_le b, le_abs_self b, abs_nonneg a, abs_nonneg b]

lemma measurable_area (hφ : ∀ i, Measurable (φ i)) (i : ι) : Measurable (area φ a b i) := by
  -- the area is an integral of a jointly measurable function of `(θ, r)`
  set F : (ι → ℝ) × ℝ → ℝ := fun p =>
    if (a < p.2 ∧ p.2 ≤ clamp a b (p.1 i)) ∧ Wins φ (update p.1 i p.2) i then 1 else 0
  have hc : Measurable fun p : (ι → ℝ) × ℝ => clamp a b (p.1 i) := by unfold clamp; fun_prop
  have hF : Measurable F := Measurable.ite (((measurable_lt_prop measurable_const
    measurable_snd).and (measurable_le_prop measurable_snd hc)).and
    ((measurable_wins hφ i).comp (by fun_prop))).setOf measurable_const measurable_const
  have : area φ a b i = fun θ => ∫ r, F (θ, r) := by
    ext θ
    rw [area, ← integral_indicator measurableSet_Ioc]
    congr 1; ext r
    simp only [Set.indicator, Set.mem_Ioc, F]
    split_ifs <;> tauto
  exact this ▸ (hF.stronglyMeasurable.integral_prod_right' (ν := volume)).measurable

/-- The area is at most the length of `[a, clamp θᵢ]`. -/
lemma abs_area_le (i : ι) (θ : ι → ℝ) : |area φ a b i θ| ≤ 2 * (|a| + |b|) := by
  have h := norm_setIntegral_le_of_norm_le_const (C := 1) (μ := volume) measure_Ioc_lt_top
    (s := Ioc a (clamp a b (θ i))) (f := fun r => if Wins φ (update θ i r) i then (1 : ℝ) else 0)
    fun r _ => by split_ifs <;> norm_num
  have hac : a ≤ clamp a b (θ i) := le_max_left _ _
  have hc := abs_le.1 (abs_clamp_le (a := a) (b := b) (θ i))
  rw [Real.norm_eq_abs, one_mul, Real.volume_real_Ioc_of_le hac] at h
  rw [area]; linarith [hc.2, neg_abs_le a, abs_nonneg b]

/-- The highest-score auction is regular: allocations and payments are bounded and
measurable. -/
lemma highestScore_regular (hφ : ∀ i, Measurable (φ i)) : (highestScore φ a b).Regular := by
  intro i
  have hq : BddMeas fun θ => (highestScore φ a b).q i θ :=
    ⟨Measurable.ite (measurable_wins hφ i).setOf measurable_const measurable_const,
      1, fun θ => by simp only [highestScore]; split_ifs <;> norm_num⟩
  have hc : Measurable fun θ : ι → ℝ => clamp a b (θ i) := by unfold clamp; fun_prop
  refine ⟨hq, (hc.mul hq.1).sub (measurable_area hφ i), |a| + |b| + 2 * (|a| + |b|),
    fun θ => (abs_sub _ _).trans (add_le_add ?_ (abs_area_le i θ))⟩
  have := abs_clamp_le (a := a) (b := b) (θ i)
  split_ifs <;> simp [this]; positivity

lemma clamp_mem (hab : a ≤ b) (s : ℝ) : clamp a b s ∈ Icc a b :=
  ⟨le_max_left _ _, max_le hab (min_le_right _ _)⟩

lemma clamp_mono : Monotone (clamp a b) := fun _ _ h => max_le_max le_rfl (min_le_min_right b h)

/-- Regularity on `[a, b]` makes the (clamped) virtual value monotone everywhere. -/
lemma virtualValue_monotone (hab : a ≤ b) {g : ℝ → ℝ}
    (hreg : MonotoneOn (virtualValue g a b) (Icc a b)) : Monotone (virtualValue g a b) := by
  have e : ∀ z, virtualValue g a b z = virtualValue g a b (clamp a b z) := fun z => by
    change _ = Myerson.J g a (clamp a b (clamp a b z)) / g (clamp a b (clamp a b z))
    rw [clamp_of_mem (clamp_mem hab z)]; rfl
  exact fun x y hxy => by
    rw [e x, e y]; exact hreg (clamp_mem hab x) (clamp_mem hab y) (clamp_mono hxy)

end HighestScore

/-! ### Myerson's optimal auction -/

variable (f a b) in
/-- **The Myerson auction**: highest nonnegative virtual value wins, at the threshold price. -/
noncomputable def myersonAuction : Mechanism ι :=
  highestScore (fun i => virtualValue (f i) a b) a b

variable [Nonempty ι] {ν}

/-- **Myerson's optimal auction** (1981). Under regularity (virtual values nondecreasing),
the auction that awards the item to the highest nonnegative virtual value, at the threshold
price, is regular, feasible, BIC and interim IR, and earns at least as much as any other
such auction. -/
theorem myerson_optimal (P : Prior ν f a b)
    (hreg : ∀ i, MonotoneOn (virtualValue (f i) a b) (Icc a b)) :
    let A := myersonAuction a b f
    A.Regular ∧ A.Feasible ∧ A.BIC ν a b ∧ (∀ i, (A.interim ν i).IR a b) ∧
      ∀ M : Mechanism ι, M.Regular → M.Feasible → M.BIC ν a b →
        (∀ i, (M.interim ν i).IR a b) → M.revenue ν ≤ A.revenue ν := by
  intro A
  unfold A myersonAuction
  set φ := fun i => virtualValue (f i) a b
  have hmono i := virtualValue_monotone P.hab (hreg i)
  have hA : (highestScore φ a b).Regular := highestScore_regular fun i =>
    (P.virtualValue_bddMeas' i).1
  -- dominant-strategy IC, hence BIC
  have hIC : (highestScore φ a b).BIC ν a b :=
    Mechanism.bic_of_dsic hA fun i θ => (highestScore_slice_IC_IR hmono i θ).1
  -- ex-post IR, hence interim IR, and the lowest type gets nothing
  have hU : ∀ i s, s ∈ Icc a b →
      0 ≤ ((highestScore φ a b).interim ν i).U s ∧ ((highestScore φ a b).interim ν i).U a = 0 :=
    fun i s hs => by
    have ha : a ∈ Icc a b := ⟨le_rfl, P.hab⟩
    rw [Mechanism.interim_U hA, Mechanism.interim_U hA]
    refine ⟨integral_nonneg fun θ => (highestScore_slice_IC_IR hmono i θ).2 s hs, ?_⟩
    simp [highestScore_slice_U ha]
  -- its revenue is Myerson's bound
  refine ⟨hA, highestScore_feasible, hIC, fun i s hs => (hU i s hs).1,
    fun M hM hF hMIC hIR => (Mechanism.revenue_le P hM hF hMIC hIR).trans_eq ?_⟩
  rw [Mechanism.revenue_eq P hA hIC, sum_eq_zero fun i _ => (hU i a ⟨le_rfl, P.hab⟩).2,
    sub_zero]
  exact integral_congr_ae (ae_of_all _ fun θ => (highestScore_sum θ).symm)

end Auction
