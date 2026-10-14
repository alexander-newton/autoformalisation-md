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

end Mechanism

end Auction
