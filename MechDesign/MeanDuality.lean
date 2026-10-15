/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import MechDesign.MeanPersuasion
import MechDesign.Duality
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.Topology.UnitInterval
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Strong duality for persuasion with a continuum of states

For posterior-mean payoffs this is Kolotilin (2018, Theorem 1) and Dworczak–Martini (2019); it
is the posterior-mean case of Dworczak–Kolotilin (2024).

The sender chooses a distribution `ν` of posterior means; feasibility is that `ν` is a
mean-preserving contraction of the prior `μ` (`PosteriorMeans`, as in Kolotilin 2018). The dual
chooses a price: a convex `p ≥ V` on `[0, 1]`.

**Theorem** (`strong_duality`): for bounded upper semicontinuous `V`, an optimal distribution
of posterior means exists, and its value equals the least expected cost of a price
(`priceValue`).

The proof is one separation. In `C([0, 1]) × ℝ` the pairs `(g, t)` with `g < p - V` and
`∫ p dμ < t` for some convex `p` form an open convex set missing `(0, priceValue)`. Pushing the
set down makes the separating functional positive, so by Riesz–Markov–Kakutani it is a
probability measure `ν`. The separation inequality says that `ν` is a contraction of `μ`
on which every continuous `W > V` is worth at least the dual value; the Lipschitz envelopes
`lipEnv` decrease to `V`, so `V` is too (`le_integral_of_forall_lt`).
-/

open MeasureTheory Set unitInterval CompactlySupported

namespace MeanPersuasion

variable {μ : Measure ℝ} {V p : ℝ → ℝ}

lemma integrable_of_mem {ν : Measure ℝ} [IsFiniteMeasure ν] (h : ∀ᵐ x ∂ν, x ∈ Icc (0 : ℝ) 1)
    {f : ℝ → ℝ} (hf : IsPayoff f) : Integrable f ν :=
  let ⟨B, hB⟩ := hf.bdd
  (integrable_const B).mono' hf.measurable.aestronglyMeasurable (h.mono fun _ hx => hB _ hx)

/-! ### Distributions of posterior means and the dual value -/

/-- A **distribution of posterior means** for the prior `μ`: a law `ν` on `[0, 1]` that is a
mean-preserving contraction of `μ`: every convex function has a smaller mean under `ν`. -/
structure PosteriorMeans (μ : Measure ℝ) where
  ν : Measure ℝ
  [isProb : IsProbabilityMeasure ν]
  mem : ∀ᵐ m ∂ν, m ∈ Icc (0 : ℝ) 1
  contraction : ∀ q : ℝ → ℝ, ConvexOn ℝ univ q → ∫ m, q m ∂ν ≤ ∫ θ, q θ ∂μ

attribute [instance] PosteriorMeans.isProb

/-- The **dual value**: the least expected cost of a price. (Meaningful when `μ` is a
probability measure on `[0, 1]`, so that prices are bounded below in cost.) -/
noncomputable def priceValue (V : ℝ → ℝ) (μ : Measure ℝ) : ℝ :=
  ⨅ p : {p // IsPrice V p}, ∫ θ, p.1 θ ∂μ

/-- A constant above `V` is a price. -/
lemma exists_isPrice_const (hV : IsPayoff V) : ∃ B, IsPrice V fun _ => B :=
  let ⟨B, hB⟩ := hV.bdd
  ⟨B, convexOn_const B convex_univ, fun x hx => (le_abs_self _).trans (hB x hx)⟩

/-- **Weak duality**: no distribution of posterior means beats the cost of a price. -/
theorem PosteriorMeans.value_le (G : PosteriorMeans μ) (hV : IsPayoff V) :
    ∫ m, V m ∂G.ν ≤ priceValue V μ := by
  obtain ⟨B, hB⟩ := exists_isPrice_const hV
  have : Nonempty {p // IsPrice V p} := ⟨⟨_, hB⟩⟩
  -- `∫ V dν ≤ ∫ p dν ≤ ∫ p dμ`
  exact le_ciInf fun p => (integral_mono_ae (integrable_of_mem G.mem hV)
    (integrable_of_mem G.mem (.of_continuous p.2.continuous))
    (G.mem.mono fun m h => p.2.le m h)).trans (G.contraction p.1 p.2.convex)

/-- The law of the posterior mean of a signal is a distribution of posterior means. -/
noncomputable def Signal.posteriorMeans (S : Signal) : PosteriorMeans S.prior where
  ν := S.π.map Prod.snd
  mem := (ae_map_iff measurable_snd.aemeasurable measurableSet_Icc).2 S.mean_mem
  contraction q hq := by
    rw [integral_map measurable_snd.aemeasurable
      (continuous_of_convexOn hq).aestronglyMeasurable, Signal.integral_prior
      (continuous_of_convexOn hq)]
    exact S.integral_mean_le hq

lemma Signal.value_eq (S : Signal) (hV : IsPayoff V) :
    S.value V = ∫ m, V m ∂S.posteriorMeans.ν :=
  (integral_map measurable_snd.aemeasurable hV.measurable.aestronglyMeasurable).symm

variable [IsProbabilityMeasure μ]

lemma priceValue_le (hμ : ∀ᵐ θ ∂μ, θ ∈ Icc (0 : ℝ) 1) (hV : IsPayoff V) (hp : IsPrice V p) :
    priceValue V μ ≤ ∫ θ, p θ ∂μ :=
  ciInf_le ⟨∫ θ, V θ ∂μ, by
    rintro _ ⟨q, rfl⟩
    exact integral_mono_ae (integrable_of_mem hμ hV)
      (integrable_of_mem hμ (.of_continuous q.2.continuous)) (hμ.mono fun θ h => q.2.le θ h)⟩
    (⟨p, hp⟩ : {p // IsPrice V p})

/-! ### The separation -/

/-- A continuous function on `ℝ`, restricted to `[0, 1]`. -/
def onI (f : ℝ → ℝ) (hf : Continuous f) : C(I, ℝ) := ⟨fun x => f x, hf.comp continuous_subtype_val⟩

lemma onI_zero : onI (fun _ => (0 : ℝ)) continuous_const = 0 := by ext; simp [onI]

lemma onI_const (k : ℝ) : onI (fun _ => k) continuous_const = k • 1 := by ext; simp [onI]

lemma const_eq_smul (k : ℝ) : ContinuousMap.const I k = k • 1 := by ext; simp

/-- The pairs `(g, t)` strictly dominated by a convex `p`: `g < p - V` on `[0, 1]` and
`∫ p dμ < t`. -/
def Dominated (V : ℝ → ℝ) (μ : Measure ℝ) : Set (C(I, ℝ) × ℝ) :=
  {a | ∃ p : ℝ → ℝ, ConvexOn ℝ univ p ∧ (∀ x : I, a.1 x < p x - V x) ∧ ∫ θ, p θ ∂μ < a.2}

/-- A convex combination of strict inequalities is strict. -/
lemma wavg_lt {s t u₁ u₂ w₁ w₂ : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) (hst : s + t = 1)
    (h₁ : u₁ < w₁) (h₂ : u₂ < w₂) : s * u₁ + t * u₂ < s * w₁ + t * w₂ := by
  rcases hs.eq_or_lt with rfl | hs
  · rw [zero_add] at hst; subst hst; linarith
  · nlinarith [mul_lt_mul_of_pos_left h₁ hs, mul_le_mul_of_nonneg_left h₂.le ht]

lemma convex_dominated (hμ : ∀ᵐ θ ∂μ, θ ∈ Icc (0 : ℝ) 1) : Convex ℝ (Dominated V μ) := by
  rintro a ⟨p, hp, hlt, hint⟩ b ⟨q, hq, hlt', hint'⟩ s t hs ht hst
  have hpi := integrable_of_mem hμ (.of_continuous (continuous_of_convexOn hp))
  have hqi := integrable_of_mem hμ (.of_continuous (continuous_of_convexOn hq))
  refine ⟨fun x => s * p x + t * q x, (hp.smul hs).add (hq.smul ht), fun x => ?_, ?_⟩
  · have e : s * (p x - V x) + t * (q x - V x) = s * p x + t * q x - V x := by
      linear_combination (-V x) * hst
    simpa [e] using wavg_lt hs ht hst (hlt x) (hlt' x)
  · rw [integral_add (hpi.const_mul s) (hqi.const_mul t), integral_const_mul, integral_const_mul]
    simpa using wavg_lt hs ht hst hint hint'

omit [IsProbabilityMeasure μ] in
lemma isOpen_dominated (hV : UpperSemicontinuous V) : IsOpen (Dominated V μ) := by
  rw [Metric.isOpen_iff]
  rintro a ⟨p, hp, hlt, hint⟩
  -- the gap `p - V - g` is lower semicontinuous, so has a positive minimum on `[0, 1]`
  have hlsc : LowerSemicontinuous fun x : I => (p x - a.1 x) + -V x :=
    (((continuous_of_convexOn hp).comp continuous_subtype_val).sub
      a.1.continuous).lowerSemicontinuous.add (hV.neg.comp continuous_subtype_val)
  obtain ⟨x₀, -, hx₀⟩ :=
    LowerSemicontinuousOn.exists_isMinOn univ_nonempty isCompact_univ (hlsc.lowerSemicontinuousOn _)
  have hδ : 0 < p x₀ - V x₀ - a.1 x₀ := by linarith [hlt x₀]
  refine ⟨min (p x₀ - V x₀ - a.1 x₀) (a.2 - ∫ θ, p θ ∂μ), lt_min hδ (by linarith),
    fun b hb => ⟨p, hp, fun x => ?_, ?_⟩⟩
  · rw [Metric.mem_ball, Prod.dist_eq, max_lt_iff] at hb
    have h1 := (le_abs_self _).trans_eq (Real.dist_eq _ _).symm |>.trans
      (ContinuousMap.dist_apply_le_dist (f := b.1) (g := a.1) x)
    have h2 := isMinOn_iff.1 hx₀ x (mem_univ x)
    linarith [hb.1.trans_le (min_le_left _ _)]
  · rw [Metric.mem_ball, Prod.dist_eq, max_lt_iff, Real.dist_eq] at hb
    linarith [neg_abs_le (b.2 - a.2), hb.2.trans_le (min_le_right _ _)]

lemma not_mem_dominated (hμ : ∀ᵐ θ ∂μ, θ ∈ Icc (0 : ℝ) 1) (hV : IsPayoff V) :
    ((0 : C(I, ℝ)), priceValue V μ) ∉ Dominated V μ := by
  rintro ⟨p, hp, hlt, hint⟩
  -- a strictly dominating `p` would be a price cheaper than every price
  have : IsPrice V p := ⟨hp, fun x hx => by have := hlt ⟨x, hx⟩; simp at this; linarith⟩
  exact hint.not_ge (priceValue_le hμ hV this)

variable {B : ℝ}

omit [IsProbabilityMeasure μ] in
/-- Convex `q`, lowered by `B + δ` and by `h ≥ 0`, dominates when `V ≤ B`. -/
lemma mem_dominated (hB : ∀ x ∈ Icc (0 : ℝ) 1, V x ≤ B) {q : ℝ → ℝ} (hq : ConvexOn ℝ univ q)
    {δ : ℝ} (hδ : 0 < δ) {h : C(I, ℝ)} (hh : 0 ≤ h) {s : ℝ} (hs : 0 ≤ s) :
    (onI q (continuous_of_convexOn hq) - (B + δ) • 1 - h, ∫ θ, q θ ∂μ + δ + s) ∈ Dominated V μ :=
  ⟨q, hq, fun x => by
    have h0 : (0 : ℝ) ≤ h x := hh x
    have := hB x x.2; simp [onI]; linarith, by linarith⟩

omit [IsProbabilityMeasure μ] in
/-- A continuous `W > V` gives the dominated pair `(-W, δ)`, through the zero price. -/
lemma mem_dominated_of_lt {W : ℝ → ℝ} (hW : Continuous W) (hVW : ∀ x ∈ Icc (0 : ℝ) 1, V x < W x)
    {δ : ℝ} (hδ : 0 < δ) : (-onI W hW, δ) ∈ Dominated V μ :=
  ⟨fun _ => 0, convexOn_const 0 convex_univ, fun x => by simp [onI]; linarith [hVW x x.2],
    by simpa using hδ⟩

/-- The `C([0, 1])` part of a functional on `C([0, 1]) × ℝ`. -/
noncomputable def coordL (f : StrongDual ℝ (C(I, ℝ) × ℝ)) : C(I, ℝ) →L[ℝ] ℝ :=
  f.comp (ContinuousLinearMap.inl ℝ C(I, ℝ) ℝ)

lemma apply_prod (f : StrongDual ℝ (C(I, ℝ) × ℝ)) (g : C(I, ℝ)) (t : ℝ) :
    f (g, t) = coordL f g + t * f (0, 1) := by
  have : ((g, t) : C(I, ℝ) × ℝ) = ContinuousLinearMap.inl ℝ C(I, ℝ) ℝ g + t • (0, 1) := by
    ext <;> simp
  rw [this, map_add, map_smul, smul_eq_mul]; rfl

/-- A real `x` with `x + δ k < y` for every `δ > 0` is at most `y`. -/
lemma le_of_forall_pos_add_mul_lt {x y k : ℝ} (h : ∀ δ : ℝ, 0 < δ → x + δ * k < y) : x ≤ y := by
  by_contra hxy; push Not at hxy
  have hd : 0 < (x - y) / (2 * (|k| + 1)) := div_pos (by linarith) (by positivity)
  have := h _ hd
  have hk : (x - y) / (2 * (|k| + 1)) * |k| ≤ (x - y) / 2 := by
    rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) two_pos]
    nlinarith [abs_nonneg k]
  nlinarith [neg_abs_le k, mul_le_mul_of_nonneg_left (neg_abs_le k) hd.le]

/-- A real `b` with `s b ≤ u` for every `s ≥ 0` is nonpositive. -/
lemma nonpos_of_forall_le {b u : ℝ} (h : ∀ s : ℝ, 0 ≤ s → s * b ≤ u) : b ≤ 0 :=
  Duality.nonpos_of_forall_lt (a := 0) (u := u + 1) fun s hs => by linarith [h s hs]

/-- A positive functional vanishing at `1` vanishes. -/
lemma eq_zero_of_pos (L : C(I, ℝ) →L[ℝ] ℝ) (hpos : ∀ h, 0 ≤ h → 0 ≤ L h) (h1 : L 1 = 0)
    (g : C(I, ℝ)) : L g = 0 := by
  -- `g` lies between `-‖g‖` and `‖g‖`
  have hb : ∀ x, |g x| ≤ ‖g‖ := fun x => (Real.norm_eq_abs _).symm.trans_le (g.norm_coe_le_norm x)
  have hu := hpos (‖g‖ • 1 - g) (ContinuousMap.le_def.2 fun x => by
    simpa using (le_abs_self _).trans (hb x))
  have hl := hpos (g + ‖g‖ • 1) (ContinuousMap.le_def.2 fun x => by
    have := neg_le_of_abs_le (hb x); simp; linarith)
  rw [map_sub, map_smul, h1] at hu; rw [map_add, map_smul, h1] at hl
  simp at hu hl; linarith

/-- `f` **separates** the dominated pairs from `(0, D)`, in the coordinates
`f (g, t) = coordL f g + t f (0, 1)`. -/
def Separates (f : StrongDual ℝ (C(I, ℝ) × ℝ)) (V : ℝ → ℝ) (μ : Measure ℝ) (D : ℝ) : Prop :=
  ∀ a ∈ Dominated V μ, coordL f a.1 + a.2 * f (0, 1) < D * f (0, 1)

/-- **Hahn–Banach**: some functional separates the dominated pairs from `(0, priceValue)`. -/
lemma exists_separates (hμ : ∀ᵐ θ ∂μ, θ ∈ Icc (0 : ℝ) 1) (hV : IsPayoff V)
    (hVu : UpperSemicontinuous V) : ∃ f, Separates f V μ (priceValue V μ) := by
  obtain ⟨f, hf⟩ := geometric_hahn_banach_open_point (convex_dominated hμ) (isOpen_dominated hVu)
    (not_mem_dominated hμ hV)
  refine ⟨f, fun ⟨g, t⟩ ha => ?_⟩
  have := hf _ ha
  rwa [apply_prod f g t, apply_prod f 0 (priceValue V μ), map_zero, zero_add] at this

namespace Separates

omit [IsProbabilityMeasure μ]

variable {f : StrongDual ℝ (C(I, ℝ) × ℝ)} {D : ℝ}

/-- The separation on the pairs of `mem_dominated`. -/
lemma key (hf : Separates f V μ D) (hB : ∀ x ∈ Icc (0 : ℝ) 1, V x ≤ B) {q : ℝ → ℝ}
    (hq : ConvexOn ℝ univ q) {δ : ℝ} (hδ : 0 < δ) {h : C(I, ℝ)} (hh : 0 ≤ h) {s : ℝ} (hs : 0 ≤ s) :
    coordL f (onI q (continuous_of_convexOn hq)) - (B + δ) * coordL f 1 - coordL f h
      + (∫ θ, q θ ∂μ + δ + s) * f (0, 1) < D * f (0, 1) := by
  have := hf _ (mem_dominated hB hq hδ hh hs)
  rwa [map_sub, map_sub, map_smul, smul_eq_mul] at this

lemma zero_price (hf : Separates f V μ D) (hB : ∀ x ∈ Icc (0 : ℝ) 1, V x ≤ B) {δ : ℝ}
    (hδ : 0 < δ) {h : C(I, ℝ)} (hh : 0 ≤ h) {s : ℝ} (hs : 0 ≤ s) :
    -(B + δ) * coordL f 1 - coordL f h + (δ + s) * f (0, 1) < D * f (0, 1) := by
  have := hf.key hB (convexOn_const 0 convex_univ) hδ hh hs
  rw [onI_zero, map_zero, integral_zero, zero_add] at this; linarith

/-- Pushing the pairs up in `t`: `f (0, 1) ≤ 0`. -/
lemma coord_nonpos (hf : Separates f V μ D) (hB : ∀ x ∈ Icc (0 : ℝ) 1, V x ≤ B) :
    f (0, 1) ≤ 0 :=
  Duality.nonpos_of_forall_lt (a := -(B + 1) * coordL f 1 + f (0, 1)) (u := D * f (0, 1))
    fun s hs => by have := hf.zero_price hB one_pos le_rfl hs; rw [map_zero] at this; linarith

/-- Pushing the pairs down in `g`: `coordL f` is positive. -/
lemma pos (hf : Separates f V μ D) (hB : ∀ x ∈ Icc (0 : ℝ) 1, V x ≤ B) {h : C(I, ℝ)}
    (hh : 0 ≤ h) : 0 ≤ coordL f h := by
  have := nonpos_of_forall_le (b := -coordL f h)
    (u := D * f (0, 1) + (B + 1) * coordL f 1 - f (0, 1)) fun k hk => by
    have := hf.zero_price hB one_pos (h := k • h)
      (ContinuousMap.le_def.2 fun x => by simpa using mul_nonneg hk (ContinuousMap.le_def.1 hh x))
      le_rfl
    rw [map_smul, smul_eq_mul] at this; linarith
  linarith

/-- Letting `δ → 0`. -/
lemma lim (hf : Separates f V μ D) (hB : ∀ x ∈ Icc (0 : ℝ) 1, V x ≤ B) (q : ℝ → ℝ)
    (hq : ConvexOn ℝ univ q) : coordL f (onI q (continuous_of_convexOn hq)) - B * coordL f 1
      + (∫ θ, q θ ∂μ) * f (0, 1) ≤ D * f (0, 1) :=
  le_of_forall_pos_add_mul_lt (k := f (0, 1) - coordL f 1) fun δ hδ => by
    have := hf.key hB hq hδ le_rfl le_rfl; rw [map_zero] at this; linarith

/-- The value side: `-coordL f W ≤ D f (0, 1)` for every continuous `W > V`. -/
lemma value (hf : Separates f V μ D) {W : ℝ → ℝ} (hW : Continuous W)
    (hVW : ∀ x ∈ Icc (0 : ℝ) 1, V x < W x) : -coordL f (onI W hW) ≤ D * f (0, 1) :=
  le_of_forall_pos_add_mul_lt (k := f (0, 1)) fun δ hδ => by
    have := hf _ (mem_dominated_of_lt (μ := μ) hW hVW hδ); rwa [map_neg] at this

/-- `f (0, 1) ≠ 0`: otherwise constant prices force `coordL f = 0`, and then `f` separates
nothing. -/
lemma coord_neg (hf : Separates f V μ D) (hB : ∀ x ∈ Icc (0 : ℝ) 1, V x ≤ B) : f (0, 1) < 0 :=
  (hf.coord_nonpos hB).lt_of_ne fun hz => by
    have h1 : coordL f 1 ≤ 0 := nonpos_of_forall_le (u := B * coordL f 1) fun k _ => by
      have := hf.lim hB _ (convexOn_const k convex_univ)
      rw [onI_const, map_smul, smul_eq_mul, hz] at this; linarith
    have hL := eq_zero_of_pos _ (fun _ => hf.pos hB)
      (le_antisymm h1 (hf.pos hB (ContinuousMap.le_def.2 fun _ => by simp)))
    have := hf.zero_price hB one_pos le_rfl le_rfl
    rw [hL, hL, hz] at this; simp at this

end Separates

/-- **The separation, normalised.** For bounded upper semicontinuous `V` (with `V ≤ B` on
`[0, 1]`) there is a positive functional `Λ` on `C([0, 1])` with `Λ p - B Λ 1 ≤ ∫ p dμ -
priceValue` for every convex `p`, and `Λ W ≥ priceValue` for every continuous `W > V`. -/
theorem exists_functional (hμ : ∀ᵐ θ ∂μ, θ ∈ Icc (0 : ℝ) 1) (hV : IsPayoff V)
    (hVu : UpperSemicontinuous V) (hB : ∀ x ∈ Icc (0 : ℝ) 1, V x ≤ B) :
    ∃ Λ : C(I, ℝ) →L[ℝ] ℝ, (∀ h, 0 ≤ h → 0 ≤ Λ h) ∧ (∀ q (hq : ConvexOn ℝ univ q),
      Λ (onI q (continuous_of_convexOn hq)) - B * Λ 1 ≤ ∫ θ, q θ ∂μ - priceValue V μ) ∧
      ∀ W (hW : Continuous W), (∀ x ∈ Icc (0 : ℝ) 1, V x < W x) →
        priceValue V μ ≤ Λ (onI W hW) := by
  obtain ⟨f, hf⟩ := exists_separates hμ hV hVu
  have hc := hf.coord_neg hB
  -- divide by `-f (0, 1) > 0`
  refine ⟨(-f (0, 1))⁻¹ • coordL f, fun h hh => ?_, fun q hq => ?_, fun W hW hVW => ?_⟩
  · exact mul_nonneg (inv_nonneg.2 (by linarith)) (hf.pos hB hh)
  · simp only [smul_apply, smul_eq_mul]
    rw [← mul_assoc, mul_comm B, mul_assoc, ← mul_sub, inv_mul_le_iff₀ (by linarith)]
    linarith [hf.lim hB q hq]
  · simp only [smul_apply, smul_eq_mul]
    rw [le_inv_mul_iff₀ (by linarith)]; linarith [hf.value hW hVW]

lemma onI_smul {q : ℝ → ℝ} (hq : Continuous q) (k : ℝ) :
    onI (fun x => k • q x) (hq.const_smul k) = k • onI q hq := by ext; simp [onI]

/-- **Reading the functional**: `Λ` is normalised and lies below `μ` on convex functions. -/
lemma functional_spec {Λ : C(I, ℝ) →L[ℝ] ℝ} {D : ℝ}
    (hΛ : ∀ q (hq : ConvexOn ℝ univ q), Λ (onI q (continuous_of_convexOn hq)) - B * Λ 1 ≤
      ∫ θ, q θ ∂μ - D) :
    Λ 1 = 1 ∧
      ∀ q (hq : ConvexOn ℝ univ q), Λ (onI q (continuous_of_convexOn hq)) ≤ ∫ θ, q θ ∂μ := by
  -- constant prices `k`: `k (Λ 1 - 1) ≤ B Λ 1 - D` for every real `k`
  have hk : ∀ k : ℝ, k * (Λ 1 - 1) ≤ B * Λ 1 - D := fun k => by
    have := hΛ _ (convexOn_const k convex_univ)
    rw [onI_const, map_smul, smul_eq_mul, integral_const] at this; simp at this; linarith
  have hle : Λ 1 - 1 ≤ 0 := nonpos_of_forall_le fun k _ => hk k
  have hge : 1 - Λ 1 ≤ 0 := nonpos_of_forall_le (u := B * Λ 1 - D)
    fun k _ => by linarith [hk (-k)]
  refine ⟨by linarith, fun q hq => ?_⟩
  -- scaled prices `s q`: `s (Λ q - ∫ q dμ) ≤ B Λ 1 - D` for every `s ≥ 0`
  have := nonpos_of_forall_le (b := Λ (onI q (continuous_of_convexOn hq)) - ∫ θ, q θ ∂μ)
      (u := B * Λ 1 - D) fun s hs => by
    have := hΛ _ (hq.smul hs)
    rw [onI_smul (continuous_of_convexOn hq), map_smul, smul_eq_mul] at this
    simp only [smul_eq_mul, integral_const_mul] at this
    linarith
  linarith

/-- **Riesz–Markov–Kakutani on a compact space**: a positive functional on `C(X, ℝ)` is
integration against a finite measure. -/
lemma exists_measure_of_pos {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [MeasurableSpace X] [BorelSpace X] (Λ : C(X, ℝ) →ₗ[ℝ] ℝ) (hpos : ∀ h, 0 ≤ h → 0 ≤ Λ h) :
    ∃ π : Measure X, IsFiniteMeasure π ∧ ∀ f : C(X, ℝ), ∫ x, f x ∂π = Λ f := by
  let Λc : C_c(X, ℝ) →ₚ[ℝ] ℝ :=
    { toFun g := Λ ⟨g, g.continuous⟩
      map_add' g g' := by rw [← map_add]; rfl
      map_smul' k g := by rw [RingHom.id_apply, ← map_smul]; rfl
      monotone' g g' hgg' := by
        have := hpos (⟨g', g'.continuous⟩ - ⟨g, g.continuous⟩)
          (ContinuousMap.le_def.2 fun x => by simpa using hgg' x)
        rw [map_sub] at this; linarith }
  exact ⟨RealRMK.rieszMeasure Λc, inferInstance, fun f =>
    RealRMK.integral_rieszMeasure Λc ⟨f, HasCompactSupport.of_compactSpace _⟩⟩

/-- A finite measure of total integral one is a probability measure. -/
lemma isProbabilityMeasure_of_integral_one {X : Type*} [MeasurableSpace X] {π : Measure X}
    [IsFiniteMeasure π] (h : ∫ _, (1 : ℝ) ∂π = 1) : IsProbabilityMeasure π := by
  rw [integral_const, smul_eq_mul, mul_one] at h
  exact ⟨by rw [← ENNReal.ofReal_toReal (measure_ne_top _ univ), ← measureReal_def, h,
    ENNReal.ofReal_one]⟩

/-- **Riesz–Markov–Kakutani on `[0, 1]`**: a positive functional with `Λ 1 = 1` is integration
against a probability measure on `[0, 1]`. -/
lemma exists_measure (Λ : C(I, ℝ) →L[ℝ] ℝ) (hpos : ∀ h, 0 ≤ h → 0 ≤ Λ h) (h1 : Λ 1 = 1) :
    ∃ ν : Measure ℝ, IsProbabilityMeasure ν ∧ (∀ᵐ m ∂ν, m ∈ Icc (0 : ℝ) 1) ∧
      ∀ f (hf : Continuous f), ∫ m, f m ∂ν = Λ (onI f hf) := by
  obtain ⟨νI, hfin, hint⟩ := exists_measure_of_pos Λ.toLinearMap hpos
  have hm := continuous_subtype_val.measurable.aemeasurable (μ := νI)
  have hint' : ∀ f (hf : Continuous f), ∫ m, f m ∂(νI.map Subtype.val) = Λ (onI f hf) :=
    fun f hf => by rw [integral_map hm hf.aestronglyMeasurable]; exact hint (onI f hf)
  refine ⟨_, isProbabilityMeasure_of_integral_one ?_,
    (ae_map_iff hm measurableSet_Icc).2 (ae_of_all _ fun x => x.2), hint'⟩
  rw [hint' _ continuous_const, onI_const, one_smul, h1]

/-! ### Approximating `V` from above -/

/-- The `k`-Lipschitz upper envelope `x ↦ sup_{y ∈ [0, 1]} (V y - k |x - y|)`. -/
noncomputable def lipEnv (V : ℝ → ℝ) (k x : ℝ) : ℝ := ⨆ y : I, (V y - k * |x - y|)

section lipEnv

variable (hB : ∀ x ∈ Icc (0 : ℝ) 1, V x ≤ B) {k : ℝ} (hk : 0 ≤ k)
include hB hk

lemma lipEnv_bdd (x : ℝ) : BddAbove (range fun y : I => V y - k * |x - y|) :=
  ⟨B, by rintro _ ⟨y, rfl⟩; nlinarith [hB y y.2, abs_nonneg (x - y)]⟩

lemma le_lipEnv {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) : V x ≤ lipEnv V k x :=
  le_ciSup_of_le (lipEnv_bdd hB hk x) ⟨x, hx⟩ (by simp)

lemma lipEnv_le (x : ℝ) : lipEnv V k x ≤ B :=
  ciSup_le fun y => by nlinarith [hB y y.2, abs_nonneg (x - y)]

lemma continuous_lipEnv : Continuous (lipEnv V k) :=
  (LipschitzWith.of_le_add_mul' k fun x x' => ciSup_le fun y => by
    -- moving `x` to `x'` costs at most `k |x - x'|`
    have h₁ : |x' - y| - |x - y| ≤ |x - x'| := by
      have := abs_sub_abs_le_abs_sub (x' - y) (x - y)
      rwa [show x' - y - (x - y) = -(x - x') by ring, abs_neg] at this
    have h := le_ciSup (lipEnv_bdd hB hk x') y
    rw [Real.dist_eq]
    nlinarith [mul_le_mul_of_nonneg_left h₁ hk]).continuous

end lipEnv

/-- **The envelopes decrease to an upper semicontinuous `V`.** -/
lemma tendsto_lipEnv (hB : ∀ x ∈ Icc (0 : ℝ) 1, V x ≤ B) (hVu : UpperSemicontinuous V) {x : ℝ}
    (hx : x ∈ Icc (0 : ℝ) 1) :
    Filter.Tendsto (fun n : ℕ => lipEnv V n x) Filter.atTop (nhds (V x)) := by
  refine tendsto_order.2 ⟨fun a ha => Filter.Eventually.of_forall fun n =>
    ha.trans_le (le_lipEnv hB n.cast_nonneg hx), fun a ha => ?_⟩
  -- near `x`, `V` is below `(V x + a) / 2`; far from `x`, the penalty `n |x - y|` wins
  obtain ⟨δ, hδ, hnear⟩ := Metric.eventually_nhds_iff.1 (hVu x ((V x + a) / 2) (by linarith))
  filter_upwards [Filter.eventually_ge_atTop ⌈(B - V x) / δ⌉₊] with n hn
  have hnδ : B - V x ≤ n * δ := by
    have := (div_le_iff₀ hδ).1 ((Nat.le_ceil _).trans (Nat.cast_le.2 hn)); linarith
  refine lt_of_le_of_lt (ciSup_le fun y => ?_) (show (V x + a) / 2 < a by linarith)
  rcases lt_or_ge (dist (y : ℝ) x) δ with h | h
  · nlinarith [hnear h, abs_nonneg (x - y), (n.cast_nonneg : (0 : ℝ) ≤ n)]
  · rw [Real.dist_eq, abs_sub_comm] at h
    nlinarith [hB y y.2, mul_le_mul_of_nonneg_left h n.cast_nonneg]

/-- **Testing on continuous majorants**: if every continuous `W > V` on `[0, 1]` has
`∫ W dν ≥ D`, then `∫ V dν ≥ D`, for bounded upper semicontinuous `V`. Test the envelopes
`lipEnv V n + 1 / (n + 1)`, which decrease to `V`, and pass to the limit. -/
lemma le_integral_of_forall_lt {ν : Measure ℝ} [IsProbabilityMeasure ν]
    (hν : ∀ᵐ x ∂ν, x ∈ Icc (0 : ℝ) 1) (hV : IsPayoff V) (hVu : UpperSemicontinuous V) {D : ℝ}
    (h : ∀ W, Continuous W → (∀ x ∈ Icc (0 : ℝ) 1, V x < W x) → D ≤ ∫ x, W x ∂ν) :
    D ≤ ∫ x, V x ∂ν := by
  obtain ⟨B, hB⟩ := hV.bdd
  have hB' : ∀ x ∈ Icc (0 : ℝ) 1, V x ≤ B := fun x hx => (le_abs_self _).trans (hB x hx)
  set W : ℕ → ℝ → ℝ := fun n x => lipEnv V n x + 1 / (n + 1)
  have hε : ∀ n : ℕ, 0 < 1 / ((n : ℝ) + 1) ∧ 1 / ((n : ℝ) + 1) ≤ 1 := fun n =>
    ⟨by positivity, by rw [div_le_one (by positivity)]; linarith [n.cast_nonneg (α := ℝ)]⟩
  have hWc : ∀ n, Continuous (W n) := fun n =>
    (continuous_lipEnv hB' n.cast_nonneg).add continuous_const
  -- `V < W n ≤ B + 1` on `[0, 1]`, and `W n → V`
  have hlt : ∀ n, ∀ x ∈ Icc (0 : ℝ) 1, V x < W n x := fun n x hx => by
    linarith [le_lipEnv hB' n.cast_nonneg hx, (hε n).1]
  have hlim := tendsto_integral_of_dominated_convergence (μ := ν) (F := W) (fun _ => B + 1)
    (fun n => (hWc n).aestronglyMeasurable) (integrable_const _) (fun n => by
      filter_upwards [hν] with x hx
      rw [Real.norm_eq_abs, abs_le]
      constructor <;> linarith [hlt n x hx, (abs_le.1 (hB x hx)).1,
        lipEnv_le hB' (k := n) n.cast_nonneg x, (hε n).2])
    (by filter_upwards [hν] with x hx
        simpa only [W, add_zero] using
          (tendsto_lipEnv hB' hVu hx).add tendsto_one_div_add_atTop_nhds_zero_nat)
  exact ge_of_tendsto' hlim fun n => h _ (hWc n) (hlt n)

/-- **Strong duality** (Kolotilin 2018; Dworczak–Martini 2019; Dworczak–Kolotilin 2024). With
a bounded upper semicontinuous payoff, some distribution of posterior means is optimal, and its
value equals the least expected cost of a price. -/
theorem strong_duality (hμ : ∀ᵐ θ ∂μ, θ ∈ Icc (0 : ℝ) 1) (hV : IsPayoff V)
    (hVu : UpperSemicontinuous V) :
    ∃ G : PosteriorMeans μ, (∀ G' : PosteriorMeans μ, ∫ m, V m ∂G'.ν ≤ ∫ m, V m ∂G.ν) ∧
      ∫ m, V m ∂G.ν = priceValue V μ := by
  obtain ⟨B, hB⟩ := hV.bdd
  obtain ⟨Λ, hpos, hΛ, hval⟩ :=
    exists_functional hμ hV hVu fun x hx => (le_abs_self _).trans (hB x hx)
  obtain ⟨h1, hcon⟩ := functional_spec hΛ
  obtain ⟨ν, hν, hmem, hint⟩ := exists_measure Λ hpos h1
  -- the separating measure is a distribution of posterior means worth the dual value
  let G : PosteriorMeans μ :=
    { ν := ν, mem := hmem, contraction := fun q hq => (hint q _).trans_le (hcon q hq) }
  have hG : ∫ m, V m ∂G.ν = priceValue V μ := le_antisymm (G.value_le hV)
    (le_integral_of_forall_lt hmem hV hVu fun W hW hVW => (hint W hW).symm ▸ hval W hW hVW)
  exact ⟨G, fun G' => hG ▸ G'.value_le hV, hG⟩

/-- Full disclosure: the prior is a distribution of posterior means. -/
def PosteriorMeans.full (hμ : ∀ᵐ θ ∂μ, θ ∈ Icc (0 : ℝ) 1) : PosteriorMeans μ :=
  { ν := μ, mem := hμ, contraction := fun _ _ => le_rfl }

/-- For convex `V` the dual value is `∫ V dμ`: `V` is its own price, and full disclosure
attains it. -/
theorem priceValue_of_convexOn (hμ : ∀ᵐ θ ∂μ, θ ∈ Icc (0 : ℝ) 1) (hV : ConvexOn ℝ univ V) :
    priceValue V μ = ∫ θ, V θ ∂μ :=
  have hc := IsPayoff.of_continuous (continuous_of_convexOn hV)
  le_antisymm (priceValue_le hμ hc ⟨hV, fun _ _ => le_rfl⟩) ((PosteriorMeans.full hμ).value_le hc)

/-- Every signal is worth at most the dual value. -/
theorem Signal.value_le_priceValue (S : Signal) (hV : IsPayoff V) :
    S.value V ≤ priceValue V S.prior :=
  (S.value_eq hV).trans_le (S.posteriorMeans.value_le hV)

end MeanPersuasion
