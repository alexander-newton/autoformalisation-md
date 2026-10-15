/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import MechDesign.MomentPrices
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Dworczak–Kolotilin, Theorem 6 and Remark 1: prices from tangent lines

Let `v` be continuously differentiable on `X = [0, 1]` with derivative `v'`. For a set `S` of
moments, `tangentPrice v v' S` is DK's `p_S`, the upper envelope of the tangent lines to `v` at
the points of `S`. **Condition (M)** (`CondM`) for a signal says two things. First, `p_S ≥ v` on
`X`. Second, `p_S(θ) = v m + v'(m) (θ - m)` at every pair `(θ, m)` in the support of the signal.

* **Theorem 6** (`optimal_iff_condM`): a signal is optimal iff (M) holds with `S` the support of
  its posterior means.
* **Remark 1** (`optimal_iff_maxMoments`): given one optimal signal `π*`, a signal is optimal iff
  its means lie in `S* = {x | p_{supp π*_X}(x) = v x}` and (M) holds with `S = S*`.

The "if" directions hold for any prior, with (M) asked on all of `X = [0, 1]` (for a prior
without full support DK ask it only on the convex hull of `supp μ₀`). The "only if" directions
assume the prior has full
support on `[0, 1]`. This is DK's convention `Ω = supp μ₀`, with `X = Ω`, so DK's convex-roof
extension of `p_S` off `Ω` is not needed. Without full support they fail: for `μ₀ = δ_{1/2}` and
`v x = x²`, the only feasible signal is optimal but violates (M).

**Proof, following DK (Appendix A.8).** *If*: `p_S` is a price, and the signal pays its full
cost. *Only if*: take the price for moments `pM` of Theorem 5, which every optimal signal pays
in full. Then `pM = v` at almost every mean, and `pM(θ) = v m + v'(m) (θ - m)` at almost every
pair, because a tangent at a touching point lies below `pM` (`tangent_le`). Both sets are closed,
so they contain the supports. Full support pairs every state with a mean in the support, so
`p_S = pM`. DK use the convex roof of an optimal state price here; in one dimension the price
for moments of Theorem 5 is already convex on `X`.
-/

open MeasureTheory Set unitInterval Filter Topology

namespace MeanPersuasion

variable {v v' : ℝ → ℝ}

/-- DK's `p_S`: the upper envelope of the tangent lines to `v` at the points of `S`. -/
noncomputable def tangentPrice (v v' : ℝ → ℝ) (S : Set ℝ) : ℝ → ℝ := lineSup S v v'

/-- DK's **condition (M)** for a signal and a set `S` of moments: `p_S` lies above `v`, and is
tight on the tangent at every pair `(θ, m)` in the support of the signal. -/
structure CondM (v v' : ℝ → ℝ) (S : Set ℝ) (Sg : Signal) : Prop where
  le : ∀ x ∈ Icc (0 : ℝ) 1, v x ≤ tangentPrice v v' S x
  tight : ∀ z ∈ Sg.π.support, tangentPrice v v' S z.1 = v z.2 + v' z.2 * (z.1 - z.2)

/-- The support of the posterior means, DK's `supp(π_X)`. -/
noncomputable def Signal.meanSupport (Sg : Signal) : Set ℝ := Sg.posteriorMeans.ν.support

lemma lineSup_congr {A : Set ℝ} {V s s' : ℝ → ℝ} (h : EqOn s s' A) :
    lineSup A V s = lineSup A V s' :=
  funext fun _ => iSup_congr fun y => by rw [h y.2]

lemma continuous_extendI_of_continuousOn {f : ℝ → ℝ} (hf : ContinuousOn f (Icc 0 1)) :
    Continuous (extendI f) :=
  hf.comp_continuous (continuous_subtype_val.comp continuous_projIcc)
    fun x => (projIcc (0 : ℝ) 1 zero_le_one x).2

/-! ### Supports -/

namespace Signal

variable {Sg : Signal}

lemma meanSupport_subset : Sg.meanSupport ⊆ Icc 0 1 :=
  Measure.support_subset_of_isClosed isClosed_Icc Sg.posteriorMeans.mem

lemma meanSupport_nonempty : Sg.meanSupport.Nonempty :=
  Measure.nonempty_support (IsProbabilityMeasure.ne_zero _)

lemma support_subset : Sg.π.support ⊆ Icc 0 1 ×ˢ Icc 0 1 :=
  Measure.support_subset_of_isClosed (isClosed_Icc.prod isClosed_Icc) (Sg.state_mem.and Sg.mean_mem)

/-- A pair in the support of the signal has its mean in the support of the means. -/
lemma snd_mem_meanSupport {z : ℝ × ℝ} (hz : z ∈ Sg.π.support) : z.2 ∈ Sg.meanSupport := by
  rw [meanSupport, Measure.mem_support_iff_forall] at *
  exact fun U hU => (hz _ (continuous_snd.continuousAt.preimage_mem_nhds hU)).trans_le
    (Measure.le_map_apply measurable_snd.aemeasurable U)

/-- **Every state in the support of the prior is paired with some mean in the support of the
signal**: the support is compact, so its projection is closed, and it has full measure. -/
lemma exists_mem_support {θ : ℝ} (hθ : θ ∈ Sg.prior.support) : ∃ m, (θ, m) ∈ Sg.π.support := by
  have hK : IsCompact (Prod.fst '' Sg.π.support) :=
    ((isCompact_Icc.prod isCompact_Icc).of_isClosed_subset Measure.isClosed_support
      support_subset).image continuous_fst
  have hae : Prod.fst '' Sg.π.support ∈ ae Sg.prior := by
    rw [prior, mem_ae_iff, Measure.map_apply measurable_fst hK.isClosed.isOpen_compl.measurableSet]
    exact measure_mono_null (fun z hz hzs => hz ⟨z, hzs, rfl⟩) Measure.measure_compl_support
  obtain ⟨z, hz, rfl⟩ := Measure.support_subset_of_isClosed hK.isClosed hae hθ
  exact ⟨z.2, hz⟩

end Signal

/-! ### A tangent below a convex majorant -/

/-- **A tangent below a convex majorant**: if a convex `pM ≥ v` on `[0, 1]` touches `v` at `x`,
the tangent to `v` at `x` stays below `pM` on `[0, 1]`. (DK: let `ε ↓ 0` in the convexity
inequality; here, Fermat's rule along the segment from `x` to `y`.) -/
lemma tangent_le {pM : ℝ → ℝ} (hconv : ConvexOn ℝ univ pM)
    (hle : ∀ x ∈ Icc (0 : ℝ) 1, v x ≤ pM x) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1)
    (hd : HasDerivWithinAt v (v' x) (Icc 0 1) x) (htouch : pM x = v x) {y : ℝ}
    (hy : y ∈ Icc (0 : ℝ) 1) : v x + v' x * (y - x) ≤ pM y := by
  -- along the segment `t ↦ x + t (y - x)`, the chord of `pM` minus `v` is least at `t = 0`
  set f : ℝ → ℝ := fun t => pM x + t * (pM y - pM x) - v (x + t * (y - x))
  have hmem : MapsTo (fun t => x + t * (y - x)) (Icc 0 1) (Icc 0 1) := fun t ht => by
    constructor <;> nlinarith [ht.1, ht.2, hx.1, hx.2, hy.1, hy.2]
  have hmin : IsLocalMinOn f (Icc 0 1) 0 := eventually_of_mem self_mem_nhdsWithin fun t ht => by
    have hc := hconv.2 (mem_univ x) (mem_univ y) (sub_nonneg.2 ht.2) ht.1 (sub_add_cancel 1 t)
    simp only [smul_eq_mul] at hc
    rw [show (1 - t) * x + t * y = x + t * (y - x) by ring] at hc
    have := hle _ (hmem ht)
    simp only [f, zero_mul, add_zero] at this ⊢
    nlinarith
  have h1 : HasDerivWithinAt (fun t => x + t * (y - x)) (y - x) (Icc 0 1) 0 := by
    simpa using ((hasDerivWithinAt_id 0 (Icc 0 1)).mul_const (y - x)).const_add x
  have h2 : HasDerivWithinAt v (v' x) (Icc 0 1) (x + 0 * (y - x)) := by simpa using hd
  have h3 : HasDerivWithinAt (fun t => pM x + t * (pM y - pM x)) (pM y - pM x) (Icc 0 1) 0 := by
    simpa using ((hasDerivWithinAt_id 0 (Icc 0 1)).mul_const (pM y - pM x)).const_add (pM x)
  -- Fermat's rule: the derivative into the segment is nonnegative
  have := hmin.hasFDerivWithinAt_nonneg (h3.sub (h2.comp 0 h1 hmem)).hasFDerivWithinAt (y := 1)
    (mem_posTangentConeAt_of_segment_subset (by simp [segment_eq_Icc]))
  simp at this
  linarith

/-! ### Theorem 6, "if" -/

/-- On `S ⊆ [0, 1]` only the slopes on `[0, 1]` matter. -/
lemma tangentPrice_eq {S : Set ℝ} (hS : S ⊆ Icc 0 1) :
    tangentPrice v v' S = lineSup S v (extendI v') :=
  lineSup_congr fun _ hy => eqOn_extendI (hS hy)

section deriv

variable (hc : ContinuousOn v' (Icc 0 1))
include hc

lemma exists_deriv_bound : ∃ L, ∀ y, |extendI v' y| ≤ L :=
  (isCompact_Icc.exists_bound_of_continuousOn hc).imp fun _ h y =>
    (Real.norm_eq_abs _).symm.trans_le (h _ (projIcc (0 : ℝ) 1 zero_le_one y).2)


/-- **Theorem 6, "if"** (and Remark 1, "if"): condition (M) for a nonempty `S ⊆ [0, 1]` makes the
signal optimal, since `p_S` is a price and the signal pays its full cost. -/
theorem optimal_of_condM (hv : IsPayoff v) {S : Set ℝ} (hS : S ⊆ Icc 0 1) (hne : S.Nonempty)
    {Sg : Signal} (hM : CondM v v' S Sg) :
    ∀ S' : Signal, S'.prior = Sg.prior → S'.value v ≤ Sg.value v := by
  obtain ⟨L, hsL⟩ := exists_deriv_bound hc
  obtain ⟨B, hB⟩ := hv.bdd
  have : Nonempty S := hne.to_subtype
  have hconv : ConvexOn ℝ univ (tangentPrice v v' S) :=
    tangentPrice_eq hS ▸ convexOn_lineSup hS hB hsL
  -- the tangents are tight on the support, which has full measure
  have hae : ∀ᵐ z ∂Sg.π, tangentPrice v v' S z.1 = v z.2 + extendI v' z.2 * (z.1 - z.2) :=
    ((show ∀ᵐ z ∂Sg.π, z ∈ Sg.π.support from Measure.support_mem_ae).and Sg.mean_mem).mono
      fun z ⟨hz, hm⟩ => by rw [hM.tight z hz, ← eqOn_extendI (v := v') hm]
  exact optimal_of_momentPrice hv hconv hM.le (value_eq_of_ae_line hv
    (continuous_of_convexOn hconv) (continuous_extendI_of_continuousOn hc).measurable hsL hae)

end deriv

/-! ### Theorem 6, "only if" -/

/-- The set where `pM` touches `v`, DK's `Š`. -/
def touchSet (v pM : ℝ → ℝ) : Set ℝ := {x | x ∈ Icc (0 : ℝ) 1 ∧ v x = pM x}

section touch

variable (hv : IsPayoff v) (hd : ∀ x ∈ Icc (0 : ℝ) 1, HasDerivWithinAt v (v' x) (Icc 0 1) x)
  (hc : ContinuousOn v' (Icc 0 1)) {pM : ℝ → ℝ} (hconv : ConvexOn ℝ univ pM)
  (hle : ∀ x ∈ Icc (0 : ℝ) 1, v x ≤ pM x) {Sg : Signal}
  (hval : Sg.value v = ∫ θ, pM θ ∂Sg.prior)
include hv hd hc hconv hle hval

omit hv hc hle hval in
lemma isClosed_touchSet : IsClosed (touchSet v pM) := by
  have hvc : ContinuousOn v (Icc 0 1) := fun x hx => (hd x hx).continuousWithinAt
  convert (hvc.sub (continuous_of_convexOn hconv).continuousOn).preimage_isClosed_of_isClosed
    isClosed_Icc (isClosed_singleton (x := (0 : ℝ))) using 1
  ext x; simp [touchSet, sub_eq_zero]

omit hd hc in
/-- **A signal that pays the full cost of `pM` puts its means where `pM` touches `v`**: its value
is at most `∫ pM(m)`, which by Jensen is at most `∫ pM(θ)`, the cost. -/
lemma ae_mem_touchSet : ∀ᵐ z ∂Sg.π, z.2 ∈ touchSet v pM := by
  have hpc := continuous_of_convexOn hconv
  have hi := Signal.integrable_comp hpc continuous_snd Sg.mean_mem
  have hle' : (fun z : ℝ × ℝ => v z.2) ≤ᵐ[Sg.π] fun z => pM z.2 :=
    Sg.mean_mem.mono fun z hz => hle _ hz
  have h := (integral_eq_iff_of_ae_le (Signal.integrable_payoff hv) hi hle').1
    (le_antisymm (integral_mono_ae (Signal.integrable_payoff hv) hi hle')
      ((Sg.integral_mean_le hconv).trans ((Signal.integral_prior hpc).symm.trans hval.symm).le))
  filter_upwards [h, Sg.mean_mem] with z hz hm using ⟨hm, hz⟩

omit hc in
lemma meanSupport_subset_touchSet : Sg.meanSupport ⊆ touchSet v pM :=
  Measure.support_subset_of_isClosed (isClosed_touchSet hd hconv)
    ((ae_map_iff measurable_snd.aemeasurable (isClosed_touchSet hd hconv).measurableSet).2
      (ae_mem_touchSet hv hconv hle hval))

/-- **States lie on the tangent at their mean**, at every pair in the support: tangents at
touching points lie below `pM`, and the signal pays its full cost, so they are tight almost
surely; the pairs where they are tight form a closed set. -/
lemma support_subset_tangent {z : ℝ × ℝ} (hz : z ∈ Sg.π.support) :
    z.1 ∈ Icc (0 : ℝ) 1 ∧ z.2 ∈ touchSet v pM ∧ pM z.1 = v z.2 + v' z.2 * (z.1 - z.2) := by
  obtain ⟨L, hsL⟩ := exists_deriv_bound hc
  have hpc := continuous_of_convexOn hconv
  have hsc := continuous_extendI_of_continuousOn hc
  have hvc := continuous_extendI_of_continuousOn fun x hx => (hd x hx).continuousWithinAt
  have hT := ae_mem_touchSet hv hconv hle hval
  -- tight almost surely
  have hae := ae_line_eq_of_le hv hpc hsc.measurable hsL ((hT.and Sg.state_mem).mono
    fun z ⟨⟨hm, hvm⟩, hθ⟩ => by
      rw [← eqOn_extendI (v := v') hm]; exact tangent_le hconv hle hm (hd _ hm) hvm.symm hθ) hval
  -- on a closed set
  have hΓ : IsClosed {z : ℝ × ℝ | z.1 ∈ Icc (0 : ℝ) 1 ∧ z.2 ∈ touchSet v pM ∧
      pM z.1 = extendI v z.2 + extendI v' z.2 * (z.1 - z.2)} :=
    (isClosed_Icc.preimage continuous_fst).inter (((isClosed_touchSet hd hconv).preimage
      continuous_snd).inter (isClosed_eq (hpc.comp continuous_fst) ((hvc.comp continuous_snd).add
        ((hsc.comp continuous_snd).mul (continuous_fst.sub continuous_snd)))))
  obtain ⟨h1, h2, h3⟩ := Measure.support_subset_of_isClosed hΓ ((hae.and (hT.and Sg.state_mem)).mono
    fun z ⟨h, hm, hθ⟩ => ⟨hθ, hm, by rw [h, ← eqOn_extendI hm.1, ← eqOn_extendI hm.1]⟩) hz
  exact ⟨h1, h2, by rw [h3, ← eqOn_extendI h2.1, ← eqOn_extendI h2.1]⟩

/-- **`p_S = pM` on `[0, 1]`** for a prior of full support, whenever `S` lies between the support
of the means and the touching set: every tangent at a touching point lies below `pM`, and every
state is paired in the support with a mean whose tangent reaches `pM`. -/
lemma tangentPrice_eqOn (hfull : Icc 0 1 ⊆ Sg.prior.support) {S : Set ℝ}
    (hS₁ : Sg.meanSupport ⊆ S) (hS₂ : S ⊆ touchSet v pM) :
    EqOn (tangentPrice v v' S) pM (Icc 0 1) := fun ω hω => by
  obtain ⟨L, hsL⟩ := exists_deriv_bound hc
  obtain ⟨B, hB⟩ := hv.bdd
  have hSI : S ⊆ Icc 0 1 := fun x hx => (hS₂ hx).1
  obtain ⟨m, hm⟩ := Sg.exists_mem_support (hfull hω)
  obtain ⟨-, -, hline⟩ := support_subset_tangent hv hd hc hconv hle hval hm
  have hmS := hS₁ (Signal.snd_mem_meanSupport hm)
  have : Nonempty S := ⟨⟨m, hmS⟩⟩
  refine le_antisymm (ciSup_le fun x =>
    tangent_le hconv hle (hS₂ x.2).1 (hd _ (hS₂ x.2).1) (hS₂ x.2).2.symm hω) ?_
  -- the tangent at `m` reaches `pM ω`
  have := line_le_lineSup hSI hB hsL ⟨m, hmS⟩ ω
  simp only at this hline
  rw [tangentPrice_eq hSI, hline, eqOn_extendI (v := v') (hSI hmS)]
  exact this

/-- `p_S = pM` on `[0, 1]` gives condition (M). -/
lemma condM_of_eqOn {S : Set ℝ} (h : EqOn (tangentPrice v v' S) pM (Icc 0 1)) :
    CondM v v' S Sg :=
  ⟨fun x hx => (hle x hx).trans_eq (h hx).symm, fun z hz => by
    obtain ⟨h1, -, h3⟩ := support_subset_tangent hv hd hc hconv hle hval hz
    rw [h h1, h3]⟩

end touch

variable {μ : Measure ℝ} [IsProbabilityMeasure μ] (hμ : ∀ᵐ θ ∂μ, θ ∈ Icc (0 : ℝ) 1)
  (hv : IsPayoff v) (hd : ∀ x ∈ Icc (0 : ℝ) 1, HasDerivWithinAt v (v' x) (Icc 0 1) x)
  (hc : ContinuousOn v' (Icc 0 1))
include hμ hv hd hc

/-- **The price for moments of Theorem 5** for a continuously differentiable `v`: a convex price
above `v` that every optimal signal pays in full. -/
lemma exists_tight_price : ∃ pM : ℝ → ℝ, ConvexOn ℝ univ pM ∧ (∀ x ∈ Icc (0 : ℝ) 1, v x ≤ pM x) ∧
    ∀ Sg : Signal, Sg.prior = μ → (∀ S' : Signal, S'.prior = μ → S'.value v ≤ Sg.value v) →
      Sg.value v = ∫ θ, pM θ ∂Sg.prior := by
  obtain ⟨L, hL⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
  -- the mean value theorem makes `v` Lipschitz
  have hLip : ∀ x ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (0 : ℝ) 1, v y ≤ v x + L * |x - y| :=
    fun x hx y hy => by
      have := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hd hL (convex_Icc 0 1) hx hy
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_sub_comm y x] at this
      linarith [le_abs_self (v y - v x)]
  obtain ⟨p, hp, hopt⟩ := exists_optimal_statePrice hLip hμ hv
  obtain ⟨pM, _, -, ⟨hconv, -, hle⟩, -, h⟩ := momentPrice_spec hμ hv hLip hp hopt
  exact ⟨pM, hconv, hle, fun Sg hS hSopt => hS ▸ (h Sg hS hSopt).1⟩

variable (hfull : Icc 0 1 ⊆ μ.support)
include hfull

/-- **Theorem 6** of Dworczak–Kolotilin, in one dimension: for `v` continuously differentiable on
`[0, 1]` and a prior of full support, a signal is optimal if and only if condition (M) holds
with `S` the support of its posterior means. -/
theorem optimal_iff_condM {Sg : Signal} (hS : Sg.prior = μ) :
    (∀ S' : Signal, S'.prior = μ → S'.value v ≤ Sg.value v) ↔
      CondM v v' Sg.meanSupport Sg := by
  refine ⟨fun hopt => ?_, fun hM S' hS' => optimal_of_condM hc hv Signal.meanSupport_subset
    Signal.meanSupport_nonempty hM S' (hS'.trans hS.symm)⟩
  obtain ⟨pM, hconv, hle, h⟩ := exists_tight_price hμ hv hd hc
  have hval := h Sg hS hopt
  exact condM_of_eqOn hv hd hc hconv hle hval (tangentPrice_eqOn hv hd hc hconv hle hval
    (by rw [hS]; exact hfull) subset_rfl (meanSupport_subset_touchSet hv hd hconv hle hval))

/-- DK's **maximal set of optimal moments**, `S* = {x | p_{supp π*_X}(x) = v x}`, built from one
optimal signal `π*`. -/
def maxMoments (v v' : ℝ → ℝ) (Sstar : Signal) : Set ℝ :=
  {x | x ∈ Icc (0 : ℝ) 1 ∧ tangentPrice v v' Sstar.meanSupport x = v x}

/-- **Remark 1** of Dworczak–Kolotilin: given one optimal signal `π*`, a signal is optimal if and
only if its posterior means lie in `S*` and condition (M) holds with `S = S*`. -/
theorem optimal_iff_maxMoments {Sstar : Signal} (hSstar : Sstar.prior = μ)
    (hstar : ∀ S' : Signal, S'.prior = μ → S'.value v ≤ Sstar.value v) {Sg : Signal}
    (hS : Sg.prior = μ) :
    (∀ S' : Signal, S'.prior = μ → S'.value v ≤ Sg.value v) ↔
      Sg.meanSupport ⊆ maxMoments v v' Sstar ∧ CondM v v' (maxMoments v v' Sstar) Sg := by
  obtain ⟨pM, hconv, hle, h⟩ := exists_tight_price hμ hv hd hc
  -- `S*` is the set where `pM` touches `v`
  have hval := h Sstar hSstar hstar
  have hE := tangentPrice_eqOn hv hd hc hconv hle hval (by rw [hSstar]; exact hfull) subset_rfl
    (meanSupport_subset_touchSet hv hd hconv hle hval)
  have hmax : maxMoments v v' Sstar = touchSet v pM :=
    ext fun x => and_congr_right fun hx => by rw [hE hx, eq_comm]
  rw [hmax]
  refine ⟨fun hopt => ?_, fun ⟨hsub, hM⟩ S' hS' => optimal_of_condM hc hv (fun x hx => hx.1)
    (Signal.meanSupport_nonempty.mono hsub) hM S' (hS'.trans hS.symm)⟩
  have hval' := h Sg hS hopt
  have hsub := meanSupport_subset_touchSet hv hd hconv hle hval'
  exact ⟨hsub, condM_of_eqOn hv hd hc hconv hle hval' (tangentPrice_eqOn hv hd hc hconv hle hval'
    (by rw [hS]; exact hfull) hsub subset_rfl)⟩

end MeanPersuasion
