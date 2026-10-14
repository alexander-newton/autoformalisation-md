/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import MechDesign.Hull

/-!
# The type-space hull is the concave hull of the revenue curve

Textbooks (Bulow–Roberts 1989) iron in *sale-probability* coordinates. Selling with probability
`q` takes the price `P(q) = F⁻¹(1 - q)` and earns `R(q) = q P(q)`; the ironed revenue curve is
the least concave majorant `R̄` of `R` on `[0, 1]`. `Hull.lean` irons in type space instead.

The two agree. The cumulative virtual surplus is `G(p) = a - R(1 - F p)` (each tail of `J` is
a posted-price revenue), and `M ↦ (θ ↦ a - M(1 - F θ))` turns concave majorants of `R` into
`F`-convex minorants of `G` and back. Hence `Ĝ(p) = a - R̄(1 - F p)` (`hull_eq_concaveHull`),
and every chord slope of `Ĝ`, from which the ironed virtual value is built, is a chord slope of
`R̄` (`fslope_hull_eq_slope`): the ironed virtual value is marginal ironed revenue.
-/

open MeasureTheory Set intervalIntegral Myerson

set_option linter.unusedSectionVars false

namespace Ironing

variable {a b : ℝ} {F K M g : ℝ → ℝ}

/-! ### From concavity in the sale probability to `F`-convexity and back -/

/-- A concave function of the sale probability `1 - F`, turned upside down, is `F`-convex. -/
lemma fconvex_of_concaveOn (c : ℝ) (hM : ConcaveOn ℝ (Icc 0 1) M)
    (hF : StrictMonoOn F (Icc a b)) (hF01 : ∀ θ ∈ Icc a b, F θ ∈ Icc (0 : ℝ) 1) :
    FConvex F (fun θ => c - M (1 - F θ)) a b := by
  intro x hx y hy z hxz hzy
  have hz : z ∈ Icc a b := ⟨hx.1.trans hxz.le, hzy.le.trans hy.2⟩
  have h₁ := hF hx hz hxz
  have h₂ := hF hz hy hzy
  have mem : ∀ θ ∈ Icc a b, 1 - F θ ∈ Icc (0 : ℝ) 1 := fun θ hθ => by
    have := hF01 θ hθ; constructor <;> linarith [this.1, this.2]
  -- the three types become sale probabilities `1 - F y < 1 - F z < 1 - F x`
  have h := hM.slope_anti_adjacent (mem y hy) (mem x hx) (by linarith) (by linarith)
    (y := 1 - F z)
  rw [div_le_div_iff₀ (by linarith) (by linarith)] at h
  linear_combination h

/-- An `F`-convex function, read through an inverse `g` of `F` and turned upside down, is
concave in the sale probability. -/
lemma concaveOn_of_fconvex (c : ℝ) (hK : FConvex F K a b) (hF : MonotoneOn F (Icc a b))
    (hg : ∀ u ∈ Icc (0 : ℝ) 1, g u ∈ Icc a b ∧ F (g u) = u) :
    ConcaveOn ℝ (Icc 0 1) (fun q => c - K (g (1 - q))) := by
  refine concaveOn_of_slope_anti_adjacent (convex_Icc 0 1) fun {u v w} hu hw huv hvw => ?_
  have flip : ∀ q ∈ Icc (0 : ℝ) 1, 1 - q ∈ Icc (0 : ℝ) 1 := fun q hq => by
    constructor <;> linarith [hq.1, hq.2]
  obtain ⟨hx, hFx⟩ := hg _ (flip w hw)
  obtain ⟨hz, hFz⟩ := hg _ (flip v ⟨hu.1.trans huv.le, hvw.le.trans hw.2⟩)
  obtain ⟨hy, hFy⟩ := hg _ (flip u hu)
  -- the three sale probabilities become types `g (1 - w) < g (1 - v) < g (1 - u)`
  have lt : ∀ {s t}, s ∈ Icc a b → t ∈ Icc a b → F s < F t → s < t := fun hs ht h =>
    lt_of_not_ge fun h' => (hF ht hs h').not_gt h
  have h := hK _ hx _ hy _ (lt hx hz (by rw [hFx, hFz]; linarith))
    (lt hz hy (by rw [hFz, hFy]; linarith))
  rw [hFx, hFy, hFz] at h
  rw [div_le_div_iff₀ (by linarith) (by linarith)]
  linear_combination h

/-! ### Inverting the quantile -/

/-- The inverse of `F` on `[a, b]`. -/
noncomputable def finv (F : ℝ → ℝ) (a b u : ℝ) : ℝ := Function.invFunOn F (Icc a b) u

/-- A continuous `F` takes every intermediate value, so `finv` inverts it. -/
lemma finv_spec (hab : a ≤ b) (hFc : ContinuousOn F (Icc a b)) {u : ℝ}
    (hu : u ∈ Icc (F a) (F b)) : finv F a b u ∈ Icc a b ∧ F (finv F a b u) = u := by
  have h : u ∈ F '' Icc a b := intermediate_value_Icc hab hFc hu
  exact ⟨Function.invFunOn_mem h, Function.invFunOn_eq h⟩

lemma finv_apply (hF : StrictMonoOn F (Icc a b)) (hFc : ContinuousOn F (Icc a b)) {θ : ℝ}
    (hθ : θ ∈ Icc a b) : finv F a b (F θ) = θ := by
  have hab := hθ.1.trans hθ.2
  have h := finv_spec hab hFc
    ⟨hF.monotoneOn ⟨le_rfl, hab⟩ hθ hθ.1, hF.monotoneOn hθ ⟨hab, le_rfl⟩ hθ.2⟩
  exact hF.injOn h.1 hθ h.2

/-! ### The revenue curve -/

variable {f : ℝ → ℝ}

variable (f) in
/-- The price at which the good sells with probability `q`: `P(q) = F⁻¹(1 - q)`. -/
noncomputable def priceAt (a b q : ℝ) : ℝ := finv (cdf f a) a b (1 - q)

variable (f) in
/-- **The revenue curve** `R(q) = q P(q)`: revenue as a function of the sale probability. -/
noncomputable def revenueCurve (a b q : ℝ) : ℝ := q * priceAt f a b q

/-- **The concave hull** of `R` on `[0, 1]`: its least concave majorant. -/
noncomputable def concaveHull (R : ℝ → ℝ) (q : ℝ) : ℝ :=
  sInf ((fun M => M q) '' {M | ConcaveOn ℝ (Icc 0 1) M ∧ ∀ r ∈ Icc (0 : ℝ) 1, R r ≤ M r})

/-- **The cumulative virtual surplus is the revenue curve upside down**:
`G(p) = a - p (1 - F p)`, because each tail of `J` is a posted-price revenue. -/
lemma cumJ_eq (hf : ContinuousOn f (Icc a b)) (hF : ∫ s in a..b, f s = 1) {p : ℝ}
    (hp : p ∈ Icc a b) : cumJ f a p = a - p * (1 - cdf f a p) := by
  have hab := hp.1.trans hp.2
  have ha : a ∈ Icc a b := ⟨le_rfl, hab⟩
  have hJi : ∀ y ∈ Icc a b, IntervalIntegrable (J f a) volume a y := fun y hy =>
    ((J_continuousOn hab hf).mono (by
      rw [uIcc_of_le hab, uIcc_of_le hy.1]; exact Icc_subset_Icc_right hy.2)).intervalIntegrable
  -- `∫ₐᵖ J = ∫ₐᵇ J - ∫ₚᵇ J`, and both tails are posted-price revenues
  have h := integral_interval_sub_left (hJi b ⟨hab, le_rfl⟩) (hJi p hp)
  rw [tail_J_eq hp hf hF, revenue_postedPrice hp hf hF] at h
  have h' := tail_J_eq ha hf hF
  rw [revenue_postedPrice ha hf hF, cdf, integral_same, sub_zero, mul_one] at h'
  rw [cumJ]; linarith

/-- **The ironed revenue curve in type space is the concave hull of the revenue curve**
(Bulow–Roberts 1989): `Ĝ(p) = a - R̄(1 - F p)`. -/
theorem hull_eq_concaveHull (hab : a < b) (hf : ContinuousOn f (Icc a b))
    (hpos : ∀ θ ∈ Icc a b, 0 < f θ) (hF : ∫ s in a..b, f s = 1) {p : ℝ} (hp : p ∈ Icc a b) :
    hull (cdf f a) (cumJ f a) a b p = a - concaveHull (revenueCurve f a b) (1 - cdf f a p) := by
  obtain ⟨L, S⟩ := hullSetting hab hf hpos
  set F := cdf f a with hFdef
  set R := revenueCurve f a b
  have hFa : F a = 0 := integral_same
  have hFb : F b = 1 := hF
  have hF01 : ∀ θ ∈ Icc a b, F θ ∈ Icc (0 : ℝ) 1 := fun θ hθ => by
    rw [← hFa, ← hFb]
    exact ⟨S.mono.monotoneOn S.left_mem hθ hθ.1, S.mono.monotoneOn hθ S.right_mem hθ.2⟩
  have hg : ∀ u ∈ Icc (0 : ℝ) 1, finv F a b u ∈ Icc a b ∧ F (finv F a b u) = u :=
    fun u hu => finv_spec hab.le S.cont (by rwa [hFa, hFb])
  have flip : ∀ q ∈ Icc (0 : ℝ) 1, 1 - q ∈ Icc (0 : ℝ) 1 := fun q hq => by
    constructor <;> linarith [hq.1, hq.2]
  -- `G` and `R` determine each other
  have hGR : ∀ θ ∈ Icc a b, cumJ f a θ = a - R (1 - F θ) := fun θ hθ => by
    rw [cumJ_eq hf hF hθ]
    simp only [R, revenueCurve, priceAt, sub_sub_cancel, ← hFdef, finv_apply S.mono S.cont hθ]
    ring
  have hRG : ∀ q ∈ Icc (0 : ℝ) 1, R q = a - cumJ f a (finv F a b (1 - q)) := fun q hq => by
    obtain ⟨hmem, hinv⟩ := hg _ (flip q hq)
    simp only [R, revenueCurve, priceAt, ← hFdef]
    rw [cumJ_eq hf hF hmem, ← hFdef, hinv]
    ring
  -- the hull, read in sale-probability coordinates, is a concave majorant of `R`
  set M₀ := fun q => a - hull F (cumJ f a) a b (finv F a b (1 - q))
  have hM₀ : M₀ ∈ {M | ConcaveOn ℝ (Icc 0 1) M ∧ ∀ r ∈ Icc (0 : ℝ) 1, R r ≤ M r} :=
    ⟨concaveOn_of_fconvex a S.hull_fconvex S.mono.monotoneOn hg, fun r hr => by
      rw [hRG r hr]; linarith [S.hull_le (hg _ (flip r hr)).1]⟩
  have hq := flip _ (hF01 p hp)
  refine le_antisymm ?_ ?_
  · -- `R̄ ≤ M₀`
    have hbdd : BddBelow ((fun M : ℝ → ℝ => M (1 - F p)) ''
        {M | ConcaveOn ℝ (Icc 0 1) M ∧ ∀ r ∈ Icc (0 : ℝ) 1, R r ≤ M r}) :=
      ⟨R (1 - F p), by rintro _ ⟨M, hM, rfl⟩; exact hM.2 _ hq⟩
    have := csInf_le hbdd ⟨M₀, hM₀, rfl⟩
    simp only [M₀, sub_sub_cancel, finv_apply S.mono S.cont hp] at this
    rw [concaveHull]; linarith
  · -- every concave majorant of `R`, turned upside down, is an `F`-convex minorant of `G`
    have : a - hull F (cumJ f a) a b p ≤ concaveHull R (1 - F p) := by
      refine le_csInf ⟨_, M₀, hM₀, rfl⟩ ?_
      rintro _ ⟨M, hM, rfl⟩
      have hK : (fun θ => a - M (1 - F θ)) ∈ minorants F (cumJ f a) a b :=
        ⟨fconvex_of_concaveOn a hM.1 S.mono hF01, fun θ hθ => by
          rw [hGR θ hθ]; linarith [hM.2 _ (flip _ (hF01 θ hθ))]⟩
      linarith [S.le_hull hK hp]
    linarith

/-- **The ironed virtual value is marginal ironed revenue.** Every quantile chord slope of the
type-space hull, from which `ironedValue` is built, is the chord slope of the concave hull of
the revenue curve between the corresponding sale probabilities. -/
theorem fslope_hull_eq_slope (hab : a < b) (hf : ContinuousOn f (Icc a b))
    (hpos : ∀ θ ∈ Icc a b, 0 < f θ) (hF : ∫ s in a..b, f s = 1) {x y : ℝ} (hx : x ∈ Icc a b)
    (hy : y ∈ Icc a b) :
    fslope (cdf f a) (hull (cdf f a) (cumJ f a) a b) x y =
      slope (concaveHull (revenueCurve f a b)) (1 - cdf f a y) (1 - cdf f a x) := by
  rw [fslope, slope_def_field, hull_eq_concaveHull hab hf hpos hF hx,
    hull_eq_concaveHull hab hf hpos hF hy]
  rw [show 1 - cdf f a x - (1 - cdf f a y) = cdf f a y - cdf f a x by ring]
  ring

end Ironing
