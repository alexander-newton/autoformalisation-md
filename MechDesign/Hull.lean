/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import MechDesign.Ironing

/-!
# Existence of ironings: the convex hull in quantile coordinates

Measure types by their quantile `F`. A function is `F`-*convex* if it is convex in that
coordinate. Myerson's ironed revenue curve `Ĝ` is the largest `F`-convex function below
`G(p) = ∫ₐᵖ J`, and the ironed virtual value `φ̄` is its right `F`-slope. Then:

* `φ̄` is monotone and bounded, by the three-chord lemma;
* `Ĝ(p) = ∫ₐᵖ φ̄ f`, because `φ̄` `F`-supports both sides (`Myerson.FSupports.sub_eq`), so the
  gap `G - Ĝ` is nonnegative and closes at the endpoints;
* where the gap is open, replacing `Ĝ` by a chord would give a larger `F`-convex minorant,
  so `Ĝ` is affine there and `φ̄` is flat.

Hence every continuous positive density admits an ironing (`exists_ironed`), and Myerson's
optimal auction exists for every such prior (`Auction.exists_optimal_auction`).
-/

open MeasureTheory Set intervalIntegral

set_option linter.unusedSectionVars false

namespace Ironing

variable {a b : ℝ} {F K K' : ℝ → ℝ}

/-! ### Convexity in quantile coordinates -/

/-- `K` is **`F`-convex** on `[a, b]`: convex once types are measured by `F`. -/
def FConvex (F K : ℝ → ℝ) (a b : ℝ) : Prop :=
  ∀ x ∈ Icc a b, ∀ y ∈ Icc a b, ∀ z, x < z → z < y →
    (F y - F x) * K z ≤ (F y - F z) * K x + (F z - F x) * K y

/-- The `F`-slope of `K` between `x` and `y`. -/
noncomputable def fslope (F K : ℝ → ℝ) (x y : ℝ) : ℝ := (K y - K x) / (F y - F x)

/-- `F`-affine functions are `F`-convex. -/
lemma fconvex_affine (α β : ℝ) : FConvex F (fun θ => α + β * F θ) a b :=
  fun _ _ _ _ _ _ _ => le_of_eq (by ring)

/-- The maximum of two `F`-convex functions is `F`-convex. -/
lemma FConvex.max (hK : FConvex F K a b) (hK' : FConvex F K' a b)
    (hF : StrictMonoOn F (Icc a b)) : FConvex F (fun θ => max (K θ) (K' θ)) a b := by
  intro x hx y hy z hxz hzy
  have hz : z ∈ Icc a b := ⟨hx.1.trans hxz.le, hzy.le.trans hy.2⟩
  have h₁ : 0 ≤ F y - F z := sub_nonneg.2 (hF.le_iff_le hz hy |>.2 hzy.le)
  have h₂ : 0 ≤ F z - F x := sub_nonneg.2 (hF.le_iff_le hx hz |>.2 hxz.le)
  have h₃ : 0 ≤ F y - F x := by linarith
  simp only
  rcases le_total (K z) (K' z) with h | h
  · rw [max_eq_right h]
    exact (hK' x hx y hy z hxz hzy).trans (by gcongr <;> simp)
  · rw [max_eq_left h]
    exact (hK x hx y hy z hxz hzy).trans (by gcongr <;> simp)

/-- **Three-chord lemma**: `F`-slopes of an `F`-convex function increase. -/
lemma FConvex.fslope_le (hK : FConvex F K a b) (hF : StrictMonoOn F (Icc a b))
    {x y z : ℝ} (hx : x ∈ Icc a b) (hy : y ∈ Icc a b) (hxz : x < z) (hzy : z < y) :
    fslope F K x z ≤ fslope F K x y ∧ fslope F K x y ≤ fslope F K z y := by
  have hz : z ∈ Icc a b := ⟨hx.1.trans hxz.le, hzy.le.trans hy.2⟩
  have hA : 0 < F z - F x := sub_pos.2 (hF hx hz hxz)
  have hB : 0 < F y - F z := sub_pos.2 (hF hz hy hzy)
  have hC : 0 < F y - F x := by linarith
  have h := hK x hx y hy z hxz hzy
  unfold fslope
  constructor
  · rw [div_le_div_iff₀ hA hC]; nlinarith
  · rw [div_le_div_iff₀ hC hB]; nlinarith

/-- The chord of `K` through `x₀` and `y₀`, as an `F`-affine function. -/
noncomputable def chord (F K : ℝ → ℝ) (x₀ y₀ θ : ℝ) : ℝ := K x₀ + fslope F K x₀ y₀ * (F θ - F x₀)

lemma chord_right {x₀ y₀ : ℝ} (h : F x₀ ≠ F y₀) : chord F K x₀ y₀ y₀ = K y₀ := by
  unfold chord fslope; field_simp [sub_ne_zero.2 h.symm]; ring

lemma fslope_chord {x₀ y₀ x y : ℝ} (h : F x ≠ F y) :
    fslope F (chord F K x₀ y₀) x y = fslope F K x₀ y₀ := by
  rw [fslope, show chord F K x₀ y₀ y - chord F K x₀ y₀ x = fslope F K x₀ y₀ * (F y - F x) by
    unfold chord; ring, mul_div_assoc, div_self (sub_ne_zero.2 h.symm), mul_one]

/-- Between its ends, a chord lies above an `F`-convex function. -/
lemma FConvex.le_chord (hK : FConvex F K a b) (hF : StrictMonoOn F (Icc a b)) {x₀ y₀ θ : ℝ}
    (hx₀ : x₀ ∈ Icc a b) (hy₀ : y₀ ∈ Icc a b) (hθ : θ ∈ Icc x₀ y₀) (hlt : x₀ < y₀) :
    K θ ≤ chord F K x₀ y₀ θ := by
  rcases hθ.1.eq_or_lt with rfl | h₁
  · simp [chord]
  rcases hθ.2.eq_or_lt with rfl | h₂
  · rw [chord_right (hF.injOn.ne hx₀ hy₀ hlt.ne)]
  have := (hK.fslope_le hF hx₀ hy₀ h₁ h₂).1
  have hpos : 0 < F θ - F x₀ := sub_pos.2 (hF hx₀ ⟨hx₀.1.trans h₁.le, h₂.le.trans hy₀.2⟩ h₁)
  rw [fslope, div_le_iff₀ hpos] at this
  unfold chord; linarith

/-- Beyond its ends, a chord lies below an `F`-convex function. -/
lemma FConvex.chord_le (hK : FConvex F K a b) (hF : StrictMonoOn F (Icc a b)) {x₀ y₀ θ : ℝ}
    (hx₀ : x₀ ∈ Icc a b) (hy₀ : y₀ ∈ Icc a b) (hθ : θ ∈ Icc a b) (hlt : x₀ < y₀)
    (hout : θ ∉ Ioo x₀ y₀) : chord F K x₀ y₀ θ ≤ K θ := by
  rcases lt_or_ge θ x₀ with h | h
  · -- left of the chord: the slope from `θ` to `x₀` is at most the chord's
    have h₁ := hK.fslope_le hF hθ hy₀ h hlt
    have hpos : 0 < F x₀ - F θ := sub_pos.2 (hF hθ hx₀ h)
    have := h₁.1.trans h₁.2
    rw [show fslope F K θ x₀ = (K x₀ - K θ) / (F x₀ - F θ) from rfl, div_le_iff₀ hpos] at this
    unfold chord; linarith
  rcases h.eq_or_lt with rfl | h
  · simp [chord]
  have hy : y₀ ≤ θ := by by_contra hc; exact hout ⟨h, not_le.1 hc⟩
  rcases hy.eq_or_lt with rfl | h'
  · rw [chord_right (hF.injOn.ne hx₀ hy₀ hlt.ne)]
  · -- right of the chord: the slope from `y₀` to `θ` is at least the chord's
    have h₁ := hK.fslope_le hF hx₀ hθ hlt h'
    have hpos : 0 < F θ - F y₀ := sub_pos.2 (hF hy₀ hθ h')
    have := h₁.1.trans h₁.2
    rw [show fslope F K y₀ θ = (K θ - K y₀) / (F θ - F y₀) from rfl, le_div_iff₀ hpos] at this
    have e := chord_right (K := K) (hF.injOn.ne hx₀ hy₀ hlt.ne)
    unfold chord at e ⊢; linarith

/-- **A monotone function `F`-supports its weighted integral** (the quantile version of
`MonotoneOn.supports_integral`): if `F` is the primitive of a density `f ≥ 0`, then
`(F y - F x) φ x ≤ ∫ₓʸ φ f ≤ (F y - F x) φ y`. -/
lemma fsupports_integral {φ f : ℝ → ℝ} (hab : a ≤ b) (hφ : MonotoneOn φ (Icc a b))
    (hint : IntervalIntegrable (fun θ => φ θ * f θ) volume a b) (hf : ContinuousOn f (Icc a b))
    (hf0 : ∀ θ ∈ Icc a b, 0 ≤ f θ) (hFf : ∀ x ∈ Icc a b, F x - F a = ∫ θ in a..x, f θ) :
    Myerson.FSupports F φ (fun x => ∫ θ in a..x, φ θ * f θ) (Icc a b) := by
  have ha : a ∈ Icc a b := ⟨le_rfl, hab⟩
  have sub : ∀ x ∈ Icc a b, ∀ y ∈ Icc a b, uIcc x y ⊆ uIcc a b := fun x hx y hy => by
    rw [uIcc_of_le hab]; exact uIcc_subset_Icc hx hy
  have hfi : ∀ x ∈ Icc a b, ∀ y ∈ Icc a b, IntervalIntegrable f volume x y :=
    fun x hx y hy => (hf.mono (uIcc_subset_Icc hx hy)).intervalIntegrable
  have hφi : ∀ x ∈ Icc a b, ∀ y ∈ Icc a b, IntervalIntegrable (fun θ => φ θ * f θ) volume x y :=
    fun x hx y hy => hint.mono_set (sub x hx y hy)
  intro x hx y hy hxy
  have hθ : ∀ θ ∈ Icc x y, θ ∈ Icc a b := fun θ hθ => ⟨hx.1.trans hθ.1, hθ.2.trans hy.2⟩
  -- increments of `F` are integrals of `f`, and `φ` is squeezed between its end values
  have hF : F y - F x = ∫ θ in x..y, f θ := by
    rw [← sub_sub_sub_cancel_right (F y) (F x) (F a), hFf y hy, hFf x hx,
      integral_interval_sub_left (hfi a ha y hy) (hfi a ha x hx)]
  have hlo : ∀ θ ∈ Icc x y, f θ * φ x ≤ φ θ * f θ := fun θ h => by
    rw [mul_comm]; exact mul_le_mul_of_nonneg_right (hφ hx (hθ θ h) h.1) (hf0 θ (hθ θ h))
  have hhi : ∀ θ ∈ Icc x y, φ θ * f θ ≤ f θ * φ y := fun θ h => by
    rw [mul_comm (f θ)]; exact mul_le_mul_of_nonneg_right (hφ (hθ θ h) hy h.2) (hf0 θ (hθ θ h))
  simp only
  rw [integral_interval_sub_left (hφi a ha y hy) (hφi a ha x hx), hF,
    ← intervalIntegral.integral_mul_const, ← intervalIntegral.integral_mul_const]
  exact ⟨integral_mono_on hxy ((hfi x hx y hy).mul_const _) (hφi x hx y hy) hlo,
    integral_mono_on hxy (hφi x hx y hy) ((hfi x hx y hy).mul_const _) hhi⟩

/-! ### The hull -/

/-- The data for the hull: `F` is a continuous, strictly increasing quantile on `[a, b]`, and
`G` is continuous with `F`-slopes bounded by `L`. -/
structure HullSetting (F G : ℝ → ℝ) (a b L : ℝ) : Prop where
  hab : a < b
  mono : StrictMonoOn F (Icc a b)
  cont : ContinuousOn F (Icc a b)
  contG : ContinuousOn G (Icc a b)
  lip : ∀ x ∈ Icc a b, ∀ y ∈ Icc a b, x ≤ y → |G y - G x| ≤ L * (F y - F x)

variable {G : ℝ → ℝ} {L : ℝ}

/-- The `F`-convex minorants of `G` on `[a, b]`. -/
def minorants (F G : ℝ → ℝ) (a b : ℝ) : Set (ℝ → ℝ) :=
  {K | FConvex F K a b ∧ ∀ x ∈ Icc a b, K x ≤ G x}

/-- **The ironed revenue curve**: the largest `F`-convex function below `G`. -/
noncomputable def hull (F G : ℝ → ℝ) (a b θ : ℝ) : ℝ := sSup ((fun K => K θ) '' minorants F G a b)

namespace HullSetting

variable (S : HullSetting F G a b L)
include S

lemma left_mem : a ∈ Icc a b := ⟨le_rfl, S.hab.le⟩
lemma right_mem : b ∈ Icc a b := ⟨S.hab.le, le_rfl⟩

lemma L_nonneg : 0 ≤ L := by
  have h := S.lip a S.left_mem b S.right_mem S.hab.le
  have : 0 < F b - F a := sub_pos.2 (S.mono S.left_mem S.right_mem S.hab)
  nlinarith [abs_nonneg (G b - G a)]

/-- The steepest descending `F`-line through `(a, G a)` lies below `G`. -/
lemma left_line_mem : (fun θ => G a - L * (F θ - F a)) ∈ minorants F G a b := by
  refine ⟨by convert fconvex_affine (F := F) (a := a) (b := b) (G a + L * F a) (-L) using 1
             ext θ; ring, fun x hx => ?_⟩
  have := S.lip a S.left_mem x hx hx.1
  linarith [neg_abs_le (G x - G a)]

/-- The steepest ascending `F`-line through `(b, G b)` lies below `G`. -/
lemma right_line_mem : (fun θ => G b + L * (F θ - F b)) ∈ minorants F G a b := by
  refine ⟨by convert fconvex_affine (F := F) (a := a) (b := b) (G b - L * F b) L using 1
             ext θ; ring, fun x hx => ?_⟩
  have := S.lip x hx b S.right_mem hx.2
  linarith [le_abs_self (G b - G x)]

lemma bddAbove {θ : ℝ} (hθ : θ ∈ Icc a b) :
    BddAbove ((fun K => K θ) '' minorants F G a b) :=
  ⟨G θ, by rintro _ ⟨K, hK, rfl⟩; exact hK.2 θ hθ⟩

lemma le_hull {K : ℝ → ℝ} (hK : K ∈ minorants F G a b) {θ : ℝ} (hθ : θ ∈ Icc a b) :
    K θ ≤ hull F G a b θ :=
  le_csSup (S.bddAbove hθ) ⟨K, hK, rfl⟩

lemma hull_le {θ : ℝ} (hθ : θ ∈ Icc a b) : hull F G a b θ ≤ G θ :=
  csSup_le ⟨_, _, S.left_line_mem, rfl⟩ (by rintro _ ⟨K, hK, rfl⟩; exact hK.2 θ hθ)

lemma hull_left : hull F G a b a = G a :=
  le_antisymm (S.hull_le S.left_mem) (by simpa using S.le_hull S.left_line_mem S.left_mem)

lemma hull_right : hull F G a b b = G b :=
  le_antisymm (S.hull_le S.right_mem) (by simpa using S.le_hull S.right_line_mem S.right_mem)

/-- The hull is `F`-convex: a supremum of `F`-convex functions. -/
lemma hull_fconvex : FConvex F (hull F G a b) a b := by
  intro x hx y hy z hxz hzy
  have hz : z ∈ Icc a b := ⟨hx.1.trans hxz.le, hzy.le.trans hy.2⟩
  have hC : 0 < F y - F x := sub_pos.2 (S.mono hx hy (hxz.trans hzy))
  have h₁ : 0 ≤ F y - F z := sub_nonneg.2 ((S.mono.le_iff_le hz hy).2 hzy.le)
  have h₂ : 0 ≤ F z - F x := sub_nonneg.2 ((S.mono.le_iff_le hx hz).2 hxz.le)
  rw [mul_comm, ← le_div_iff₀ hC]
  refine csSup_le ⟨_, _, S.left_line_mem, rfl⟩ ?_
  rintro _ ⟨K, hK, rfl⟩
  rw [le_div_iff₀ hC, mul_comm]
  exact (hK.1 x hx y hy z hxz hzy).trans (by
    gcongr
    exacts [S.le_hull hK hx, S.le_hull hK hy])

/-- `F`-slopes of the hull lie in `[-L, L]`: it is pinned between the two steepest lines. -/
lemma fslope_mem {x y : ℝ} (hx : x ∈ Icc a b) (hy : y ∈ Icc a b) (hxy : x < y) :
    -L ≤ fslope F (hull F G a b) x y ∧ fslope F (hull F G a b) x y ≤ L := by
  have hK := S.hull_fconvex
  have pos : ∀ {u v}, u ∈ Icc a b → v ∈ Icc a b → u < v → 0 < F v - F u :=
    fun hu hv h => sub_pos.2 (S.mono hu hv h)
  -- the slope from `a` is at least `-L`, the slope to `b` at most `L`
  have from_a : ∀ {v}, v ∈ Icc a b → a < v → -L ≤ fslope F (hull F G a b) a v := fun hv h => by
    have := S.le_hull S.left_line_mem hv
    rw [fslope, le_div_iff₀ (pos S.left_mem hv h), S.hull_left]; linarith
  have to_b : ∀ {u}, u ∈ Icc a b → u < b → fslope F (hull F G a b) u b ≤ L := fun hu h => by
    have := S.le_hull S.right_line_mem hu
    rw [fslope, div_le_iff₀ (pos hu S.right_mem h), S.hull_right]; linarith
  constructor
  · rcases hx.1.eq_or_lt with rfl | hax
    · exact from_a hy hxy
    · exact (from_a hx hax).trans ((hK.fslope_le S.mono S.left_mem hy hax hxy).1.trans
        (hK.fslope_le S.mono S.left_mem hy hax hxy).2)
  · rcases hy.2.eq_or_lt with rfl | hyb
    · exact to_b hx hxy
    · exact ((hK.fslope_le S.mono hx S.right_mem hxy hyb).1.trans
        (hK.fslope_le S.mono hx S.right_mem hxy hyb).2).trans (to_b hy hyb)

end HullSetting

/-- **The ironed virtual value**: the right `F`-slope of the hull (types below `a` read as
`a`; from `b` on, the slope bound `L`). -/
noncomputable def ironedValue (F G : ℝ → ℝ) (a b L θ : ℝ) : ℝ :=
  if θ < b then sInf (fslope F (hull F G a b) (max a θ) '' Ioc (max a θ) b) else L

namespace HullSetting

variable (S : HullSetting F G a b L)
include S

lemma ironedValue_of_mem {θ : ℝ} (hθ : θ ∈ Ico a b) :
    ironedValue F G a b L θ = sInf (fslope F (hull F G a b) θ '' Ioc θ b) := by
  simp [ironedValue, hθ.2, max_eq_right hθ.1]

lemma bddBelow_fslope {θ : ℝ} (hθ : θ ∈ Ico a b) :
    BddBelow (fslope F (hull F G a b) θ '' Ioc θ b) :=
  ⟨-L, by rintro _ ⟨y, hy, rfl⟩; exact (S.fslope_mem (Ico_subset_Icc_self hθ)
    ⟨hθ.1.trans hy.1.le, hy.2⟩ hy.1).1⟩

/-- The ironed value is below every slope to the right. -/
lemma ironedValue_le_fslope {x y : ℝ} (hx : x ∈ Icc a b) (hy : y ∈ Icc a b) (hxy : x < y) :
    ironedValue F G a b L x ≤ fslope F (hull F G a b) x y := by
  have hx' : x ∈ Ico a b := ⟨hx.1, hxy.trans_le hy.2⟩
  rw [S.ironedValue_of_mem hx']
  exact csInf_le (S.bddBelow_fslope hx') ⟨y, ⟨hxy, hy.2⟩, rfl⟩

/-- The ironed value is above every slope to the left. -/
lemma fslope_le_ironedValue {x y : ℝ} (hx : x ∈ Icc a b) (hy : y ∈ Icc a b) (hxy : x < y) :
    fslope F (hull F G a b) x y ≤ ironedValue F G a b L y := by
  rcases hy.2.eq_or_lt with rfl | hyb
  · simpa [ironedValue] using (S.fslope_mem hx hy hxy).2
  rw [S.ironedValue_of_mem ⟨hy.1, hyb⟩]
  refine le_csInf ⟨_, b, ⟨hyb, le_rfl⟩, rfl⟩ ?_
  rintro _ ⟨z, hz, rfl⟩
  have h := S.hull_fconvex.fslope_le S.mono hx ⟨hy.1.trans hz.1.le, hz.2⟩ hxy hz.1
  exact h.1.trans h.2

lemma ironedValue_mem (θ : ℝ) : ironedValue F G a b L θ ∈ Icc (-L) L := by
  by_cases hθ : θ < b
  · have hθ' : max a θ ∈ Ico a b := ⟨le_max_left _ _, max_lt S.hab hθ⟩
    have hm : max a θ ∈ Icc a b := Ico_subset_Icc_self hθ'
    have hb := S.fslope_mem hm S.right_mem hθ'.2
    have h1 := S.ironedValue_le_fslope hm S.right_mem hθ'.2
    have h2 : -L ≤ ironedValue F G a b L (max a θ) := by
      rw [S.ironedValue_of_mem hθ']
      exact le_csInf ⟨_, b, ⟨hθ'.2, le_rfl⟩, rfl⟩ (by
        rintro _ ⟨y, hy, rfl⟩
        exact (S.fslope_mem hm ⟨hθ'.1.trans hy.1.le, hy.2⟩ hy.1).1)
    have e : ironedValue F G a b L θ = ironedValue F G a b L (max a θ) := by
      simp [ironedValue, hθ, hθ'.2]
    rw [e]; exact ⟨h2, h1.trans hb.2⟩
  · simp [ironedValue, hθ, neg_le_self S.L_nonneg]

/-- The ironed value `F`-supports the hull. -/
lemma fsupports : Myerson.FSupports F (ironedValue F G a b L) (hull F G a b) (Icc a b) := by
  intro x hx y hy hxy
  rcases hxy.eq_or_lt with rfl | hxy
  · simp
  have hpos : 0 < F y - F x := sub_pos.2 (S.mono hx hy hxy)
  have h₁ := S.ironedValue_le_fslope hx hy hxy
  have h₂ := S.fslope_le_ironedValue hx hy hxy
  rw [fslope, le_div_iff₀ hpos] at h₁
  rw [fslope, div_le_iff₀ hpos] at h₂
  constructor <;> linarith

/-- **The ironed value is monotone.** -/
lemma ironedValue_monotone : Monotone (ironedValue F G a b L) := by
  intro x y hxy
  by_cases hy : y < b
  · -- below `b`, compare through the slope between the clamped points
    have e : ∀ θ, θ < b → ironedValue F G a b L θ = ironedValue F G a b L (max a θ) :=
      fun θ hθ => by simp [ironedValue, hθ, max_lt S.hab hθ]
    rw [e x (hxy.trans_lt hy), e y hy]
    have hx' : max a x ∈ Icc a b := ⟨le_max_left _ _, (max_lt S.hab (hxy.trans_lt hy)).le⟩
    have hy' : max a y ∈ Icc a b := ⟨le_max_left _ _, (max_lt S.hab hy).le⟩
    rcases (max_le_max le_rfl hxy : max a x ≤ max a y).eq_or_lt with h | h
    · rw [h]
    · exact (S.ironedValue_le_fslope hx' hy' h).trans (S.fslope_le_ironedValue hx' hy' h)
  · simpa [ironedValue, hy] using (S.ironedValue_mem x).2

lemma ironedValue_bddMeas : Auction.BddMeas (ironedValue F G a b L) :=
  ⟨S.ironedValue_monotone.measurable, L, fun θ => abs_le.2 (S.ironedValue_mem θ)⟩

/-- The hull is `L`-Lipschitz in the quantile. -/
lemma hull_lip {x y : ℝ} (hx : x ∈ Icc a b) (hy : y ∈ Icc a b) (hxy : x ≤ y) :
    |hull F G a b y - hull F G a b x| ≤ L * (F y - F x) := by
  rcases hxy.eq_or_lt with rfl | hxy
  · simp
  have hpos : 0 < F y - F x := sub_pos.2 (S.mono hx hy hxy)
  obtain ⟨h₁, h₂⟩ := S.fslope_mem hx hy hxy
  rw [fslope, le_div_iff₀ hpos] at h₁
  rw [fslope, div_le_iff₀ hpos] at h₂
  rw [abs_le]; constructor <;> linarith

/-- **Maximality**: if the chord over `[x₀, y₀]` stays below `G` there, the hull *is* that
chord on `[x₀, y₀]` (raising the hull to the chord would give a larger minorant). -/
lemma hull_eq_chord {x₀ y₀ : ℝ} (hx₀ : x₀ ∈ Icc a b) (hy₀ : y₀ ∈ Icc a b) (hxy : x₀ < y₀)
    (hc : ∀ θ ∈ Ioo x₀ y₀, chord F (hull F G a b) x₀ y₀ θ ≤ G θ) :
    ∀ θ ∈ Icc x₀ y₀, hull F G a b θ = chord F (hull F G a b) x₀ y₀ θ := by
  set H := hull F G a b
  have hK : (fun θ => max (H θ) (chord F H x₀ y₀ θ)) ∈ minorants F G a b := by
    refine ⟨S.hull_fconvex.max (by
      convert fconvex_affine (F := F) (a := a) (b := b) (H x₀ - fslope F H x₀ y₀ * F x₀)
        (fslope F H x₀ y₀) using 1
      ext θ; simp only [chord]; ring) S.mono, fun θ hθ => max_le (S.hull_le hθ) ?_⟩
    by_cases hin : θ ∈ Ioo x₀ y₀
    · exact hc θ hin
    · exact (S.hull_fconvex.chord_le S.mono hx₀ hy₀ hθ hxy hin).trans (S.hull_le hθ)
  exact fun θ hθ => le_antisymm (S.hull_fconvex.le_chord S.mono hx₀ hy₀ hθ hxy)
    ((le_max_right _ _).trans (S.le_hull hK ⟨hx₀.1.trans hθ.1, hθ.2.trans hy₀.2⟩))

/-- Where the hull is a chord, the ironed value is the chord's slope. -/
lemma ironedValue_eq_fslope {x₀ y₀ : ℝ} (hx₀ : x₀ ∈ Icc a b) (hy₀ : y₀ ∈ Icc a b)
    (hH : ∀ θ ∈ Icc x₀ y₀, hull F G a b θ = chord F (hull F G a b) x₀ y₀ θ)
    {θ : ℝ} (hθ : θ ∈ Ico x₀ y₀) :
    ironedValue F G a b L θ = fslope F (hull F G a b) x₀ y₀ := by
  set H := hull F G a b
  have hθI : θ ∈ Icc a b := ⟨hx₀.1.trans hθ.1, hθ.2.le.trans hy₀.2⟩
  have hθ' : θ ∈ Ico a b := ⟨hθI.1, hθ.2.trans_le hy₀.2⟩
  -- slopes from `θ` within the chord are the chord's slope, beyond it they are larger
  have hin : ∀ z ∈ Icc a b, θ < z → z ≤ y₀ → fslope F H θ z = fslope F H x₀ y₀ :=
    fun z hz hθz hzy => by
      rw [show fslope F H θ z = fslope F (chord F H x₀ y₀) θ z by
        unfold fslope; rw [hH θ (Ico_subset_Icc_self hθ), hH z ⟨hθ.1.trans hθz.le, hzy⟩],
        fslope_chord (S.mono hθI hz hθz).ne]
  rw [S.ironedValue_of_mem hθ']
  refine le_antisymm ((csInf_le (S.bddBelow_fslope hθ') ⟨y₀, ⟨hθ.2, hy₀.2⟩, rfl⟩).trans
    (hin y₀ hy₀ hθ.2 le_rfl).le) (le_csInf ⟨_, y₀, ⟨hθ.2, hy₀.2⟩, rfl⟩ ?_)
  rintro _ ⟨z, hz, rfl⟩
  have hzI : z ∈ Icc a b := ⟨hθI.1.trans hz.1.le, hz.2⟩
  rcases le_or_gt z y₀ with hzy | hzy
  · exact (hin z hzI hz.1 hzy).ge
  · exact (hin y₀ hy₀ hθ.2 le_rfl).symm.le.trans
      (S.hull_fconvex.fslope_le S.mono hθI hzI hθ.2 hzy).1

/-- **The ironed value is flat where the gap is open.** Near a point where the hull is strictly
below `G`, a short chord still lies below `G`, so the hull is that chord and its slope is
constant. -/
lemma flat {p : ℝ} (hp : p ∈ Ioo a b) (hgap : hull F G a b p < G p) :
    ∃ ε > 0, ∀ x ∈ Ioo (p - ε) (p + ε), ironedValue F G a b L x = ironedValue F G a b L p := by
  set H := hull F G a b
  set δ := G p - H p
  have hδ : 0 < δ := sub_pos.2 hgap
  have hL := S.L_nonneg
  set κ := δ / (8 * (L + 1))
  have hLκ : L * κ ≤ δ / 8 := by
    rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  -- near `p`, `G` and `F` barely move
  have hpN : Icc a b ∈ nhds p := Icc_mem_nhds hp.1 hp.2
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1
    ((Metric.tendsto_nhds.1 (S.contG.continuousAt hpN) (δ / 4) (by positivity)).and
      ((Metric.tendsto_nhds.1 (S.cont.continuousAt hpN) κ (by positivity)).and
        (Ioo_mem_nhds hp.1 hp.2)))
  set x₀ := p - ε / 2 with hx₀d
  set y₀ := p + ε / 2 with hy₀d
  have near : ∀ θ ∈ Icc x₀ y₀, |G θ - G p| < δ / 4 ∧ |F θ - F p| < κ ∧ θ ∈ Ioo a b :=
    fun θ hθ => by
      have h := hball (y := θ) (by
        rw [Real.dist_eq, abs_lt]; constructor <;> linarith [hθ.1, hθ.2, hx₀d, hy₀d])
      simpa [Real.dist_eq] using h
  have hx₀ : x₀ ∈ Icc a b := Ioo_subset_Icc_self (near x₀ ⟨le_rfl, by linarith⟩).2.2
  have hy₀ : y₀ ∈ Icc a b := Ioo_subset_Icc_self (near y₀ ⟨by linarith, le_rfl⟩).2.2
  have hxy : x₀ < y₀ := by linarith
  -- the short chord lies below `G`: it rises at most `L` times a small quantile change
  have hc : ∀ θ ∈ Ioo x₀ y₀, chord F H x₀ y₀ θ ≤ G θ := fun θ hθ => by
    obtain ⟨hGθ, hFθ, hθI⟩ := near θ (Ioo_subset_Icc_self hθ)
    obtain ⟨-, hFx₀, -⟩ := near x₀ ⟨le_rfl, hxy.le⟩
    have hmono : F x₀ ≤ F θ := (S.mono.le_iff_le hx₀ (Ioo_subset_Icc_self hθI)).2 hθ.1.le
    have hlip := S.hull_lip hx₀ (Ioo_subset_Icc_self hp) (by linarith)
    have : fslope F H x₀ y₀ * (F θ - F x₀) ≤ L * (F θ - F x₀) :=
      mul_le_mul_of_nonneg_right (S.fslope_mem hx₀ hy₀ hxy).2 (by linarith)
    rw [abs_lt] at hGθ hFθ hFx₀; rw [abs_le] at hlip
    simp only [chord]
    nlinarith
  refine ⟨ε / 2, by positivity, fun x hx => ?_⟩
  have hH := S.hull_eq_chord hx₀ hy₀ hxy hc
  rw [S.ironedValue_eq_fslope hx₀ hy₀ hH ⟨hx.1.le, hx.2⟩,
    S.ironedValue_eq_fslope hx₀ hy₀ hH ⟨by linarith, by linarith⟩]

/-- **The hull is the integral of the ironed value**, when `F` is the primitive of a
nonnegative density `f`: both sides are `F`-supported by the ironed value. -/
lemma hull_sub_eq_integral {f : ℝ → ℝ} (hf : ContinuousOn f (Icc a b))
    (hf0 : ∀ θ ∈ Icc a b, 0 ≤ f θ) (hFf : ∀ x ∈ Icc a b, F x - F a = ∫ θ in a..x, f θ)
    {p : ℝ} (hp : p ∈ Icc a b) :
    hull F G a b p - hull F G a b a = ∫ θ in a..p, ironedValue F G a b L θ * f θ := by
  have hsub : Icc a p ⊆ Icc a b := Icc_subset_Icc_right hp.2
  have hW := fsupports_integral S.hab.le (S.ironedValue_monotone.monotoneOn _)
    ((S.ironedValue_bddMeas.intervalIntegrable a b).mul_continuousOn
      (by rwa [uIcc_of_le S.hab.le])) hf hf0 hFf
  have := Myerson.FSupports.sub_eq (S.mono.mono hsub) (S.cont.mono hsub)
    (fun x hx y hy => S.fsupports x (hsub hx) y (hsub hy))
    (fun x hx y hy => hW x (hsub hx) y (hsub hy)) hp.1
  simpa using this

end HullSetting

end Ironing

/-! ### Every density admits an ironing -/

namespace Ironing

open Myerson

variable {a b : ℝ} {f : ℝ → ℝ}

/-- The cumulative virtual surplus `G(p) = ∫ₐᵖ J`. -/
noncomputable def cumJ (f : ℝ → ℝ) (a p : ℝ) : ℝ := ∫ θ in a..p, J f a θ

/-- A pointwise bound `|g| ≤ L h` integrates. -/
lemma abs_integral_le_mul {g h : ℝ → ℝ} {L x y : ℝ} (hxy : x ≤ y)
    (hg : IntervalIntegrable g volume x y) (hh : IntervalIntegrable h volume x y)
    (hb : ∀ θ ∈ Icc x y, |g θ| ≤ L * h θ) : |∫ θ in x..y, g θ| ≤ L * ∫ θ in x..y, h θ := by
  rw [abs_le, ← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_neg]
  exact ⟨integral_mono_on hxy (hh.const_mul L).neg hg fun θ hθ => by
      linarith [neg_abs_le (g θ), hb θ hθ],
    integral_mono_on hxy hg (hh.const_mul L) fun θ hθ => (le_abs_self _).trans (hb θ hθ)⟩

/-- With a continuous positive density, the quantile `F` and the cumulative virtual surplus `G`
satisfy the hull's hypotheses, with `L` a bound on the virtual value. -/
lemma hullSetting (hab : a < b) (hf : ContinuousOn f (Icc a b))
    (hpos : ∀ θ ∈ Icc a b, 0 < f θ) :
    ∃ L, HullSetting (cdf f a) (cumJ f a) a b L := by
  have hJ : ContinuousOn (J f a) (Icc a b) := by
    simpa [uIcc_of_le hab.le] using J_continuousOn hab.le hf
  obtain ⟨L, hL⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (hJ.div hf fun θ hθ => (hpos θ hθ).ne')
  have hfi : ∀ x ∈ Icc a b, ∀ y ∈ Icc a b, IntervalIntegrable f volume x y :=
    fun x hx y hy => (hf.mono (uIcc_subset_Icc hx hy)).intervalIntegrable
  have hJi : ∀ x ∈ Icc a b, ∀ y ∈ Icc a b, IntervalIntegrable (J f a) volume x y :=
    fun x hx y hy => (hJ.mono (uIcc_subset_Icc hx hy)).intervalIntegrable
  have ha : a ∈ Icc a b := ⟨le_rfl, hab.le⟩
  -- increments are integrals over the subinterval
  have incr : ∀ {g : ℝ → ℝ}, (∀ x ∈ Icc a b, ∀ y ∈ Icc a b, IntervalIntegrable g volume x y) →
      ∀ x ∈ Icc a b, ∀ y ∈ Icc a b,
        (∫ θ in a..y, g θ) - (∫ θ in a..x, g θ) = ∫ θ in x..y, g θ :=
    fun hg x hx y hy => integral_interval_sub_left (hg a ha y hy) (hg a ha x hx)
  refine ⟨L, ⟨hab, fun x hx y hy hxy => ?_, ?_, ?_, fun x hx y hy hxy => ?_⟩⟩
  · -- the quantile is strictly increasing
    have := incr hfi x hx y hy
    have hpos' := intervalIntegral.intervalIntegral_pos_of_pos_on (hfi x hx y hy)
      (fun θ hθ => hpos θ ⟨hx.1.trans hθ.1.le, hθ.2.le.trans hy.2⟩) hxy
    simp only [cdf] at *; linarith
  · have := continuousOn_primitive_interval' (hfi a ha b ⟨hab.le, le_rfl⟩) (left_mem_uIcc (b := b))
    rw [uIcc_of_le hab.le] at this; exact this
  · have := continuousOn_primitive_interval' (hJi a ha b ⟨hab.le, le_rfl⟩) (left_mem_uIcc (b := b))
    rw [uIcc_of_le hab.le] at this; exact this
  · -- `G`'s increments are bounded by `L` times `F`'s, since `|J| ≤ L f`
    simp only [cdf, cumJ]
    rw [incr hJi x hx y hy, incr hfi x hx y hy]
    refine abs_integral_le_mul hxy (hJi x hx y hy) (hfi x hx y hy) fun θ hθ => ?_
    have hθ' : θ ∈ Icc a b := ⟨hx.1.trans hθ.1, hθ.2.trans hy.2⟩
    have := hL θ hθ'
    rwa [Pi.div_apply, Real.norm_eq_abs, abs_div, abs_of_pos (hpos θ hθ'),
      div_le_iff₀ (hpos θ hθ')] at this

/-- **The hull's slope irons the virtual value** (Myerson 1981, §6): the right quantile-slope
of the convex hull of the cumulative virtual surplus is an ironing. -/
theorem ironedValue_ironed (hab : a < b) (hf : ContinuousOn f (Icc a b))
    (hpos : ∀ θ ∈ Icc a b, 0 < f θ) :
    ∃ L, Ironed f a b (ironedValue (cdf f a) (cumJ f a) a b L) := by
  obtain ⟨L, S⟩ := hullSetting hab hf hpos
  refine ⟨L, ?_⟩
  set φ := ironedValue (cdf f a) (cumJ f a) a b L
  have hFf : ∀ x ∈ Icc a b, cdf f a x - cdf f a a = ∫ θ in a..x, f θ := fun x _ => by
    simp [cdf]
  -- the gap is the distance from the hull to the cumulative virtual surplus
  have hgap : ∀ p ∈ Icc a b, gap f a φ p = cumJ f a p - hull (cdf f a) (cumJ f a) a b p :=
    fun p hp => by
      have hsub : uIcc a p ⊆ Icc a b := by rw [uIcc_of_le hp.1]; exact Icc_subset_Icc_right hp.2
      have hJ : IntervalIntegrable (J f a) volume a p :=
        ((J_continuousOn hab.le hf).mono (hsub.trans (uIcc_of_le hab.le).ge)).intervalIntegrable
      have hφf : IntervalIntegrable (fun θ => φ θ * f θ) volume a p :=
        (S.ironedValue_bddMeas.intervalIntegrable a p).mul_continuousOn (hf.mono hsub)
      have h := S.hull_sub_eq_integral hf (fun θ hθ => (hpos θ hθ).le) hFf hp
      rw [S.hull_left] at h
      simp only [gap, intervalIntegral.integral_sub hJ hφf, cumJ, integral_same] at h ⊢
      linarith
  exact ⟨S.ironedValue_monotone, S.ironedValue_bddMeas,
    fun p hp => by rw [hgap p hp]; exact sub_nonneg.2 (S.hull_le hp),
    by rw [hgap b S.right_mem, S.hull_right, sub_self],
    fun p hp hpos' => S.flat hp (by rw [hgap p (Ioo_subset_Icc_self hp)] at hpos'; linarith)⟩

/-- **Every continuous positive density admits an ironing.** (On a degenerate interval any
constant irons trivially.) -/
theorem exists_ironed (hab : a ≤ b) (hf : ContinuousOn f (Icc a b))
    (hpos : ∀ θ ∈ Icc a b, 0 < f θ) : ∃ φ, Ironed f a b φ := by
  rcases hab.eq_or_lt with rfl | hab
  · refine ⟨fun _ => 0, monotone_const, ⟨measurable_const, 0, by simp⟩, fun p hp => ?_,
      by simp [gap], fun p hp => absurd hp (by simp)⟩
    simp [gap, le_antisymm hp.2 hp.1]
  · obtain ⟨L, h⟩ := ironedValue_ironed hab hf hpos
    exact ⟨_, h⟩

end Ironing

/-! ### Myerson's optimal auction, unconditionally -/

namespace Auction

open Ironing

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] {ν : ι → Measure ℝ}
  [∀ i, IsProbabilityMeasure (ν i)] {a b : ℝ} {f : ι → ℝ → ℝ}

/-- **Myerson's optimal auction** (1981), for every prior with continuous positive densities and
no regularity assumption: iron each bidder's virtual value; the ironed auction is bounded
measurable, feasible, BIC and interim IR, and earns at least as much as any other such
auction. -/
theorem exists_optimal_auction (P : Prior ν f a b) :
    ∃ φ : ι → ℝ → ℝ, (∀ i, Ironed (f i) a b (φ i)) ∧
      (ironedAuction a b φ).BddMeasurable ∧ (ironedAuction a b φ).Feasible ∧
      (ironedAuction a b φ).BIC ν a b ∧ (∀ i, ((ironedAuction a b φ).interim ν i).IR a b) ∧
      ∀ M : Mechanism ι, M.BddMeasurable → M.Feasible → M.BIC ν a b →
        (∀ i, (M.interim ν i).IR a b) → M.revenue ν ≤ (ironedAuction a b φ).revenue ν := by
  choose φ hφ using fun i => exists_ironed P.hab (P.cont i).continuousOn (P.pos i)
  exact ⟨φ, hφ, ironed_optimal P hφ⟩

end Auction
