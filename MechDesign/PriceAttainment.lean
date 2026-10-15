/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import MechDesign.MeanDuality
import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
import Mathlib.Topology.MetricSpace.UniformConvergence
import Mathlib.Topology.Order.ProjIcc

/-!
# The best price exists when the payoff is Lipschitz

For an `L`-Lipschitz payoff `V`, the dual infimum `priceValue V μ` is attained by a price
(`exists_optimal_price`). (With prices convex on all of `ℝ`, attainment can fail for
non-Lipschitz `V`, e.g. `V m = -√m`.)

**Proof.** Replace any price `p` by `lipPrice`, the supremum over `y ∈ [0, 1]` of the lines
through `(y, V y)` with the slope of `p` at `y` clamped to `[-L, L]`. It is again a price, lies
below `p` on `[0, 1]`, and is `L`-Lipschitz with values in `[-B, B + L]`. By Arzelà–Ascoli a
minimising sequence of such prices has a uniformly convergent subsequence. Its limit `g`
keeps, at every point, a line of slope in `[-L, L]` through `V` below it (`Supported`), and the
supremum of all lines of slope in `[-L, L]` below `g` is a price costing at most `∫ g dμ`.
-/

open MeasureTheory Set unitInterval BoundedContinuousFunction Filter Topology

namespace MeanPersuasion

variable {μ : Measure ℝ} {V p : ℝ → ℝ} {L : ℝ}

/-! ### Clamped slopes and Lipschitz prices -/

/-- The slope of `p` at `y`, clamped to `[-L, L]`. -/
noncomputable def clampSlope (L : ℝ) (p : ℝ → ℝ) (y : ℝ) : ℝ := max (-L) (min (subgrad p y) L)

lemma abs_clampSlope_le (hL : 0 ≤ L) (y : ℝ) : |clampSlope L p y| ≤ L :=
  abs_le.2 ⟨le_max_left _ _, max_le (by linarith) (min_le_right _ _)⟩

/-- Where clamping changes the slope `s` to `c`, the line with slope `c` falls at rate `L`. -/
lemma clamp_mul_le (hL : 0 ≤ L) (s d : ℝ) (h : d * (s - max (-L) (min s L)) < 0) :
    max (-L) (min s L) * d ≤ -L * |d| := by
  rcases le_or_gt s L with h1 | h1 <;> rcases le_or_gt (-L) s with h2 | h2
  · rw [min_eq_left h1, max_eq_right h2] at h; simp at h
  · rw [min_eq_left h1, max_eq_left h2.le] at h ⊢
    rw [abs_of_pos (by nlinarith)]
  · rw [min_eq_right h1.le, max_eq_right (by linarith)] at h ⊢
    rw [abs_of_neg (by nlinarith)]; linarith
  · linarith

/-- **A clamped line through `V` stays below the price**, by convexity of `p` on one side and
the Lipschitz bound on `V` on the other. -/
lemma line_le_price (hL : 0 ≤ L) (hLip : ∀ x ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (0 : ℝ) 1,
    V y ≤ V x + L * |x - y|) (hp : IsPrice V p) {x y : ℝ} (hx : x ∈ Icc (0 : ℝ) 1)
    (hy : y ∈ Icc (0 : ℝ) 1) : V y + clampSlope L p y * (x - y) ≤ p x := by
  have hsup := le_support hp.convex y x
  have hVy := hp.le y hy
  by_cases h : (x - y) * (subgrad p y - clampSlope L p y) < 0
  · have := clamp_mul_le hL _ _ h
    rw [clampSlope]; linarith [hLip x hx y hy, hp.le x hx]
  · push Not at h; rw [clampSlope] at h ⊢; nlinarith

/-- **The Lipschitz price** built from `p`: the supremum over `y ∈ [0, 1]` of the lines through
`(y, V y)` with the clamped slope of `p` at `y`. -/
noncomputable def lipPrice (L : ℝ) (V p : ℝ → ℝ) (x : ℝ) : ℝ :=
  ⨆ y : I, (V y + clampSlope L p y * (x - y))

section lipPrice

variable {B : ℝ} (hB : ∀ x ∈ Icc (0 : ℝ) 1, |V x| ≤ B) (hL : 0 ≤ L)
include hB hL

lemma lipPrice_bdd (x : ℝ) : BddAbove (range fun y : I => V y + clampSlope L p y * (x - y)) :=
  ⟨B + L * (|x| + 1), by
    rintro _ ⟨y, rfl⟩
    have h1 := (le_abs_self _).trans (hB y y.2)
    have h2 : |clampSlope L p y * (x - y)| ≤ L * (|x| + 1) := by
      rw [abs_mul]; exact mul_le_mul (abs_clampSlope_le hL y)
        ((abs_sub _ _).trans (by linarith [abs_le_one_of_mem y])) (abs_nonneg _) hL
    linarith [le_abs_self (clampSlope L p y * (x - y))]⟩

lemma line_le_lipPrice (y : I) (x : ℝ) :
    V y + clampSlope L p y * (x - y) ≤ lipPrice L V p x :=
  le_ciSup (lipPrice_bdd hB hL x) y

lemma convexOn_lipPrice : ConvexOn ℝ univ (lipPrice L V p) :=
  ⟨convex_univ, fun x _ y _ s t hs ht hst => ciSup_le fun m => by
    have hx := line_le_lipPrice (p := p) hB hL m x
    have hy := line_le_lipPrice (p := p) hB hL m y
    simp only [smul_eq_mul]
    calc V m + clampSlope L p m * (s * x + t * y - m)
        = s * (V m + clampSlope L p m * (x - m)) + t * (V m + clampSlope L p m * (y - m)) := by
          linear_combination (-(V m) + clampSlope L p m * m) * hst
      _ ≤ _ := by gcongr⟩

lemma lipPrice_lip (x x' : ℝ) : lipPrice L V p x ≤ lipPrice L V p x' + L * |x - x'| :=
  ciSup_le fun y => by
    have h1 := line_le_lipPrice (p := p) hB hL y x'
    have h2 : clampSlope L p y * (x - x') ≤ L * |x - x'| := by
      have := mul_le_mul_of_nonneg_right (abs_clampSlope_le (p := p) hL y) (abs_nonneg (x - x'))
      rw [← abs_mul] at this; exact (le_abs_self _).trans this
    linarith [show clampSlope L p y * (x - y) = clampSlope L p y * (x' - y)
      + clampSlope L p y * (x - x') by ring]

lemma lipPrice_mem {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) : lipPrice L V p x ∈ Icc (-B) (B + L) :=
  ⟨by linarith [line_le_lipPrice (p := p) hB hL ⟨x, hx⟩ x, neg_abs_le (V x), hB x hx],
    ciSup_le fun y => by
      have h := mul_le_mul (abs_clampSlope_le (p := p) hL y) (show |x - y| ≤ 1 by
        rw [abs_le]; constructor <;> linarith [hx.1, hx.2, y.2.1, y.2.2]) (abs_nonneg _) hL
      rw [← abs_mul] at h
      linarith [le_abs_self (clampSlope L p y * (x - y)), (le_abs_self _).trans (hB y y.2)]⟩

/-- `lipPrice` is a price, below `p` on `[0, 1]`. -/
lemma lipPrice_spec (hLip : ∀ x ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (0 : ℝ) 1,
    V y ≤ V x + L * |x - y|) (hp : IsPrice V p) :
    IsPrice V (lipPrice L V p) ∧ ∀ x ∈ Icc (0 : ℝ) 1, lipPrice L V p x ≤ p x :=
  ⟨⟨convexOn_lipPrice hB hL, fun x hx => by
      simpa using line_le_lipPrice (p := p) hB hL ⟨x, hx⟩ x⟩,
    fun x hx => ciSup_le fun y => line_le_price hL hLip hp hx y.2⟩

end lipPrice

/-! ### A price from its restriction to `[0, 1]` -/

/-- `g` is **supported** below `V` with slopes in `[-L, L]`: at every `x ∈ [0, 1]`, some line
through `(x, V x)` with slope in `[-L, L]` stays below `g`. -/
def Supported (V : ℝ → ℝ) (L : ℝ) (g : I →ᵇ ℝ) : Prop :=
  ∀ x : I, ∃ b ∈ Icc (-L) L, ∀ y : I, V x + b * (y - x) ≤ g y

/-- The supremum of the lines with slope in `[-L, L]` below `g` on `[0, 1]`. -/
noncomputable def lowerHull (L : ℝ) (g : I →ᵇ ℝ) (x : ℝ) : ℝ :=
  ⨆ b : Icc (-L) L, ((b : ℝ) * x + ⨅ y : I, (g y - b * y))

lemma abs_apply_le_norm (g : I →ᵇ ℝ) (x : I) : |g x| ≤ ‖g‖ :=
  (Real.norm_eq_abs _).symm.trans_le (g.norm_coe_le_norm x)

section lowerHull

variable (hL : 0 ≤ L) (g : I →ᵇ ℝ)
include hL

lemma lowerHull_inner_bdd (b : Icc (-L) L) : BddBelow (range fun y : I => g y - b * y) :=
  ⟨-‖g‖ - L, by
    rintro _ ⟨y, rfl⟩
    have := mul_le_mul (abs_le.2 ⟨b.2.1, b.2.2⟩) (abs_le_one_of_mem y) (abs_nonneg _) hL
    rw [← abs_mul] at this
    linarith [neg_abs_le (g y), le_abs_self ((b : ℝ) * y), abs_apply_le_norm g y]⟩

lemma lowerHull_bdd (x : ℝ) :
    BddAbove (range fun b : Icc (-L) L => (b : ℝ) * x + ⨅ y : I, (g y - b * y)) :=
  ⟨L * |x| + ‖g‖, by
    rintro _ ⟨b, rfl⟩
    have h1 := ciInf_le (lowerHull_inner_bdd hL g b) 0
    have h2 := mul_le_mul_of_nonneg_right (abs_le.2 ⟨b.2.1, b.2.2⟩) (abs_nonneg x)
    rw [← abs_mul] at h2
    simp only [Icc.coe_zero, mul_zero, sub_zero] at h1
    linarith [le_abs_self ((b : ℝ) * x), le_abs_self (g 0), abs_apply_le_norm g 0]⟩

lemma convexOn_lowerHull : ConvexOn ℝ univ (lowerHull L g) :=
  have : Nonempty (Icc (-L) L) := ⟨⟨0, by linarith, hL⟩⟩
  ⟨convex_univ, fun x _ y _ s t hs ht hst => ciSup_le fun b => by
    have hx := le_ciSup (lowerHull_bdd hL g x) b
    have hy := le_ciSup (lowerHull_bdd hL g y) b
    simp only [smul_eq_mul, lowerHull] at hx hy ⊢
    calc (b : ℝ) * (s * x + t * y) + ⨅ y : I, (g y - b * y)
        = s * (b * x + ⨅ y : I, (g y - b * y)) + t * (b * y + ⨅ y : I, (g y - b * y)) := by
          linear_combination (-⨅ y : I, (g y - b * y)) * hst
      _ ≤ _ := by gcongr⟩

lemma lowerHull_le (x : I) : lowerHull L g x ≤ g x :=
  have : Nonempty (Icc (-L) L) := ⟨⟨0, by linarith, hL⟩⟩
  ciSup_le fun b => by linarith [ciInf_le (lowerHull_inner_bdd hL g b) x]

/-- **A supported `g` yields a price below it.** -/
lemma isPrice_lowerHull {g : I →ᵇ ℝ} (hg : Supported V L g) : IsPrice V (lowerHull L g) :=
  ⟨convexOn_lowerHull hL g, fun x hx => by
    obtain ⟨b, hb, hline⟩ := hg ⟨x, hx⟩
    refine le_ciSup_of_le (lowerHull_bdd hL g x) ⟨b, hb⟩ ?_
    have := le_ciInf fun y : I => show V x - b * x ≤ g y - b * y by linarith [hline y]
    simp only at this ⊢; linarith⟩

end lowerHull

/-! ### Compactness -/

/-- A continuous function on `ℝ`, restricted to `[0, 1]` as a bounded continuous function. -/
noncomputable def toB (f : ℝ → ℝ) (hf : Continuous f) : I →ᵇ ℝ := mkOfCompact (onI f hf)

@[simp] lemma toB_apply (f : ℝ → ℝ) (hf : Continuous f) (x : I) : toB f hf x = f x := rfl

/-- The cost of `g` under `μ`, reading `g` on `[0, 1]`. -/
noncomputable def cost (μ : Measure ℝ) (g : I →ᵇ ℝ) : ℝ :=
  ∫ θ, g (projIcc 0 1 zero_le_one θ) ∂μ

section cost

variable [IsProbabilityMeasure μ]

lemma integrable_cost (g : I →ᵇ ℝ) : Integrable (fun θ => g (projIcc 0 1 zero_le_one θ)) μ :=
  (integrable_const ‖g‖).mono' (g.continuous.comp continuous_projIcc).aestronglyMeasurable
    (ae_of_all _ fun _ => g.norm_coe_le_norm _)

lemma continuous_cost : Continuous (cost μ) :=
  (LipschitzWith.of_le_add_mul' 1 fun g g' => by
    -- `g ≤ g' + dist g g'` pointwise
    have hpt : ∀ θ, g (projIcc 0 1 zero_le_one θ) ≤
        g' (projIcc 0 1 zero_le_one θ) + dist g g' := fun θ => by
      have := dist_coe_le_dist (f := g) (g := g') (projIcc 0 1 zero_le_one θ)
      rw [Real.dist_eq] at this; linarith [le_abs_self (g (projIcc 0 1 zero_le_one θ) -
        g' (projIcc 0 1 zero_le_one θ))]
    have := integral_mono (integrable_cost (μ := μ) g)
      ((integrable_cost g').add (integrable_const (dist g g'))) hpt
    simp only [Pi.add_apply] at this
    rw [integral_add (integrable_cost g') (integrable_const _), integral_const] at this
    simpa [cost] using this).continuous

omit [IsProbabilityMeasure μ] in
lemma cost_toB (hμ : ∀ᵐ θ ∂μ, θ ∈ Icc (0 : ℝ) 1) {f : ℝ → ℝ} (hf : Continuous f) :
    cost μ (toB f hf) = ∫ θ, f θ ∂μ :=
  integral_congr_ae (hμ.mono fun θ hθ => by simp [projIcc_of_mem _ hθ])

end cost

/-- The candidate restrictions: `L`-Lipschitz with values in `[-B, B + L]`. -/
def candidates (L B : ℝ) : Set (I →ᵇ ℝ) :=
  {g | (∀ x y : I, g x ≤ g y + L * dist x y) ∧ ∀ x, g x ∈ Icc (-B) (B + L)}

/-- **Arzelà–Ascoli**: the candidates form a compact set. -/
lemma isCompact_candidates (B : ℝ) : IsCompact (candidates L B) := by
  have hc : candidates L B = (⋂ x : I, ⋂ y : I, {g : I →ᵇ ℝ | g x ≤ g y + L * dist x y}) ∩
      ⋂ x : I, (fun g : I →ᵇ ℝ => g x) ⁻¹' Icc (-B) (B + L) := by
    ext g
    simp only [candidates, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage]
  refine arzela_ascoli₂ (Icc (-B) (B + L)) isCompact_Icc _ ?_ (fun f x hf => hf.2 x) ?_
  · rw [hc]
    exact (isClosed_iInter fun x => isClosed_iInter fun y => isClosed_le
      (continuous_eval_const x) ((continuous_eval_const y).add continuous_const)).inter
      (isClosed_iInter fun x => isClosed_Icc.preimage (continuous_eval_const x))
  · exact (LipschitzWith.uniformEquicontinuous _ _ fun g =>
      LipschitzWith.of_le_add_mul' L g.2.1).equicontinuous

/-! ### The limit of a minimising sequence -/

/-- `lipPrice` restricted to `[0, 1]`. -/
noncomputable def lipB {B : ℝ} (hB : ∀ x ∈ Icc (0 : ℝ) 1, |V x| ≤ B) (hL : 0 ≤ L) (p : ℝ → ℝ) :
    I →ᵇ ℝ :=
  toB (lipPrice L V p) (continuous_of_convexOn (convexOn_lipPrice hB hL))

/-- **Limits of Lipschitz prices are supported**: the clamped slopes at each `x` converge along a
subsequence, and the lines through `(x, V x)` pass to the limit. -/
lemma supported_of_tendsto {B : ℝ} (hB : ∀ x ∈ Icc (0 : ℝ) 1, |V x| ≤ B) (hL : 0 ≤ L)
    {P : ℕ → ℝ → ℝ} {g : I →ᵇ ℝ} (hlim : Tendsto (fun n => lipB hB hL (P n)) atTop (𝓝 g)) :
    Supported V L g := fun x => by
  obtain ⟨b, hb, ψ, hψ, hblim⟩ := isCompact_Icc.tendsto_subseq fun n =>
    abs_le.1 (abs_clampSlope_le (p := P n) hL x)
  exact ⟨b, hb, fun y => le_of_tendsto_of_tendsto' (tendsto_const_nhds.add (hblim.mul_const _))
    (((continuous_eval_const y).tendsto g).comp (hlim.comp hψ.tendsto_atTop))
    fun n => line_le_lipPrice hB hL x y⟩

variable [IsProbabilityMeasure μ]

/-- **A supported limit**: the restrictions of a minimising sequence of Lipschitz prices have a
uniform limit `g` that is supported and costs at most the dual value. -/
lemma exists_supported (hμ : ∀ᵐ θ ∂μ, θ ∈ Icc (0 : ℝ) 1) (hV : IsPayoff V) {B : ℝ}
    (hB : ∀ x ∈ Icc (0 : ℝ) 1, |V x| ≤ B) (hL : 0 ≤ L)
    (hLip : ∀ x ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (0 : ℝ) 1, V y ≤ V x + L * |x - y|) :
    ∃ g : I →ᵇ ℝ, Supported V L g ∧ cost μ g ≤ priceValue V μ := by
  set D := priceValue V μ
  obtain ⟨B₀, hB₀⟩ := exists_isPrice_const hV
  have : Nonempty {p // IsPrice V p} := ⟨⟨_, hB₀⟩⟩
  -- a minimising sequence of prices, made Lipschitz and restricted to `[0, 1]`
  have hseq : ∀ n : ℕ, ∃ p, IsPrice V p ∧ ∫ θ, p θ ∂μ < D + 1 / (n + 1) := fun n => by
    obtain ⟨⟨p, hp⟩, h⟩ := exists_lt_of_ciInf_lt
      (lt_add_of_pos_right D (by positivity : (0 : ℝ) < 1 / (n + 1)))
    exact ⟨p, hp, h⟩
  choose P hP hPc using hseq
  set q : ℕ → I →ᵇ ℝ := fun n => lipB hB hL (P n)
  have hq : ∀ n, q n ∈ candidates L B := fun n =>
    ⟨fun x y => by simpa [q, lipB, Subtype.dist_eq, Real.dist_eq] using lipPrice_lip hB hL x y,
      fun x => lipPrice_mem hB hL x.2⟩
  have hqc : ∀ n, cost μ (q n) ≤ D + 1 / (n + 1) := fun n => by
    rw [show q n = lipB hB hL (P n) from rfl, lipB, cost_toB hμ]
    exact (integral_mono_ae (integrable_of_mem hμ
      (.of_continuous (continuous_of_convexOn (convexOn_lipPrice hB hL))))
      (integrable_of_mem hμ (.of_continuous (hP n).continuous))
      (hμ.mono fun θ hθ => (lipPrice_spec hB hL hLip (hP n)).2 θ hθ)).trans (hPc n).le
  obtain ⟨g, -, φ, hφ, hlim⟩ := (isCompact_candidates B).tendsto_subseq hq
  refine ⟨g, supported_of_tendsto hB hL hlim, ?_⟩
  -- the costs converge to that of `g`, and are at most `D + 1 / (n + 1)`
  have hD : Tendsto (fun n => D + 1 / ((φ n : ℝ) + 1)) atTop (𝓝 D) := by
    have := (tendsto_const_nhds (x := D)).add
      (tendsto_one_div_add_atTop_nhds_zero_nat.comp hφ.tendsto_atTop)
    rw [add_zero] at this; exact this
  exact le_of_tendsto_of_tendsto' ((continuous_cost.tendsto g).comp hlim) hD fun n => hqc (φ n)

/-- **The best price exists** when `V` is `L`-Lipschitz on `[0, 1]`: some price costs exactly
the dual value. -/
theorem exists_optimal_price (hμ : ∀ᵐ θ ∂μ, θ ∈ Icc (0 : ℝ) 1) (hV : IsPayoff V) (hL : 0 ≤ L)
    (hLip : ∀ x ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (0 : ℝ) 1, V y ≤ V x + L * |x - y|) :
    ∃ p, IsPrice V p ∧ ∫ θ, p θ ∂μ = priceValue V μ := by
  obtain ⟨B, hB⟩ := hV.bdd
  obtain ⟨g, hg, hcost⟩ := exists_supported hμ hV hB hL hLip
  have hp := isPrice_lowerHull hL hg
  -- the hull of the limit lies below it, so costs at most the dual value
  refine ⟨_, hp, le_antisymm ((integral_mono_ae (integrable_of_mem hμ
    (.of_continuous hp.continuous)) (integrable_cost g) (hμ.mono fun θ hθ => ?_)).trans hcost)
    (priceValue_le hμ hV hp)⟩
  simpa [projIcc_of_mem _ hθ] using lowerHull_le hL g ⟨θ, hθ⟩

end MeanPersuasion
