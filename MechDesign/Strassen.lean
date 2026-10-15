/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import MechDesign.MeanDuality
import Mathlib.Analysis.Convex.Cone.Extension
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Topology.Order.ProjIcc

/-!
# Strassen's theorem on `[0, 1]`: every distribution of posterior means comes from a signal

If `ν` is a mean-preserving contraction of `μ` (both on `[0, 1]`), there is a joint law of
`(θ, m)` with marginals `μ` and `ν` in which `m` is the conditional mean of `θ`
(`PosteriorMeans.exists_signal`). So the optimal distribution of posterior means of
`strong_duality` is induced by an actual signal (`exists_optimal_signal`).

The proof treats the coupling as a positive functional on `C([0, 1]²)`. On the test functions
`f(θ) + g(m) + h(m) (θ - m)` it must equal `∫ f dμ + ∫ g dν`. This is well defined and positive
by the **dual inequality** (`testVal_nonneg`): if a test function is nonnegative, then
`c(θ) = sup_m (-g m - h m (θ - m))` is a convex function between `-g` and `f`, so
`∫ f dμ ≥ ∫ c dμ ≥ ∫ c dν ≥ -∫ g dν`. M. Riesz's extension theorem extends it positively to
all of `C([0, 1]²)`, and Riesz–Markov–Kakutani makes it a measure.
-/

open MeasureTheory Set unitInterval CompactlySupported BoundedContinuousFunction

namespace MeanPersuasion

variable {μ : Measure ℝ} [IsProbabilityMeasure μ]

/-! ### Functions on `[0, 1]` extended to `ℝ` -/

/-- A continuous function on `[0, 1]`, extended to `ℝ` by its endpoint values. -/
noncomputable def extI (f : C(I, ℝ)) (x : ℝ) : ℝ := f (projIcc 0 1 zero_le_one x)

lemma continuous_extI (f : C(I, ℝ)) : Continuous (extI f) := f.continuous.comp continuous_projIcc

@[simp] lemma extI_coe (f : C(I, ℝ)) (x : I) : extI f x = f x := by simp [extI]

lemma extI_add (f g : C(I, ℝ)) : extI (f + g) = extI f + extI g := rfl

lemma extI_smul (k : ℝ) (f : C(I, ℝ)) : extI (k • f) = k • extI f := rfl

lemma abs_extI_le (f : C(I, ℝ)) (x : ℝ) : |extI f x| ≤ ‖f‖ :=
  abs_apply_le_norm' f _

lemma integrable_extI {ν : Measure ℝ} [IsFiniteMeasure ν] (f : C(I, ℝ)) :
    Integrable (extI f) ν :=
  (integrable_const ‖f‖).mono' (continuous_extI f).aestronglyMeasurable
    (ae_of_all _ fun x => (Real.norm_eq_abs _).trans_le (abs_extI_le f x))

/-! ### Test functions and the dual inequality -/

/-- The test functions on `[0, 1]²`: `(θ, m) ↦ f(θ) + g(m) + h(m) (θ - m)`. -/
noncomputable def testFn : (C(I, ℝ) × C(I, ℝ)) × C(I, ℝ) →ₗ[ℝ] C(I × I, ℝ) where
  toFun x := ⟨fun z => x.1.1 z.1 + x.1.2 z.2 + x.2 z.2 * ((z.1 : ℝ) - z.2), by fun_prop⟩
  map_add' _ _ := by ext; simp; ring
  map_smul' _ _ := by ext; simp; ring

@[simp] lemma testFn_apply (x : (C(I, ℝ) × C(I, ℝ)) × C(I, ℝ)) (z : I × I) :
    testFn x z = x.1.1 z.1 + x.1.2 z.2 + x.2 z.2 * ((z.1 : ℝ) - z.2) := rfl

/-- The value the coupling must give a test function: `∫ f dμ + ∫ g dν`. -/
noncomputable def testVal (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    (C(I, ℝ) × C(I, ℝ)) × C(I, ℝ) →ₗ[ℝ] ℝ where
  toFun x := ∫ θ, extI x.1.1 θ ∂μ + ∫ m, extI x.1.2 m ∂ν
  map_add' x y := by
    simp only [Prod.fst_add, Prod.snd_add, extI_add, Pi.add_apply]
    rw [integral_add (integrable_extI _) (integrable_extI _),
      integral_add (integrable_extI _) (integrable_extI _)]; ring
  map_smul' k x := by
    simp only [Prod.smul_fst, Prod.smul_snd, extI_smul, Pi.smul_apply, smul_eq_mul,
      RingHom.id_apply, integral_const_mul]; ring

@[simp] lemma testVal_apply (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (x : (C(I, ℝ) × C(I, ℝ)) × C(I, ℝ)) :
    testVal μ ν x = ∫ θ, extI x.1.1 θ ∂μ + ∫ m, extI x.1.2 m ∂ν := rfl

/-- The **envelope** of a test function: `c(θ) = sup_m (-g m - h m (θ - m))`, the least
function forced on `f` by `f(θ) + g(m) + h(m) (θ - m) ≥ 0`. -/
noncomputable def envelope (g h : C(I, ℝ)) (θ : ℝ) : ℝ := ⨆ m : I, (-g m - h m * (θ - m))

section envelope

variable (g h : C(I, ℝ))

lemma envelope_bdd (θ : ℝ) : BddAbove (range fun m : I => -g m - h m * (θ - m)) :=
  ⟨‖g‖ + ‖h‖ * (1 + |θ|), by
    rintro _ ⟨m, rfl⟩
    have hg := abs_apply_le_norm' g m
    have hh := abs_apply_le_norm' h m
    have : |h m * (θ - m)| ≤ ‖h‖ * (1 + |θ|) := by
      rw [abs_mul]; exact mul_le_mul hh ((abs_sub _ _).trans (by linarith [abs_le_one_of_mem m]))
        (abs_nonneg _) (norm_nonneg _)
    linarith [neg_le_abs (h m * (θ - m)), neg_le_abs (g m)]⟩

/-- A supremum of lines is convex. -/
lemma convexOn_envelope : ConvexOn ℝ univ (envelope g h) :=
  ⟨convex_univ, fun x _ y _ s t hs ht hst => ciSup_le fun m => by
    have hx := le_ciSup (envelope_bdd g h x) m
    have hy := le_ciSup (envelope_bdd g h y) m
    simp only [smul_eq_mul, envelope] at hx hy ⊢
    calc -g m - h m * (s * x + t * y - m)
        = s * (-g m - h m * (x - m)) + t * (-g m - h m * (y - m)) := by
          linear_combination (g m - h m * m) * hst
      _ ≤ _ := by gcongr⟩

lemma neg_le_envelope (m : I) : -extI g m ≤ envelope g h m :=
  le_ciSup_of_le (envelope_bdd g h m) m (by simp)

lemma envelope_le {f : C(I, ℝ)} (hx : 0 ≤ testFn ((f, g), h)) (θ : I) :
    envelope g h θ ≤ extI f θ := ciSup_le fun m => by
  have := ContinuousMap.le_def.1 hx (θ, m)
  simp only [testFn_apply, ContinuousMap.zero_apply] at this
  simp only [extI_coe]; linarith

end envelope

/-- **The dual inequality** (the easy half of Strassen's theorem): if
`f(θ) + g(m) + h(m) (θ - m) ≥ 0` on `[0, 1]²`, then `∫ f dμ + ∫ g dν ≥ 0`. -/
theorem testVal_nonneg (hμ : ∀ᵐ θ ∂μ, θ ∈ Icc (0 : ℝ) 1) (G : PosteriorMeans μ)
    (x : (C(I, ℝ) × C(I, ℝ)) × C(I, ℝ)) (hx : 0 ≤ testFn x) : 0 ≤ testVal μ G.ν x := by
  obtain ⟨⟨f, g⟩, h⟩ := x
  have hc := IsPayoff.of_continuous (continuous_of_convexOn (convexOn_envelope g h))
  -- `∫ f dμ ≥ ∫ c dμ ≥ ∫ c dν ≥ -∫ g dν`, with `c` the envelope
  have h1 := integral_mono_ae (integrable_of_mem hμ hc) (integrable_extI (ν := μ) f)
    (hμ.mono fun θ hθ => envelope_le g h hx ⟨θ, hθ⟩)
  have h2 := G.contraction _ (convexOn_envelope g h)
  have h3 := integral_mono_ae (integrable_extI (ν := G.ν) g).neg (integrable_of_mem G.mem hc)
    (G.mem.mono fun m hm => neg_le_envelope g h ⟨m, hm⟩)
  simp only [Pi.neg_apply, integral_neg] at h3
  rw [testVal_apply]; linarith

/-! ### The coupling as a positive functional -/

/-- The cone of nonnegative continuous functions. -/
def posCone (X : Type*) [TopologicalSpace X] : PointedCone ℝ C(X, ℝ) where
  carrier := {f | 0 ≤ f}
  add_mem' hf hg := ContinuousMap.le_def.2 fun x => by
    simpa using add_nonneg (ContinuousMap.le_def.1 hf x) (ContinuousMap.le_def.1 hg x)
  zero_mem' := show (0 : C(X, ℝ)) ≤ 0 from le_rfl
  smul_mem' c f hf := ContinuousMap.le_def.2 fun x =>
    show (0 : ℝ) ≤ (c : ℝ) * f x from mul_nonneg c.2 (ContinuousMap.le_def.1 hf x)

lemma mem_posCone {X : Type*} [TopologicalSpace X] {f : C(X, ℝ)} : f ∈ posCone X ↔ 0 ≤ f :=
  Iff.rfl

/-- `testVal` descends to the space of test functions: it vanishes on the kernel of `testFn`,
by the dual inequality applied to `±x`. -/
lemma exists_range_functional (hμ : ∀ᵐ θ ∂μ, θ ∈ Icc (0 : ℝ) 1) (G : PosteriorMeans μ) :
    ∃ ψ : LinearMap.range testFn →ₗ[ℝ] ℝ,
      ∀ x, ψ ⟨testFn x, LinearMap.mem_range_self _ x⟩ = testVal μ G.ν x := by
  have hker : LinearMap.ker testFn ≤ LinearMap.ker (testVal μ G.ν) := fun x hx => by
    rw [LinearMap.mem_ker] at hx ⊢
    have h1 := testVal_nonneg hμ G x (by rw [hx])
    have h2 := testVal_nonneg hμ G (-x) (by rw [map_neg, hx, neg_zero])
    rw [map_neg] at h2; linarith
  exact ⟨(LinearMap.ker testFn).liftQ (testVal μ G.ν) hker ∘ₗ
    testFn.quotKerEquivRange.symm.toLinearMap,
    fun x => by simp [LinearMap.quotKerEquivRange_symm_apply_image]⟩

/-- **The coupling functional** (M. Riesz extension): a positive linear functional on
`C([0, 1]²)` giving each test function its value `∫ f dμ + ∫ g dν`. -/
theorem exists_coupling_functional (hμ : ∀ᵐ θ ∂μ, θ ∈ Icc (0 : ℝ) 1) (G : PosteriorMeans μ) :
    ∃ Λ : C(I × I, ℝ) →ₗ[ℝ] ℝ, (∀ h, 0 ≤ h → 0 ≤ Λ h) ∧ ∀ x, Λ (testFn x) = testVal μ G.ν x := by
  obtain ⟨ψ, hψ⟩ := exists_range_functional hμ G
  -- it is positive, and every function lies below a constant test function
  have hnonneg : ∀ y : LinearMap.range testFn, (y : C(I × I, ℝ)) ∈ posCone (I × I) →
      0 ≤ ψ y := by
    rintro ⟨_, x, rfl⟩ hy; exact (hψ x).symm ▸ testVal_nonneg hμ G x (mem_posCone.1 hy)
  have hdense : ∀ y : C(I × I, ℝ), ∃ x : LinearMap.range testFn,
      (x : C(I × I, ℝ)) + y ∈ posCone (I × I) := fun y =>
    ⟨⟨testFn ((‖y‖ • 1, 0), 0), LinearMap.mem_range_self _ _⟩,
      mem_posCone.2 <| ContinuousMap.le_def.2 fun z => by
        have := abs_apply_le_norm' y z
        have h1 : testFn ((‖y‖ • (1 : C(I, ℝ)), 0), 0) z = ‖y‖ := by simp
        simp only [ContinuousMap.zero_apply, ContinuousMap.add_apply, h1]
        linarith [neg_abs_le (y z)]⟩
  obtain ⟨Λ, hext, hpos⟩ := riesz_extension (posCone (I × I)) ⟨_, ψ⟩ hnonneg hdense
  exact ⟨Λ, hpos, fun x => (hext ⟨testFn x, LinearMap.mem_range_self _ x⟩).trans (hψ x)⟩

/-! ### From continuous to measurable test functions -/

/-- The weight `q z` clipped to `[0, 1]`, as a density. -/
noncomputable def clip01 (q : ℝ × ℝ → ℝ) (z : ℝ × ℝ) : NNReal :=
  ⟨projIcc 0 1 zero_le_one (q z), (projIcc 0 1 zero_le_one (q z)).2.1⟩

/-- The law of `m` weighted by `q`: `∫ g dρ = ∫ q z g(m) dπ`. -/
noncomputable def weighted (π : Measure (ℝ × ℝ)) (q : ℝ × ℝ → ℝ) : Measure ℝ :=
  (π.withDensity fun z => clip01 q z).map Prod.snd

lemma integral_weighted {π : Measure (ℝ × ℝ)} {q : ℝ × ℝ → ℝ} (hq : Continuous q)
    (hmem : ∀ᵐ z ∂π, q z ∈ Icc (0 : ℝ) 1) {g : ℝ → ℝ} (hg : Measurable g) :
    ∫ m, g m ∂(weighted π q) = ∫ z, q z * g z.2 ∂π := by
  have hc : Measurable (clip01 q) :=
    (continuous_subtype_val.comp (continuous_projIcc.comp hq)).measurable.subtype_mk
  rw [weighted, integral_map measurable_snd.aemeasurable hg.aestronglyMeasurable,
    integral_withDensity_eq_integral_smul hc]
  refine integral_congr_ae (hmem.mono fun z hz => ?_)
  simp [clip01, projIcc_of_mem _ hz]; rfl

instance {π : Measure (ℝ × ℝ)} [IsFiniteMeasure π] (q : ℝ × ℝ → ℝ) :
    IsFiniteMeasure (weighted π q) := by
  have : IsFiniteMeasure (π.withDensity fun z => clip01 q z) :=
    isFiniteMeasure_withDensity <| ne_top_of_le_ne_top (measure_ne_top π univ) <|
      (lintegral_mono fun z => ENNReal.coe_le_one_iff.2 (projIcc 0 1 zero_le_one (q z)).2.2).trans
        (by simp)
  unfold weighted; infer_instance

/-- **The mean condition on continuous test functions suffices**: the two weighted laws of
`m` agree on bounded continuous functions, hence as measures. -/
lemma mean_eq_of_continuous {π : Measure (ℝ × ℝ)} [IsFiniteMeasure π]
    (h1 : ∀ᵐ z ∂π, z.1 ∈ Icc (0 : ℝ) 1) (h2 : ∀ᵐ z ∂π, z.2 ∈ Icc (0 : ℝ) 1)
    (h : ∀ g : ℝ →ᵇ ℝ, ∫ z, z.1 * g z.2 ∂π = ∫ z, z.2 * g z.2 ∂π) {g : ℝ → ℝ}
    (hg : Measurable g) : ∫ z, z.1 * g z.2 ∂π = ∫ z, z.2 * g z.2 ∂π := by
  have he : weighted π Prod.fst = weighted π Prod.snd :=
    ext_of_forall_integral_eq_of_IsFiniteMeasure fun f => by
      rw [integral_weighted continuous_fst h1 f.continuous.measurable,
        integral_weighted continuous_snd h2 f.continuous.measurable, h f]
  rw [← integral_weighted continuous_fst h1 hg, ← integral_weighted continuous_snd h2 hg, he]

/-! ### The signal -/

lemma extI_zero : extI 0 = 0 := rfl

lemma integral_extI_onI {ν : Measure ℝ} (hν : ∀ᵐ x ∂ν, x ∈ Icc (0 : ℝ) 1) {f : ℝ → ℝ}
    (hf : Continuous f) : ∫ x, extI (onI f hf) x ∂ν = ∫ x, f x ∂ν :=
  integral_congr_ae (hν.mono fun x hx => by simp [extI, onI, projIcc_of_mem _ hx])

/-- The coordinates of `[0, 1]²` in `ℝ²`. -/
def toR2 (z : I × I) : ℝ × ℝ := (z.1, z.2)

lemma continuous_toR2 : Continuous toR2 :=
  (continuous_subtype_val.comp continuous_fst).prodMk (continuous_subtype_val.comp continuous_snd)

/-- **The coupling**: a probability law of `(θ, m)` on `[0, 1]²` integrating each test function
to its value. -/
theorem exists_coupling (hμ : ∀ᵐ θ ∂μ, θ ∈ Icc (0 : ℝ) 1) (G : PosteriorMeans μ) :
    ∃ π : Measure (ℝ × ℝ), IsProbabilityMeasure π ∧ (∀ᵐ z ∂π, z.1 ∈ Icc (0 : ℝ) 1) ∧
      (∀ᵐ z ∂π, z.2 ∈ Icc (0 : ℝ) 1) ∧ ∀ x (F : ℝ × ℝ → ℝ), Continuous F →
        (∀ z, F (toR2 z) = testFn x z) → ∫ z, F z ∂π = testVal μ G.ν x := by
  obtain ⟨Λ, hpos, hΛ⟩ := exists_coupling_functional hμ G
  obtain ⟨πK, hfin, hint⟩ := exists_measure_of_pos Λ hpos
  have hm := continuous_toR2.measurable.aemeasurable (μ := πK)
  have htest : ∀ x (F : ℝ × ℝ → ℝ), Continuous F → (∀ z, F (toR2 z) = testFn x z) →
      ∫ z, F z ∂(πK.map toR2) = testVal μ G.ν x := fun x F hF h => by
    have hfx : (⟨F ∘ toR2, hF.comp continuous_toR2⟩ : C(I × I, ℝ)) = testFn x :=
      ContinuousMap.ext h
    rw [integral_map hm hF.aestronglyMeasurable, ← hΛ, ← hfx]
    exact hint ⟨F ∘ toR2, hF.comp continuous_toR2⟩
  -- the total mass is the value `∫ 1 dμ = 1` of the constant test function
  have h1 := htest ((1, 0), 0) (fun _ => 1) continuous_const fun z => by simp
  simp only [testVal_apply, extI_zero, Pi.zero_apply, integral_zero, add_zero] at h1
  refine ⟨_, isProbabilityMeasure_of_integral_one (h1.trans (by simp [extI])),
    (ae_map_iff hm (measurableSet_Icc.preimage measurable_fst)).2 (ae_of_all _ fun z => z.1.2),
    (ae_map_iff hm (measurableSet_Icc.preimage measurable_snd)).2 (ae_of_all _ fun z => z.2.2),
    htest⟩

lemma integrable_mul_bdd {π : Measure (ℝ × ℝ)} [IsFiniteMeasure π] {q : ℝ × ℝ → ℝ}
    (hq : Continuous q) (hmem : ∀ᵐ z ∂π, q z ∈ Icc (0 : ℝ) 1) (g : ℝ →ᵇ ℝ) :
    Integrable (fun z => q z * g z.2) π :=
  integrable_mul_of_mem hq hmem g.continuous.measurable fun x =>
    (Real.norm_eq_abs _).symm.trans_le (g.norm_coe_le_norm x)

/-- A law on `ℝ` is pinned down by its integrals of bounded continuous functions: the image of
`π` under `φ` is `ν` when they integrate each `f` alike. -/
lemma map_eq_of_integral {π : Measure (ℝ × ℝ)} [IsFiniteMeasure π] {ν : Measure ℝ}
    [IsFiniteMeasure ν] {φ : ℝ × ℝ → ℝ} (hφ : Continuous φ)
    (h : ∀ f : ℝ →ᵇ ℝ, ∫ z, f (φ z) ∂π = ∫ x, f x ∂ν) : π.map φ = ν :=
  ext_of_forall_integral_eq_of_IsFiniteMeasure fun f => by
    rw [integral_map hφ.measurable.aemeasurable f.continuous.aestronglyMeasurable, h f]

/-- **Strassen's theorem on `[0, 1]`**: every distribution of posterior means is the law of
the posterior mean of a signal with the given prior. -/
theorem PosteriorMeans.exists_signal (hμ : ∀ᵐ θ ∂μ, θ ∈ Icc (0 : ℝ) 1) (G : PosteriorMeans μ) :
    ∃ S : Signal, S.prior = μ ∧ S.posteriorMeans.ν = G.ν := by
  obtain ⟨π, hπ, h1, h2, htest⟩ := exists_coupling hμ G
  -- the mean condition, on bounded continuous test functions `g`
  have hmean : ∀ g : ℝ →ᵇ ℝ, ∫ z, z.1 * g z.2 ∂π = ∫ z, z.2 * g z.2 ∂π := fun g => by
    have := htest ((0, 0), onI g g.continuous) (fun z => (z.1 - z.2) * g z.2) (by fun_prop)
      fun z => by simp [toR2, onI]; ring
    simp only [testVal_apply, extI_zero, Pi.zero_apply, integral_zero, add_zero, sub_mul] at this
    rwa [integral_sub (integrable_mul_bdd continuous_fst h1 g)
      (integrable_mul_bdd continuous_snd h2 g), sub_eq_zero] at this
  let S : Signal := ⟨π, h1, h2, fun g hg _ _ => mean_eq_of_continuous h1 h2 hmean hg⟩
  -- the marginals agree with `μ` and `ν` on bounded continuous functions
  refine ⟨S, map_eq_of_integral continuous_fst fun f => ?_,
    map_eq_of_integral continuous_snd fun f => ?_⟩
  · have := htest ((onI f f.continuous, 0), 0) (fun z => f z.1) (by fun_prop)
      fun z => by simp [toR2, onI]
    simpa only [testVal_apply, extI_zero, Pi.zero_apply, integral_zero, add_zero,
      integral_extI_onI hμ] using this
  · have := htest ((0, onI f f.continuous), 0) (fun z => f z.2) (by fun_prop)
      fun z => by simp [toR2, onI]
    simpa only [testVal_apply, extI_zero, Pi.zero_apply, integral_zero, zero_add,
      integral_extI_onI G.mem] using this

/-- **An optimal signal exists** for a bounded upper semicontinuous payoff, and its value is the
least expected cost of a price. -/
theorem exists_optimal_signal {V : ℝ → ℝ} (hμ : ∀ᵐ θ ∂μ, θ ∈ Icc (0 : ℝ) 1) (hV : IsPayoff V)
    (hVu : UpperSemicontinuous V) :
    ∃ S : Signal, S.prior = μ ∧ S.value V = priceValue V μ ∧
      ∀ S' : Signal, S'.prior = μ → S'.value V ≤ S.value V := by
  obtain ⟨G, -, hG⟩ := strong_duality hμ hV hVu
  obtain ⟨S, hS, hSν⟩ := G.exists_signal hμ
  have hval : S.value V = priceValue V μ := by rw [S.value_eq hV, hSν, hG]
  exact ⟨S, hS, hval, fun S' hS' => hval ▸ hS' ▸ S'.value_le_priceValue hV⟩

end MeanPersuasion
