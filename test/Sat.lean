import MechDesign

open MeasureTheory Set MeanPersuasion

noncomputable section

/-- The uniform prior on [0, 1]. -/
def U : Measure ℝ := volume.restrict (Icc (0 : ℝ) 1)

instance : IsProbabilityMeasure U := ⟨by simp [U]⟩

lemma hU : ∀ᵐ θ ∂U, θ ∈ Icc (0 : ℝ) 1 := ae_restrict_mem measurableSet_Icc

lemma hUfull : Icc (0 : ℝ) 1 ⊆ U.support := by
  have h1 : Ioo (0 : ℝ) 1 ⊆ U.support := by
    intro x hx
    have : x ∈ interior (Icc (0 : ℝ) 1) ∩ (volume : Measure ℝ).support := by
      rw [interior_Icc, Measure.support_eq_univ]; exact ⟨hx, trivial⟩
    exact Measure.interior_inter_support this
  have h2 := closure_mono h1
  rw [closure_Ioo zero_ne_one, Measure.isClosed_support.closure_eq] at h2
  exact h2

/-- v = x², v' = 2x. -/
def v2 : ℝ → ℝ := fun x => x ^ 2
def v2' : ℝ → ℝ := fun x => 2 * x

lemma hv2 : IsPayoff v2 := .of_continuous (by unfold v2; fun_prop)
lemma hv2u : UpperSemicontinuous v2 := (by unfold v2; fun_prop : Continuous v2).upperSemicontinuous
lemma hd2 : ∀ x ∈ Icc (0 : ℝ) 1, HasDerivWithinAt v2 (v2' x) (Icc 0 1) x := fun x _ => by
  unfold v2 v2'; simpa using (hasDerivAt_pow 2 x).hasDerivWithinAt
lemma hc2 : ContinuousOn v2' (Icc 0 1) := by unfold v2'; fun_prop
lemma hLip2 : ∀ x ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (0 : ℝ) 1, v2 y ≤ v2 x + 2 * |x - y| := by
  intro x hx y hy
  simp only [v2]
  rcases le_total x y with h | h
  · rw [abs_of_nonpos (by linarith)]; nlinarith [hx.1, hx.2, hy.1, hy.2]
  · rw [abs_of_nonneg (by linarith)]; nlinarith [hx.1, hx.2, hy.1, hy.2]

/-- Theorem 6 instantiated: full disclosure is optimal for convex v, so (M) holds. -/
example : CondM v2 v2' (full U hU).meanSupport (full U hU) :=
  (optimal_iff_condM hU hv2 hd2 hc2 hUfull (full_prior hU)).1 fun S' hS' =>
    full_optimal (μ := U) (by unfold v2; exact (Even.convexOn_pow even_two)) hU S' hS'

/-- Remark 1 instantiated. -/
example : (∀ S' : Signal, S'.prior = U → S'.value v2 ≤ (full U hU).value v2) ↔
    (full U hU).meanSupport ⊆ maxMoments v2 v2' (full U hU) ∧
      CondM v2 v2' (maxMoments v2 v2' (full U hU)) (full U hU) :=
  optimal_iff_maxMoments hU hv2 hd2 hc2 hUfull (full_prior hU)
    (fun S' hS' => full_optimal (μ := U) (by unfold v2; exact (Even.convexOn_pow even_two)) hU S' hS')
    (full_prior hU)

/-- Corollary 2 and Theorem 5 instantiated. -/
example : ∃ pM _q : ℝ → ℝ, EqOn pM pM U.support := by
  obtain ⟨p, hp, hopt⟩ := exists_optimal_statePrice hLip2 hU hv2
  obtain ⟨pM, q, -⟩ := momentPrice_spec hU hv2 hLip2 hp hopt
  exact ⟨pM, q, fun _ _ => rfl⟩

/-- Theorem 4 instantiated (with a Dirac prior η). -/
example : concaveClosure v2 (Measure.dirac (1/2)) - concaveClosure v2 U ≤
    2 * krDist (Measure.dirac (1/2)) U :=
  concaveClosure_lip hv2 hLip2 hU ((ae_dirac_iff measurableSet_Icc).2 ⟨by norm_num, by norm_num⟩)

/-- Theorem 3 instantiated; all three conditions hold. -/
example : Superdifferentiable v2 U ∧ BoundedSteepness v2 U := by
  have h := dual_attainment_tfae hU hv2 hv2u
  have hb : BoundedSteepness v2 U := boundedSteepness_of_lip hv2 hLip2 hU
  exact ⟨(h.out 2 3).2 hb, hb⟩

/-- Theorem 2 instantiated. -/
example : ∃ S : Signal, S.prior = U ∧ (∀ S' : Signal, S'.prior = U → S'.value v2 ≤ S.value v2) ∧
    S.value v2 = stateValue v2 U := exists_optimal_signal_stateValue hU hv2 hv2u

/-- Sanity: `krDist` is not junk; `d(δ₁, δ₀) ≥ 1` via the test function `id`. -/
example : 1 ≤ krDist (Measure.dirac 1) (Measure.dirac 0) := by
  have := le_krDist (μ := Measure.dirac 0) ((ae_dirac_iff measurableSet_Icc).2 ⟨le_rfl, zero_le_one⟩)
    ((ae_dirac_iff measurableSet_Icc).2 ⟨zero_le_one, le_rfl⟩)
    ⟨id, LipschitzWith.id, rfl⟩
  simpa using this

/-- Sanity: `stateValue` is a genuine upper bound on signal values. -/
example : (silent hU).value v2 ≤ stateValue v2 U := by
  obtain ⟨S, -, hopt, hval⟩ := exists_optimal_signal_stateValue hU hv2 hv2u
  exact hval ▸ hopt _ (silent_prior hU)

end
