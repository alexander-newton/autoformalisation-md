import MechDesign

open MeasureTheory Set MeanPersuasion

noncomputable section

def v2 : ℝ → ℝ := fun x => x ^ 2
def v2' : ℝ → ℝ := fun x => 2 * x

def δ : Measure ℝ := Measure.dirac (1/2)
instance : IsProbabilityMeasure δ := by unfold δ; infer_instance
lemma hδ : ∀ᵐ θ ∂δ, θ ∈ Icc (0 : ℝ) 1 :=
  (ae_dirac_iff measurableSet_Icc).2 ⟨by norm_num, by norm_num⟩

lemma priorMean_δ : priorMean δ = 1/2 := by simp [priorMean, δ]

lemma meanSupport_silent : (silent hδ).meanSupport ⊆ {1/2} := by
  apply Measure.support_subset_of_isClosed isClosed_singleton
  refine (ae_map_iff measurable_snd.aemeasurable (measurableSet_singleton (1/2 : ℝ))).2 ?_
  refine (ae_map_iff (μ := δ) (f := fun θ => (θ, priorMean δ)) (by fun_prop)
    ((measurableSet_singleton (1/2 : ℝ)).preimage measurable_snd)).2 ?_
  exact ae_of_all _ fun _ => by simp [priorMean_δ]

/-- Without full support the "only if" of Theorem 6 fails: the silent signal is the only one
(so optimal), yet (M) fails at `x = 0`. We show (M) fails. -/
example : ¬ CondM v2 v2' (silent hδ).meanSupport (silent hδ) := by
  intro hM
  have := hM.le 0 ⟨le_rfl, zero_le_one⟩
  have : Nonempty (silent hδ).meanSupport := Signal.meanSupport_nonempty.to_subtype
  have hle : tangentPrice v2 v2' (silent hδ).meanSupport 0 ≤ -1/4 := by
    unfold tangentPrice lineSup
    refine ciSup_le fun y => ?_
    have hy : (y : ℝ) = 1/2 := meanSupport_silent y.2
    simp only [v2, v2', hy]; norm_num
  simp [v2] at *; linarith

/-- ... and the silent signal is optimal (every signal with prior δ has value ≤ v(1/2)). -/
example : ∀ S' : Signal, S'.prior = δ → S'.value v2 ≤ (silent hδ).value v2 := by
  intro S' hS'
  -- price: the constant... use the state price p = v2 restricted? use a convex price x ↦ x^2
  have hp : IsPrice v2 v2 := ⟨by unfold v2; exact Even.convexOn_pow even_two, fun _ _ => le_rfl⟩
  have h1 := S'.value_le (.of_continuous hp.continuous) hp
  rw [hS'] at h1
  have h2 : (silent hδ).value v2 = v2 (1/2) := by
    rw [Signal.value, show (silent hδ).π = δ.map fun θ => (θ, priorMean δ) from rfl,
      integral_map (by fun_prop) (by unfold v2; fun_prop)]
    rw [priorMean_δ]; simp [δ]
  rw [h2]; simpa [δ] using h1

end
