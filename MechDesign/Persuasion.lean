/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import MechDesign.Duality

/-!
# The persuasion duality (Kolotilin 2018; Dworczak–Kolotilin 2024), finite version

A sender commits to an information structure; a receiver with utility `w a θ` takes an action.
By the revelation principle the sender chooses a joint distribution `x (a, θ)` of
recommended action and state with state-marginal equal to the prior `μ` and subject to
*obedience*.  This is a linear program (Kolotilin 2018, "Optimal information disclosure: a
linear programming approach").

Its dual assigns a **price** `p θ` to each state:
`p_y θ = max_a [v a θ + ∑_{a'} y (a, a') (w a θ - w a' θ)]` for obedience multipliers `y ≥ 0`.
We prove

* `weak_duality`: every obedient scheme earns at most `∑ μ θ p_y θ`;
* `exists_optimal`: an optimal obedient scheme exists;
* `strong_duality`: the optimal value equals `inf_{y ≥ 0} ∑ μ θ p_y θ`
  (no duality gap).
-/

open Finset ContinuousLinearMap

namespace Persuasion

set_option linter.unusedSectionVars false

variable {Θ A : Type*} [Fintype Θ] [Fintype A] [DecidableEq A] (μ : Θ → ℝ) (v w : A → Θ → ℝ)

/-- Recommendation schemes: joint distributions of (recommended action, state) consistent with
the prior. -/
def Schemes : Set (A × Θ → ℝ) := {x | 0 ≤ x ∧ ∀ θ, ∑ a, x (a, θ) = μ θ}

/-- Sender's expected utility. -/
noncomputable def obj : (A × Θ → ℝ) →L[ℝ] ℝ := ∑ i : A × Θ, v i.1 i.2 • proj i

/-- Obedience slack of recommendation `p.1` against deviation `p.2`. -/
noncomputable def obed (p : A × A) : (A × Θ → ℝ) →L[ℝ] ℝ :=
  ∑ θ, (w p.1 θ - w p.2 θ) • proj (p.1, θ)

/-- Obedience: following each recommendation is optimal for the receiver. -/
def Obedient (x : A × Θ → ℝ) : Prop := ∀ p, 0 ≤ obed w p x

/-- The deterministic scheme recommending `s θ` in state `θ`. -/
def pure (s : Θ → A) : A × Θ → ℝ := fun i => if i.1 = s i.2 then μ i.2 else 0

variable {μ v w}

lemma obj_apply (x : A × Θ → ℝ) : obj v x = ∑ a, ∑ θ, x (a, θ) * v a θ := by
  simp [obj, Fintype.sum_prod_type, mul_comm]

lemma obed_apply (x : A × Θ → ℝ) (p : A × A) : obed w p x = ∑ θ, x (p.1, θ) * (w p.1 θ - w p.2 θ) := by
  simp [obed, mul_comm]

lemma pure_mem (hμ : 0 ≤ μ) (s : Θ → A) : pure μ s ∈ Schemes μ :=
  ⟨fun i => by unfold pure; split_ifs; exacts [hμ i.2, le_rfl], fun θ => by simp [pure]⟩

lemma sum_pure (s : Θ → A) (F : A → Θ → ℝ) :
    ∑ θ, ∑ a, pure μ s (a, θ) * F a θ = ∑ θ, μ θ * F (s θ) θ := by
  simp [pure, ite_mul]

lemma prior_nonneg {x : A × Θ → ℝ} (hx : x ∈ Schemes μ) : 0 ≤ μ :=
  fun θ => hx.2 θ ▸ sum_nonneg fun a _ => hx.1 (a, θ)


lemma schemes_convex : Convex ℝ (Schemes μ : Set (A × Θ → ℝ)) := by
  intro x hx x' hx' s t hs ht hst
  refine ⟨add_nonneg (smul_nonneg hs hx.1) (smul_nonneg ht hx'.1), fun θ => ?_⟩
  simp [sum_add_distrib, ← mul_sum, hx.2, hx'.2, ← add_mul, hst]

lemma schemes_compact : IsCompact (Schemes μ : Set (A × Θ → ℝ)) := by
  refine Metric.isCompact_of_isClosed_isBounded ?_ ?_
  · simp only [Schemes, Set.ofPred_and, Set.ofPred_forall]
    exact (isClosed_le continuous_const continuous_id).inter <| isClosed_iInter fun θ =>
      isClosed_eq (continuous_finsetSum _ fun a _ => continuous_apply _) continuous_const
  · refine (Metric.isBounded_Icc (0 : A × Θ → ℝ) (fun i => μ i.2)).subset fun x hx =>
      ⟨hx.1, fun i => ?_⟩
    show x i ≤ μ i.2
    rw [← hx.2 i.2]
    exact single_le_sum (f := fun a => x (a, i.2)) (fun a _ => hx.1 (a, i.2)) (mem_univ i.1)

/-! ### Duality -/

section Duality

variable [Nonempty A] (μ v w)

/-- Lagrangian payoff of recommending `a` in state `θ`. -/
def lag (y : A × A → ℝ) (a : A) (θ : Θ) : ℝ := v a θ + ∑ a', y (a, a') * (w a θ - w a' θ)

/-- The dual **price of state `θ`**: the best Lagrangian payoff available in `θ`. -/
noncomputable def price (y : A × A → ℝ) (θ : Θ) : ℝ := univ.sup' univ_nonempty (lag v w y · θ)

/-- Dual objective. -/
noncomputable def dualValue (y : A × A → ℝ) : ℝ := ∑ θ, μ θ * price v w y θ

variable {μ v w}

/-- Lagrangian = expected Lagrangian payoff. -/
lemma lagrangian_eq (x : A × Θ → ℝ) (y : A × A → ℝ) :
    obj v x + ∑ p, y p * obed w p x = ∑ θ, ∑ a, x (a, θ) * lag v w y a θ := by
  simp only [obj_apply, obed_apply, lag, mul_add, sum_add_distrib, mul_sum, Fintype.sum_prod_type]
  congr 1
  · exact sum_comm
  · conv_rhs => rw [sum_comm]
    refine sum_congr rfl fun a _ => ?_
    rw [sum_comm]
    exact sum_congr rfl fun θ _ => sum_congr rfl fun a' _ => by ring

/-- **Weak persuasion duality**: every obedient scheme earns at most the expected state
price. -/
theorem weak_duality {x : A × Θ → ℝ} (hx : x ∈ Schemes μ) (hob : Obedient w x)
    {y : A × A → ℝ} (hy : 0 ≤ y) : obj v x ≤ dualValue μ v w y :=
  calc obj v x ≤ obj v x + ∑ p, y p * obed w p x :=
        le_add_of_nonneg_right (sum_nonneg fun p _ => mul_nonneg (hy p) (hob p))
    _ = ∑ θ, ∑ a, x (a, θ) * lag v w y a θ := lagrangian_eq x y
    _ ≤ _ := sum_le_sum fun θ _ => by
        rw [← hx.2 θ, sum_mul]
        exact sum_le_sum fun a _ =>
          mul_le_mul_of_nonneg_left (le_sup' (lag v w y · θ) (mem_univ a)) (hx.1 (a, θ))

/-- An optimal obedient scheme exists: the feasible set is compact, and nonempty because
recommending a prior-optimal action in every state is obedient. -/
theorem exists_optimal (hμ : 0 ≤ μ) :
    ∃ xs ∈ Schemes μ, Obedient w xs ∧ ∀ x ∈ Schemes μ, Obedient w x → obj v x ≤ obj v xs := by
  have hF : IsCompact (Schemes μ ∩ {x | Obedient w x}) :=
    schemes_compact.inter_right <| by
      simpa only [Obedient, Set.ofPred_forall] using
        isClosed_iInter fun p => isClosed_le continuous_const (obed w p).continuous
  obtain ⟨a₀, -, ha₀⟩ := exists_max_image univ (fun a => ∑ θ, μ θ * w a θ) univ_nonempty
  have h₀ : Obedient w (pure μ fun _ => a₀) := fun p => by
    rw [obed_apply]
    by_cases h : p.1 = a₀
    · simp only [pure, h, ite_true, mul_sub, sum_sub_distrib]
      linarith [ha₀ p.2 (mem_univ _)]
    · simp [pure, h]
  obtain ⟨xs, hxs, hmax⟩ := hF.exists_isMaxOn ⟨_, pure_mem hμ _, h₀⟩ (obj v).continuous.continuousOn
  exact ⟨xs, hxs.1, hxs.2, fun x hx hob => hmax ⟨hx, hob⟩⟩

/-- **Strong persuasion duality** (no gap): the value of optimal persuasion equals the
infimum over obedience multipliers `y ≥ 0` of the expected state price `∑ μ θ p_y θ`. -/
theorem strong_duality {xs : A × Θ → ℝ} (hxs : xs ∈ Schemes μ) (hob : Obedient w xs)
    (hopt : ∀ x ∈ Schemes μ, Obedient w x → obj v x ≤ obj v xs) {ε : ℝ} (hε : 0 < ε) :
    ∃ y : A × A → ℝ, 0 ≤ y ∧ dualValue μ v w y ≤ obj v xs + ε := by
  obtain ⟨y, hy, hbound⟩ :=
    Duality.strong_duality schemes_compact schemes_convex (obj v) (obed w) hxs hob hopt hε
  -- test the bound on the scheme recommending, in each state, a price-attaining action
  choose s _ hs using fun θ : Θ => exists_mem_eq_sup' univ_nonempty (lag v w y · θ)
  refine ⟨y, hy, ?_⟩
  have := hbound _ (pure_mem (prior_nonneg hxs) s)
  rwa [lagrangian_eq, sum_pure, ← sum_congr rfl fun θ _ => congrArg (μ θ * ·) (hs θ)] at this

end Duality

end Persuasion
