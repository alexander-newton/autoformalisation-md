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

open Finset

namespace Persuasion

variable {Θ A : Type*} [Fintype Θ] [Fintype A] [DecidableEq A] [DecidableEq Θ] [Nonempty A]
  (μ : Θ → ℝ) (v w : A → Θ → ℝ)

/-- Recommendation schemes: joint distributions of (recommended action, state) consistent with
the prior. -/
def Schemes : Set (A × Θ → ℝ) := {x | 0 ≤ x ∧ ∀ θ, ∑ a, x (a, θ) = μ θ}

/-- Obedience slack of recommendation `a` against deviation `a'`. -/
def obed (x : A × Θ → ℝ) (p : A × A) : ℝ := ∑ θ, x (p.1, θ) * (w p.1 θ - w p.2 θ)

/-- Obedience: following each recommendation is optimal for the receiver. -/
def Obedient (x : A × Θ → ℝ) : Prop := ∀ p, 0 ≤ obed w x p

/-- Sender's expected utility. -/
def obj (x : A × Θ → ℝ) : ℝ := ∑ a, ∑ θ, x (a, θ) * v a θ

/-- Lagrangian payoff of recommending `a` in state `θ`. -/
def lag (y : A × A → ℝ) (a : A) (θ : Θ) : ℝ := v a θ + ∑ a', y (a, a') * (w a θ - w a' θ)

/-- The dual **price of state `θ`**. -/
noncomputable def price (y : A × A → ℝ) (θ : Θ) : ℝ := univ.sup' univ_nonempty (lag v w y · θ)

/-- Dual objective. -/
noncomputable def dualValue (y : A × A → ℝ) : ℝ := ∑ θ, μ θ * price v w y θ

variable {μ v w}

lemma lagrangian_eq (x : A × Θ → ℝ) (y : A × A → ℝ) :
    obj v x + ∑ p, y p * obed w x p = ∑ θ, ∑ a, x (a, θ) * lag v w y a θ := by
  simp only [obj, obed, lag, mul_add, sum_add_distrib, mul_sum, Fintype.sum_prod_type]
  congr 1
  · exact sum_comm
  · conv_rhs => rw [sum_comm]
    refine sum_congr rfl fun a _ => ?_
    rw [sum_comm]
    exact sum_congr rfl fun θ _ => sum_congr rfl fun a' _ => by ring

lemma lagrangian_le {x : A × Θ → ℝ} (hx : x ∈ Schemes μ) (y : A × A → ℝ) :
    ∑ θ, ∑ a, x (a, θ) * lag v w y a θ ≤ dualValue μ v w y := by
  refine sum_le_sum fun θ _ => ?_
  rw [← hx.2 θ, sum_mul]
  exact sum_le_sum fun a _ =>
    mul_le_mul_of_nonneg_left (le_sup' (lag v w y · θ) (mem_univ a)) (hx.1 (a, θ))

/-- **Weak persuasion duality.** -/
theorem weak_duality {x : A × Θ → ℝ} (hx : x ∈ Schemes μ) (hob : Obedient w x)
    {y : A × A → ℝ} (hy : 0 ≤ y) : obj v x ≤ dualValue μ v w y := by
  calc obj v x ≤ obj v x + ∑ p, y p * obed w x p :=
        le_add_of_nonneg_right (sum_nonneg fun p _ => mul_nonneg (hy p) (hob p))
    _ ≤ _ := (lagrangian_eq x y).symm ▸ lagrangian_le hx y

/-! Topological facts. -/

lemma schemes_convex : Convex ℝ (Schemes μ : Set (A × Θ → ℝ)) := by
  intro x hx x' hx' s t hs ht hst
  refine ⟨fun i => ?_, fun θ => ?_⟩
  · simp only [Pi.zero_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact add_nonneg (mul_nonneg hs (hx.1 i)) (mul_nonneg ht (hx'.1 i))
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, sum_add_distrib, ← mul_sum, hx.2,
      hx'.2]
    rw [← add_mul, hst, one_mul]

lemma schemes_compact : IsCompact (Schemes μ : Set (A × Θ → ℝ)) := by
  refine Metric.isCompact_of_isClosed_isBounded ?_ ?_
  · have : Schemes μ = {x | 0 ≤ x} ∩ ⋂ θ, {x : A × Θ → ℝ | ∑ a, x (a, θ) = μ θ} := by
      ext x; simp [Schemes]
    rw [this]
    exact (isClosed_le continuous_const continuous_id).inter (isClosed_iInter fun θ =>
      isClosed_eq (continuous_finsetSum _ fun a _ => continuous_apply _) continuous_const)
  · refine (Metric.isBounded_Icc (0 : A × Θ → ℝ) (fun i => μ i.2)).subset fun x hx => ?_
    refine ⟨hx.1, fun i => ?_⟩
    show x i ≤ μ i.2
    rw [← hx.2 i.2]
    exact single_le_sum (f := fun a => x (a, i.2)) (fun a _ => hx.1 (a, i.2)) (mem_univ i.1)

/-- Objective and constraints as continuous linear functionals. -/
noncomputable def objL (v : A → Θ → ℝ) : (A × Θ → ℝ) →L[ℝ] ℝ :=
  ∑ i : A × Θ, v i.1 i.2 • ContinuousLinearMap.proj i

noncomputable def obedL (w : A → Θ → ℝ) (p : A × A) : (A × Θ → ℝ) →L[ℝ] ℝ :=
  ∑ θ, (w p.1 θ - w p.2 θ) • ContinuousLinearMap.proj (p.1, θ)

lemma objL_apply (x : A × Θ → ℝ) : objL v x = obj v x := by
  simp [objL, obj, Fintype.sum_prod_type, mul_comm]

lemma obedL_apply (x : A × Θ → ℝ) (p : A × A) : obedL w p x = obed w x p := by
  simp [obedL, obed, mul_comm]

/-- An optimal obedient scheme exists (the no-information scheme is feasible). -/
theorem exists_optimal (hμ : 0 ≤ μ) :
    ∃ xs ∈ Schemes μ, Obedient w xs ∧ ∀ x ∈ Schemes μ, Obedient w x → obj v x ≤ obj v xs := by
  set F := Schemes μ ∩ {x | Obedient w x}
  have hFc : IsCompact F := (schemes_compact (μ := μ)).inter_right (by
    have : {x | Obedient w x} = ⋂ p, {x : A × Θ → ℝ | 0 ≤ obedL w p x} := by
      ext x; simp [Obedient, obedL_apply]
    rw [this]; exact isClosed_iInter fun p => isClosed_le continuous_const (obedL w p).continuous)
  -- the no-information scheme: always recommend a prior-optimal action
  obtain ⟨a₀, -, ha₀⟩ := exists_max_image univ (fun a => ∑ θ, μ θ * w a θ) univ_nonempty
  set x₀ : A × Θ → ℝ := fun i => if i.1 = a₀ then μ i.2 else 0
  have hx₀ : x₀ ∈ F := by
    refine ⟨⟨fun i => by simp only [x₀]; split_ifs; exacts [hμ i.2, le_rfl], fun θ => by simp [x₀]⟩,
      fun p => ?_⟩
    simp only [obed, x₀]
    split_ifs with h
    · have := ha₀ p.2 (mem_univ _)
      rw [← h] at this
      simp only [mul_sub, sum_sub_distrib]; linarith
    · simp
  obtain ⟨xs, hxs, hmax⟩ := hFc.exists_isMaxOn ⟨x₀, hx₀⟩ (objL v).continuous.continuousOn
  exact ⟨xs, hxs.1, hxs.2, fun x hx hob => by
    have := hmax ⟨hx, hob⟩; simpa [objL_apply] using this⟩

/-- **Strong persuasion duality** (no gap): the value of optimal persuasion equals the
infimum over obedience multipliers `y ≥ 0` of the expected state price `∑ μ θ p_y θ`. -/
theorem strong_duality {xs : A × Θ → ℝ} (hxs : xs ∈ Schemes μ) (hob : Obedient w xs)
    (hopt : ∀ x ∈ Schemes μ, Obedient w x → obj v x ≤ obj v xs) {ε : ℝ} (hε : 0 < ε) :
    ∃ y : A × A → ℝ, 0 ≤ y ∧ dualValue μ v w y ≤ obj v xs + ε := by
  obtain ⟨y, hy, hbound⟩ := Duality.strong_duality (schemes_compact (μ := μ)) (schemes_convex (μ := μ)) (objL v)
    (obedL w) hxs (fun p => by rw [obedL_apply]; exact hob p)
    (fun x hx hg => by
      rw [objL_apply, objL_apply]; exact hopt x hx fun p => by rw [← obedL_apply]; exact hg p) hε
  refine ⟨y, hy, ?_⟩
  -- the scheme recommending, in each state, an action attaining the state price
  choose aθ _ haθ using fun θ : Θ => exists_mem_eq_sup' univ_nonempty (lag v w y · θ)
  set x : A × Θ → ℝ := fun i => if i.1 = aθ i.2 then μ i.2 else 0
  have hx : x ∈ Schemes μ := by
    refine ⟨fun i => ?_, fun θ => by simp [x]⟩
    have hμ : 0 ≤ μ i.2 := hxs.2 i.2 ▸ sum_nonneg fun a _ => hxs.1 (a, i.2)
    simp only [x, Pi.zero_apply]; split_ifs <;> simp [hμ]
  have := hbound x hx
  simp only [objL_apply, obedL_apply] at this
  rw [lagrangian_eq] at this
  convert this using 1
  simp only [dualValue, price, haθ, x]
  refine sum_congr rfl fun θ _ => ?_
  simp [ite_mul]

end Persuasion
