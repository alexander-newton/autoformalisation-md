/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Algebra.Group.Pointwise

/-!
# Lagrangian strong duality on a compact convex domain

`strong_duality`: maximise a continuous linear objective `c` over a compact convex set `P`
subject to finitely many linear inequalities `g j x ≥ 0`. If `xs` is optimal then, for every
`ε > 0`, there are multipliers `y ≥ 0` with `c x + ∑ y j * g j x ≤ c xs + ε` on all of `P`,
i.e. there is no duality gap. The proof separates the point `(0, c xs + ε)` from the closed
convex set `{(g x - s, c x - r) | x ∈ P, s ≥ 0, r ≥ 0}` (Hahn–Banach).

This is the workhorse behind the linear-programming approach to persuasion
(`MechDesign.Persuasion`).
-/

open Set Pointwise

namespace Duality

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  {J : Type*} [Fintype J]

/-- Weak duality: nonnegative multipliers only increase the objective on feasible points. -/
theorem weak_duality (c : E →L[ℝ] ℝ) (g : J → E →L[ℝ] ℝ) {x : E} (hx : ∀ j, 0 ≤ g j x)
    {y : J → ℝ} (hy : ∀ j, 0 ≤ y j) : c x ≤ c x + ∑ j, y j * g j x :=
  le_add_of_nonneg_right (Finset.sum_nonneg fun j _ => mul_nonneg (hy j) (hx j))

/-- A real `b` with `a + s b < u` for every `s ≥ 0` is nonpositive. -/
lemma nonpos_of_forall_lt {a b u : ℝ} (h : ∀ s : ℝ, 0 ≤ s → a + s * b < u) : b ≤ 0 := by
  by_contra hb; push Not at hb
  have := h ((u - a) / b) (div_nonneg (by linarith [h 0 le_rfl]) hb.le)
  rw [div_mul_cancel₀ _ hb.ne'] at this; linarith


/-- **Strong duality (no gap)** for linear programs over a compact convex set. -/
theorem strong_duality {P : Set E} (hPc : IsCompact P) (hPv : Convex ℝ P)
    (c : E →L[ℝ] ℝ) (g : J → E →L[ℝ] ℝ) {xs : E} (hxs : xs ∈ P) (hfeas : ∀ j, 0 ≤ g j xs)
    (hopt : ∀ x ∈ P, (∀ j, 0 ≤ g j x) → c x ≤ c xs) {ε : ℝ} (hε : 0 < ε) :
    ∃ y : J → ℝ, (∀ j, 0 ≤ y j) ∧ ∀ x ∈ P, c x + ∑ j, y j * g j x ≤ c xs + ε := by
  classical
  -- `C`: the image of `P` in (constraints, objective)-space, closed downwards by `K`
  let L : E →L[ℝ] (J → ℝ) × ℝ := (ContinuousLinearMap.pi g).prod c
  let K : Set ((J → ℝ) × ℝ) := Iic 0 ×ˢ Iic 0
  have memC : ∀ x ∈ P, ∀ k : (J → ℝ) × ℝ, k.1 ≤ 0 → k.2 ≤ 0 → L x + k ∈ L '' P + K :=
    fun x hx k hk₁ hk₂ => add_mem_add (mem_image_of_mem L hx) ⟨hk₁, hk₂⟩
  -- the point `(0, c xs + ε)` lies above `C`, so a hyperplane `f = u` separates them
  have hpt : ((0 : J → ℝ), c xs + ε) ∉ L '' P + K := by
    rintro ⟨_, ⟨x, hx, rfl⟩, k, ⟨hk₁, hk₂⟩, he⟩
    have e₁ := fun j => congrFun (congrArg Prod.fst he) j
    have e₂ := congrArg Prod.snd he
    simp only [mem_Iic] at hk₁ hk₂
    simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, Pi.zero_apply, L,
      ContinuousLinearMap.prod_apply, ContinuousLinearMap.pi_apply] at e₁ e₂
    linarith [hopt x hx fun j => by linarith [e₁ j, show k.1 j ≤ 0 from hk₁ j]]
  obtain ⟨f, u, hC, hu⟩ := geometric_hahn_banach_closed_point
    ((hPv.linear_image L.toLinearMap).add ((convex_Iic 0).prod (convex_Iic 0)))
    ((isClosed_Iic.prod isClosed_Iic).add_left_of_isCompact (hPc.image L.continuous)) hpt
  -- in coordinates, `f (v, r) = ∑ λⱼ vⱼ + t r`
  set lam : J → ℝ := fun j => f (Pi.single j 1, 0)
  set t := f (0, 1)
  have hf : ∀ v r, f (v, r) = ∑ j, lam j * v j + t * r := fun v r => by
    have : ((v, r) : (J → ℝ) × ℝ) = ∑ j, v j • ((Pi.single j 1 : J → ℝ), (0 : ℝ)) + r • (0, 1) := by
      ext <;> simp [Prod.fst_sum, Prod.snd_sum, Finset.sum_apply, Pi.single_apply]
    rw [this, map_add, map_sum, map_smul]
    simp only [map_smul, smul_eq_mul, lam, t, mul_comm]
  -- `f ≤ 0` on `K` (push points of `C` down), so `λ ≥ 0`
  have hK : ∀ k : (J → ℝ) × ℝ, k.1 ≤ 0 → k.2 ≤ 0 → f k ≤ 0 := fun k hk₁ hk₂ =>
    nonpos_of_forall_lt fun s hs => by
      simpa using hC _ (memC xs hxs (s • k) (smul_nonpos_of_nonneg_of_nonpos hs hk₁)
        (smul_nonpos_of_nonneg_of_nonpos hs hk₂))
  have hlam : ∀ j, 0 ≤ lam j := fun j => by
    have := hK (-Pi.single j 1, 0) (fun i => by by_cases h : i = j <;> simp [h]) le_rfl
    rw [hf] at this; simpa [Pi.single_apply] using this
  -- `t > 0`, because `(0, c xs) ∈ C` lies below the point
  have ht : 0 < t := by
    have := hC _ (memC xs hxs (fun j => -g j xs, 0) (fun j => by simpa using hfeas j) le_rfl)
    have hu' := hu; simp only [hf, L, ContinuousLinearMap.prod_apply,
      Prod.mk_add_mk, Pi.add_apply, ContinuousLinearMap.pi_apply, add_neg_cancel, add_zero]
      at this hu'
    simp only [Pi.zero_apply, mul_zero, Finset.sum_const_zero, zero_add] at this hu'
    nlinarith
  -- divide the separation inequality by `t`
  refine ⟨fun j => lam j / t, fun j => div_nonneg (hlam j) ht.le, fun x hx => ?_⟩
  have := hC _ (memC x hx 0 le_rfl le_rfl)
  simp only [add_zero, L, ContinuousLinearMap.prod_apply, ContinuousLinearMap.pi_apply, hf]
    at this hu
  simp only [Pi.zero_apply, mul_zero, Finset.sum_const_zero, zero_add] at hu
  rw [← mul_le_mul_iff_of_pos_right ht, add_mul, Finset.sum_mul]
  simp_rw [div_mul_eq_mul_div, mul_div_assoc, div_self ht.ne', mul_one]
  linarith

end Duality
