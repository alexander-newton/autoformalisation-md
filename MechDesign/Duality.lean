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

variable [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [DecidableEq J]

/-- **Strong duality (no gap)** for linear programs over a compact convex set. -/
theorem strong_duality {P : Set E} (hPc : IsCompact P) (hPv : Convex ℝ P)
    (c : E →L[ℝ] ℝ) (g : J → E →L[ℝ] ℝ) {xs : E} (hxs : xs ∈ P) (hfeas : ∀ j, 0 ≤ g j xs)
    (hopt : ∀ x ∈ P, (∀ j, 0 ≤ g j x) → c x ≤ c xs) {ε : ℝ} (hε : 0 < ε) :
    ∃ y : J → ℝ, (∀ j, 0 ≤ y j) ∧ ∀ x ∈ P, c x + ∑ j, y j * g j x ≤ c xs + ε := by
  let L : E →L[ℝ] (J → ℝ) × ℝ := (ContinuousLinearMap.pi g).prod c
  have hL : ∀ x, L x = (fun j => g j x, c x) := fun x => rfl
  set K : Set ((J → ℝ) × ℝ) := Iic 0 ×ˢ Iic 0
  set C : Set ((J → ℝ) × ℝ) := L '' P + K with hCdef
  have hCconv : Convex ℝ C :=
    (hPv.linear_image L.toLinearMap).add ((convex_Iic 0).prod (convex_Iic 0))
  have hCcl : IsClosed C :=
    (isClosed_Iic.prod isClosed_Iic).add_left_of_isCompact (hPc.image L.continuous)
  have memC : ∀ x ∈ P, ∀ k : (J → ℝ) × ℝ, k.1 ≤ 0 → k.2 ≤ 0 → L x + k ∈ C :=
    fun x hx k hk1 hk2 => add_mem_add (mem_image_of_mem L hx) ⟨hk1, hk2⟩
  have hpt : ((0 : J → ℝ), c xs + ε) ∉ C := by
    rintro ⟨_, ⟨x, hx, rfl⟩, k, ⟨hk1, hk2⟩, hsum⟩
    rw [hL, Prod.ext_iff] at hsum
    obtain ⟨h1, h2⟩ := hsum
    have hfx : ∀ j, 0 ≤ g j x := fun j => by
      have := congrFun h1 j; have := hk1 j; simp only [Prod.fst_add, Pi.add_apply,
        Pi.zero_apply] at *; linarith
    have := hopt x hx hfx; have : k.2 ≤ 0 := hk2; simp only [Prod.snd_add, Prod.snd_zero] at *; linarith
  obtain ⟨f, u, hfC, hfu⟩ := geometric_hahn_banach_closed_point hCconv hCcl hpt
  -- coordinates of the separating functional
  set lam : J → ℝ := fun j => f (Pi.single j 1, 0)
  set t : ℝ := f (0, 1)
  have hf : ∀ w : (J → ℝ) × ℝ, f w = ∑ j, w.1 j * lam j + w.2 * t := by
    intro w
    have hw : w = ∑ j, w.1 j • ((Pi.single j 1 : J → ℝ), (0 : ℝ)) + w.2 • ((0 : J → ℝ), (1 : ℝ)) := by
      ext i
      · simp [Prod.fst_sum, Finset.sum_apply, Pi.single_apply]
      · simp [Prod.snd_sum]
    conv_lhs => rw [hw]
    rw [map_add, map_sum, map_smul]
    simp only [map_smul, smul_eq_mul, lam, t]
  have hfpt : f ((0 : J → ℝ), c xs + ε) = (c xs + ε) * t := by simp [hf]
  -- `t > 0`, using the point `(0, c xs) ∈ C`
  have ht : 0 < t := by
    have hmem : ((0 : J → ℝ), c xs) ∈ C := by
      have := memC xs hxs (fun j => -g j xs, 0) (fun j => by simpa using hfeas j) le_rfl
      convert this using 1; ext <;> simp [hL]
    have h1 := hfC _ hmem; rw [hf] at h1; simp at h1
    nlinarith
  -- `lam ≥ 0`, by pushing the slack to infinity
  have hlam : ∀ j, 0 ≤ lam j := by
    intro j; by_contra hneg; push Not at hneg
    set K := f (L xs)
    have hK : K < u := hfC _ (by simpa using memC xs hxs 0 le_rfl le_rfl)
    set s := (u - K) / -lam j
    have hs : 0 ≤ s := div_nonneg (by linarith) (by linarith)
    have hk : -(s • (Pi.single j 1 : J → ℝ)) ≤ 0 :=
      fun i => by by_cases h : i = j <;> simp [h, Pi.single_apply, hs]
    have h1 := hfC _ (memC xs hxs (-(s • (Pi.single j 1 : J → ℝ)), (0 : ℝ)) hk le_rfl)
    rw [map_add] at h1
    have : f (-(s • (Pi.single j 1 : J → ℝ)), (0 : ℝ)) = -s * lam j := by
      rw [hf]; simp [Pi.single_apply, lam]
    rw [this] at h1
    have hl : lam j ≠ 0 := hneg.ne
    have : -s * lam j = u - K := by simp only [s]; field_simp
    linarith
  refine ⟨fun j => lam j / t, fun j => div_nonneg (hlam j) ht.le, fun x hx => ?_⟩
  have h1 := hfC _ (by simpa using memC x hx 0 le_rfl le_rfl)
  rw [hf, hL] at h1; simp only at h1
  have key : (c x + ∑ j, lam j / t * g j x) * t < (c xs + ε) * t := by
    rw [add_mul, Finset.sum_mul]
    have : ∑ j, lam j / t * g j x * t = ∑ j, g j x * lam j :=
      Finset.sum_congr rfl fun j _ => by field_simp
    rw [this]; linarith
  exact (lt_of_mul_lt_mul_right key ht.le).le

end Duality
