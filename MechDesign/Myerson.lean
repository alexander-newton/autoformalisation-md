/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm

/-!
# Myerson (1981): optimal mechanisms with one agent and a continuum of types

A single buyer has private value `θ ∈ [a, b]` and quasilinear utility `θ q - t`.
A direct mechanism is a pair `(q, t)` of an allocation probability and a payment.

* `IC_iff` — **Myerson's lemma**: a mechanism is incentive compatible iff `q` is nondecreasing
  and the indirect utility satisfies the envelope formula `U θ = U a + ∫_a^θ q`.
* `revenue_equivalence` — two IC mechanisms with the same allocation and the same payment of
  the lowest type have identical payments.
* `revenue_eq_virtualSurplus` — expected revenue equals expected *virtual surplus*
  `∫ q J - U a` with `J θ = θ f θ - (1 - F θ)` (that is, `J = φ f` for the virtual value
  `φ θ = θ - (1 - F θ) / f θ`; see `J_eq_virtualValue_mul`).
* `revenue_le` / `postedPrice_optimal` — every IC, IR mechanism earns at most `∫ max(J, 0)`, and
  under regularity (single crossing of `J` at `p`) the posted price `p` attains this bound
  (Myerson 1981; Riley–Zeckhauser 1983).
-/

open MeasureTheory Set intervalIntegral

namespace Myerson

/-- A direct mechanism for a single agent: allocation `q` and payment `t` as functions of the
reported type. -/
structure Mech where
  q : ℝ → ℝ
  t : ℝ → ℝ

variable (m : Mech) (a b : ℝ)

/-- Utility of a type-`θ` agent reporting `θ'`. -/
def util (θ θ' : ℝ) : ℝ := θ * m.q θ' - m.t θ'

/-- Indirect utility (truth-telling). -/
def U (θ : ℝ) : ℝ := m.util θ θ

/-- Incentive compatibility on the type space `[a, b]`. -/
def IC : Prop := ∀ θ ∈ Icc a b, ∀ θ' ∈ Icc a b, m.util θ θ' ≤ m.U θ

/-- Individual rationality on `[a, b]`. -/
def IR : Prop := ∀ θ ∈ Icc a b, 0 ≤ m.U θ

variable {m a b}

lemma util_eq (θ θ' : ℝ) : m.util θ θ' = m.U θ' + (θ - θ') * m.q θ' := by
  simp only [util, U]; ring

/-- IC sandwiches utility differences between allocations. -/
lemma IC.sandwich (h : m.IC a b) {θ θ'} (hθ : θ ∈ Icc a b) (hθ' : θ' ∈ Icc a b) :
    (θ' - θ) * m.q θ ≤ m.U θ' - m.U θ ∧ m.U θ' - m.U θ ≤ (θ' - θ) * m.q θ' := by
  have h1 := h θ' hθ' θ hθ; have h2 := h θ hθ θ' hθ'
  rw [util_eq] at h1 h2
  constructor <;> linarith

/-- IC implies a monotone allocation rule. -/
lemma IC.monotoneOn (h : m.IC a b) : MonotoneOn m.q (Icc a b) := by
  intro θ hθ θ' hθ' hle
  obtain ⟨h1, h2⟩ := h.sandwich hθ hθ'
  rcases hle.lt_or_eq with hlt | rfl
  · have : 0 < θ' - θ := sub_pos.2 hlt
    have := le_trans h1 h2
    exact le_of_mul_le_mul_left this (by linarith)
  · exact le_rfl

/-! ### A Riemann-sum lemma: sandwiched increments integrate a monotone function -/

/-- If `f` is monotone and the increments of `V` are sandwiched between lower and upper
rectangles of `f`, then `V b - V a = ∫_a^b f`.  (Proof: uniform partitions; the error is
at most `(f b - f a) (b - a) / n` for every `n`.) -/
theorem sub_eq_integral_of_sandwich {f V : ℝ → ℝ} (hab : a ≤ b) (hf : MonotoneOn f (Icc a b))
    (hV : ∀ x ∈ Icc a b, ∀ y ∈ Icc a b, x ≤ y →
      (y - x) * f x ≤ V y - V x ∧ V y - V x ≤ (y - x) * f y) :
    V b - V a = ∫ x in a..b, f x := by
  have hint : ∀ x ∈ Icc a b, ∀ y ∈ Icc a b, IntervalIntegrable f volume x y := fun x hx y hy =>
    (hf.mono (uIcc_subset_Icc hx hy)).intervalIntegrable
  -- the defect on a subinterval
  set D : ℝ → ℝ → ℝ := fun x y => V y - V x - ∫ t in x..y, f t with hD
  have hloc : ∀ x ∈ Icc a b, ∀ y ∈ Icc a b, x ≤ y → |D x y| ≤ (f y - f x) * (y - x) := by
    intro x hx y hy hxy
    have hsub : Icc x y ⊆ Icc a b := Icc_subset_Icc hx.1 hy.2
    have i1 : (y - x) * f x ≤ ∫ t in x..y, f t := by
      have := integral_mono_on hxy intervalIntegrable_const (hint x hx y hy)
        (fun t ht => hf hx (hsub ht) ht.1)
      simpa [mul_comm] using this
    have i2 : ∫ t in x..y, f t ≤ (y - x) * f y := by
      have := integral_mono_on hxy (hint x hx y hy) intervalIntegrable_const
        (fun t ht => hf (hsub ht) hy ht.2)
      simpa [mul_comm] using this
    obtain ⟨v1, v2⟩ := hV x hx y hy hxy
    rw [abs_le]; constructor <;> simp only [hD] <;> nlinarith
  have hfab : f a ≤ f b := hf ⟨le_rfl, hab⟩ ⟨hab, le_rfl⟩ hab
  -- for every `n`, the total defect is small
  have key : ∀ n : ℕ, 0 < n → |D a b| ≤ (f b - f a) * (b - a) / n := by
    intro n hn
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    set p : ℕ → ℝ := fun i => a + i * ((b - a) / n) with hp
    have hp0 : p 0 = a := by simp [hp]
    have hpn : p n = b := by simp [hp]; field_simp; ring
    have hmem : ∀ i ≤ n, p i ∈ Icc a b := by
      intro i hi
      have hi' : (i : ℝ) ≤ n := by exact_mod_cast hi
      have hd : 0 ≤ (b - a) / n := div_nonneg (by linarith) hn'.le
      refine ⟨by simp only [hp]; nlinarith [(Nat.cast_nonneg i : (0 : ℝ) ≤ i)], ?_⟩
      calc p i ≤ a + n * ((b - a) / n) := by simp only [hp]; nlinarith
        _ = b := by field_simp; ring
    have hstep : ∀ i, p (i + 1) - p i = (b - a) / n := by intro i; simp [hp]; ring
    have hmono : ∀ i, p i ≤ p (i + 1) := fun i => by
      have := hstep i; have : 0 ≤ (b - a) / n := div_nonneg (by linarith) hn'.le; linarith
    have hsplit : D a b = ∑ i ∈ Finset.range n, D (p i) (p (i + 1)) := by
      simp only [hD, Finset.sum_sub_distrib, Finset.sum_range_sub (fun i => V (p i))]
      rw [sum_integral_adjacent_intervals (fun k hk => hint _ (hmem k hk.le) _ (hmem _ hk)),
        hp0, hpn]
    calc |D a b| ≤ ∑ i ∈ Finset.range n, |D (p i) (p (i + 1))| := by
          rw [hsplit]; exact Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i ∈ Finset.range n, (f (p (i + 1)) - f (p i)) * ((b - a) / n) := by
          refine Finset.sum_le_sum fun i hi => ?_
          have hi := Finset.mem_range.1 hi
          rw [← hstep i]
          exact hloc _ (hmem i hi.le) _ (hmem _ hi) (hmono i)
      _ = (f b - f a) * (b - a) / n := by
          rw [← Finset.sum_mul, Finset.sum_range_sub (fun i => f (p i)), hpn, hp0]; ring
  -- hence the defect vanishes
  have hC : 0 ≤ (f b - f a) * (b - a) := mul_nonneg (by linarith) (by linarith)
  have : D a b = 0 := by
    by_contra hne
    have hpos : 0 < |D a b| := abs_pos.2 hne
    obtain ⟨n, hn⟩ := exists_nat_gt ((f b - f a) * (b - a) / |D a b|)
    have hn0 : 0 < n := by
      have : (0 : ℝ) < n := lt_of_le_of_lt (div_nonneg hC hpos.le) hn
      exact_mod_cast this
    have h1 := key n hn0
    have : (f b - f a) * (b - a) / n < |D a b| := by
      rw [div_lt_iff₀ (by exact_mod_cast hn0)]
      rw [div_lt_iff₀ hpos] at hn; linarith
    linarith
  simp only [hD] at this; linarith

/-! ### Myerson's lemma -/

/-- **Myerson's lemma (envelope formula).** -/
theorem IC.envelope (h : m.IC a b) {θ : ℝ} (hθ : θ ∈ Icc a b) :
    m.U θ = m.U a + ∫ s in a..θ, m.q s := by
  have haθ : Icc a θ ⊆ Icc a b := Icc_subset_Icc le_rfl hθ.2
  have := sub_eq_integral_of_sandwich (V := m.U) hθ.1 (h.monotoneOn.mono haθ)
    (fun x hx y hy _ => h.sandwich (haθ hx) (haθ hy))
  linarith

/-- **Myerson's lemma.** A direct mechanism is IC iff the allocation is monotone and the
indirect utility is given by the envelope formula. -/
theorem IC_iff (hab : a ≤ b) :
    m.IC a b ↔ MonotoneOn m.q (Icc a b) ∧ ∀ θ ∈ Icc a b, m.U θ = m.U a + ∫ s in a..θ, m.q s := by
  refine ⟨fun h => ⟨h.monotoneOn, fun θ hθ => h.envelope hθ⟩, fun ⟨hmono, henv⟩ => ?_⟩
  intro θ hθ θ' hθ'
  have ha : a ∈ Icc a b := ⟨le_rfl, hab⟩
  have hint : ∀ x ∈ Icc a b, ∀ y ∈ Icc a b, IntervalIntegrable m.q volume x y :=
    fun x hx y hy => (hmono.mono (uIcc_subset_Icc hx hy)).intervalIntegrable
  have hdiff : m.U θ - m.U θ' = ∫ s in θ'..θ, m.q s := by
    rw [henv θ hθ, henv θ' hθ', ← integral_interval_sub_left (hint a ha θ hθ)
      (hint a ha θ' hθ')]; ring
  rw [util_eq]
  rcases le_total θ' θ with hle | hle
  · have : (θ - θ') * m.q θ' ≤ ∫ s in θ'..θ, m.q s := by
      have := integral_mono_on hle intervalIntegrable_const (hint θ' hθ' θ hθ)
        (fun s hs => hmono hθ' ⟨hθ'.1.trans hs.1, hs.2.trans hθ.2⟩ hs.1)
      simpa [mul_comm] using this
    linarith
  · have : ∫ s in θ..θ', m.q s ≤ (θ' - θ) * m.q θ' := by
      have := integral_mono_on hle (hint θ hθ θ' hθ') intervalIntegrable_const
        (fun s hs => hmono ⟨hθ.1.trans hs.1, hs.2.trans hθ'.2⟩ hθ' hs.2)
      simpa [mul_comm] using this
    rw [integral_symm] at hdiff
    linarith

/-- **Revenue equivalence.** IC mechanisms with the same allocation rule and the same payment
from the lowest type collect the same payment from every type. -/
theorem revenue_equivalence {m₁ m₂ : Mech} (h₁ : m₁.IC a b) (h₂ : m₂.IC a b) (hab : a ≤ b)
    (hq : ∀ θ ∈ Icc a b, m₁.q θ = m₂.q θ) (ht : m₁.t a = m₂.t a) :
    ∀ θ ∈ Icc a b, m₁.t θ = m₂.t θ := by
  intro θ hθ
  have ha : a ∈ Icc a b := ⟨le_rfl, hab⟩
  have e₁ := h₁.envelope hθ; have e₂ := h₂.envelope hθ
  have hi : ∫ s in a..θ, m₁.q s = ∫ s in a..θ, m₂.q s :=
    integral_congr fun s hs => hq s (uIcc_subset_Icc ha hθ hs)
  simp only [U, util] at e₁ e₂
  rw [hq a ha, ht, hi, hq θ hθ] at e₁
  linarith

/-! ### Revenue and virtual surplus -/

variable (f : ℝ → ℝ)

/-- Cumulative distribution function of the density `f` on `[a, b]`. -/
noncomputable def cdf (θ : ℝ) : ℝ := ∫ s in a..θ, f s

/-- Virtual surplus density `J θ = θ f θ - (1 - F θ)`, i.e. `φ(θ) f(θ)`. -/
noncomputable def J (θ : ℝ) : ℝ := θ * f θ - (1 - cdf a f θ)

/-- Expected revenue of a mechanism. -/
noncomputable def revenue (m : Mech) : ℝ := ∫ θ in a..b, m.t θ * f θ

lemma J_eq_virtualValue_mul {θ : ℝ} (hf : f θ ≠ 0) :
    J a f θ = (θ - (1 - cdf a f θ) / f θ) * f θ := by
  simp only [J]; field_simp

variable {f}

/-- **Revenue = expected virtual surplus** (Myerson 1981, Lemma 3). For a continuous density
`f` on `[a, b]` and any IC mechanism, `E[t] = ∫ q J - U a`. -/
theorem revenue_eq_virtualSurplus (hab : a ≤ b) (hf : ContinuousOn f (Icc a b))
    (hF : ∫ s in a..b, f s = 1) (h : m.IC a b) :
    revenue a b f m = (∫ θ in a..b, m.q θ * J a f θ) - m.U a := by
  have hu : uIcc a b = Icc a b := uIcc_of_le hab
  have ha : a ∈ uIcc a b := left_mem_uIcc
  have hfi : IntervalIntegrable f volume a b := (hu ▸ hf).intervalIntegrable
  have hqi : IntervalIntegrable m.q volume a b := (hu ▸ h.monotoneOn).intervalIntegrable
  set G : ℝ → ℝ := fun θ => ∫ s in a..θ, m.q s with hG
  set F : ℝ → ℝ := fun θ => cdf a f θ - 1 with hFdef
  have hGac : AbsolutelyContinuousOnInterval G a b :=
    hqi.absolutelyContinuousOnInterval_intervalIntegral ha
  have hFac : AbsolutelyContinuousOnInterval F a b :=
    (hfi.absolutelyContinuousOnInterval_intervalIntegral ha).sub
      (LipschitzOnWith.absolutelyContinuousOnInterval (K := 0) (LipschitzWith.const 1).lipschitzOnWith)
  -- payments in terms of `G`
  have ht : ∀ θ ∈ Icc a b, m.t θ = θ * m.q θ - m.U a - G θ := by
    intro θ hθ; have := h.envelope hθ; simp only [U, util] at this ⊢; rw [hG]; linarith
  -- integration by parts: ∫ G f = ∫ q (1 - F)
  have hGc : ContinuousOn G (uIcc a b) := hGac.continuousOn
  have hFc : ContinuousOn F (uIcc a b) := hFac.continuousOn
  have dG : ∀ᵐ x, x ∈ Ι a b → deriv G x = m.q x := by
    filter_upwards [hqi.ae_hasDerivAt_integral] with x hx hxI
    exact (hx (uIoc_subset_uIcc hxI) a ha).deriv
  have dF : ∀ᵐ x, x ∈ Ι a b → deriv F x = f x := by
    filter_upwards [hfi.ae_hasDerivAt_integral] with x hx hxI
    exact ((hx (uIoc_subset_uIcc hxI) a ha).sub_const 1).deriv
  have ibp := hGac.integral_mul_deriv_eq_deriv_mul hFac
  have hGa : G a = 0 := by simp [hG]
  have hFb : F b = 0 := by simp [hFdef, cdf, hF]
  rw [hGa, hFb, integral_congr_ae (dF.mono fun x hx hxI => by rw [hx hxI]),
    integral_congr_ae (dG.mono fun x hx hxI => by rw [hx hxI])] at ibp
  simp only [zero_mul, mul_zero, sub_zero, zero_sub] at ibp
  -- assemble
  have hθqf : IntervalIntegrable (fun θ => θ * m.q θ * f θ) volume a b := by
    have := hqi.mul_continuousOn (g := fun θ => θ * f θ) (continuousOn_id.mul (hu ▸ hf))
    refine this.congr (Filter.Eventually.of_forall fun θ => ?_); simp only; ring
  have hGf : IntervalIntegrable (fun θ => G θ * f θ) volume a b :=
    hfi.continuousOn_mul hGc
  have hqF : IntervalIntegrable (fun θ => m.q θ * F θ) volume a b := hqi.mul_continuousOn hFc
  unfold revenue
  rw [integral_congr (g := fun θ => θ * m.q θ * f θ - m.U a * f θ - G θ * f θ)
    (fun θ hθ => by simp only; rw [ht θ (hu ▸ hθ)]; ring)]
  rw [integral_sub (hθqf.sub (hfi.const_mul _)) hGf, integral_sub hθqf (hfi.const_mul _),
    integral_const_mul, hF, ibp]
  rw [integral_congr (g := fun θ => θ * m.q θ * f θ + m.q θ * F θ)
    (fun θ _ => by simp only [J, hFdef]; ring), integral_add hθqf hqF]
  ring

/-- **Myerson's revenue bound.** Every IC and IR mechanism with allocation probabilities in
`[0, 1]` earns at most the expected positive part of the virtual surplus. -/
theorem revenue_le (hab : a ≤ b) (hf : ContinuousOn f (Icc a b)) (hF : ∫ s in a..b, f s = 1)
    (h : m.IC a b) (hIR : m.IR a b) (hq : ∀ θ ∈ Icc a b, m.q θ ∈ Icc (0 : ℝ) 1) :
    revenue a b f m ≤ ∫ θ in a..b, max (J a f θ) 0 := by
  have hu : uIcc a b = Icc a b := uIcc_of_le hab
  have hJc : ContinuousOn (J a f) (Icc a b) := by
    have hFc : ContinuousOn (cdf a f) (Icc a b) :=
      hu ▸ (((hu ▸ hf).intervalIntegrable).absolutelyContinuousOnInterval_intervalIntegral
        left_mem_uIcc).continuousOn
    exact (continuousOn_id.mul hf).sub (continuousOn_const.sub hFc)
  rw [revenue_eq_virtualSurplus hab hf hF h]
  have hUa := hIR a ⟨le_rfl, hab⟩
  have : ∫ θ in a..b, m.q θ * J a f θ ≤ ∫ θ in a..b, max (J a f θ) 0 := by
    refine integral_mono_on hab ?_ ?_ fun θ hθ => ?_
    · exact (hu ▸ h.monotoneOn).intervalIntegrable.mul_continuousOn (hu ▸ hJc)
    · exact (hJc.max continuousOn_const).intervalIntegrable_of_Icc hab
    · obtain ⟨h0, h1⟩ := hq θ hθ
      rcases le_total 0 (J a f θ) with hJ | hJ
      · rw [max_eq_left hJ]; nlinarith
      · rw [max_eq_right hJ]; nlinarith
  linarith

/-- The posted-price mechanism at price `p`: sell iff the value is at least `p`. -/
noncomputable def postedPrice (p : ℝ) : Mech :=
  ⟨fun θ => if p ≤ θ then 1 else 0, fun θ => if p ≤ θ then p else 0⟩

lemma postedPrice_U (p θ : ℝ) : (postedPrice p).U θ = max (θ - p) 0 := by
  simp only [U, util, postedPrice]
  split_ifs with h
  · rw [max_eq_left (by linarith)]; ring
  · rw [max_eq_right (by linarith)]; ring

lemma postedPrice_IC (p : ℝ) : (postedPrice p).IC a b := by
  intro θ _ θ' _
  rw [postedPrice_U]
  simp only [util, postedPrice]
  split_ifs
  · simp
  · simp

/-- **Optimality of posted prices (Myerson 1981; Riley–Zeckhauser 1983).** If the virtual
surplus `J` single-crosses zero at `p` (regularity), the posted price `p` maximises revenue
among all IC and IR mechanisms. -/
theorem postedPrice_optimal (hab : a ≤ b) (hf : ContinuousOn f (Icc a b))
    (hF : ∫ s in a..b, f s = 1) {p : ℝ} (hp : p ∈ Icc a b)
    (hreg : ∀ θ ∈ Icc a b, (θ < p → J a f θ ≤ 0) ∧ (p ≤ θ → 0 ≤ J a f θ))
    (h : m.IC a b) (hIR : m.IR a b) (hq : ∀ θ ∈ Icc a b, m.q θ ∈ Icc (0 : ℝ) 1) :
    revenue a b f m ≤ revenue a b f (postedPrice p) := by
  refine (revenue_le hab hf hF h hIR hq).trans (le_of_eq ?_)
  rw [revenue_eq_virtualSurplus hab hf hF (postedPrice_IC p), postedPrice_U,
    max_eq_right (by linarith [hp.1]), sub_zero]
  refine integral_congr fun θ hθ => ?_
  rw [uIcc_of_le hab] at hθ
  simp only [postedPrice]
  split_ifs with h'
  · rw [max_eq_left ((hreg θ hθ).2 h'), one_mul]
  · rw [max_eq_right ((hreg θ hθ).1 (not_le.1 h')), zero_mul]

end Myerson
