/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Myerson (1981): optimal selling to one buyer

A buyer with private value `θ ∈ [a, b]` and quasilinear utility faces a direct mechanism
`(q, t)`. Reporting `θ'` yields `θ q(θ') - t(θ') = U(θ') + (θ - θ') q(θ')`, so incentive
compatibility says exactly that every chord of `U` has slope between the values of `q` at
its endpoints. We call this "`q` supports `U`" and everything follows from three facts about
it:

1. a supporting function is monotone (`Supports.monotoneOn`);
2. a monotone function supports its own integral (`MonotoneOn.supports_integral`);
3. two functions supported by the same `f` differ by a constant (`Supports.sub_eq`).

Hence **Myerson's lemma** (`Mech.IC_iff`) and **revenue equivalence**. One integration by
parts (`integral_primitive_mul`) turns revenue into **virtual surplus**
(`revenue_eq_virtualSurplus`), from which the optimality of posted prices under regularity
(`postedPrice_optimal`) is immediate.
-/

open MeasureTheory Set Filter Topology intervalIntegral Finset
open scoped Interval

namespace Myerson

variable {a b : ℝ} {f V W : ℝ → ℝ} {s : Set ℝ}

/-! ### Supporting functions -/

/-- `f` **supports** `V` on `s`: on every chord `[x, y] ⊆ s` the increment of `V` lies between
the rectangles of height `f x` and `f y`. -/
def Supports (f V : ℝ → ℝ) (s : Set ℝ) : Prop :=
  ∀ x ∈ s, ∀ y ∈ s, x ≤ y → (y - x) * f x ≤ V y - V x ∧ V y - V x ≤ (y - x) * f y

lemma Supports.mono (h : Supports f V s) {t : Set ℝ} (hts : t ⊆ s) : Supports f V t :=
  fun x hx y hy => h x (hts hx) y (hts hy)

/-- A supporting function is monotone. -/
lemma Supports.monotoneOn (h : Supports f V s) : MonotoneOn f s := by
  intro x hx y hy hxy
  rcases hxy.eq_or_lt with rfl | hlt
  · rfl
  obtain ⟨h₁, h₂⟩ := h x hx y hy hxy
  exact le_of_mul_le_mul_left (h₁.trans h₂) (sub_pos.2 hlt)

/-- A monotone function supports its integral. -/
lemma _root_.MonotoneOn.supports_integral (hf : MonotoneOn f (Icc a b)) :
    Supports f (fun x => ∫ t in a..x, f t) (Icc a b) := by
  intro x hx y hy hxy
  have hi : ∀ {u v}, u ∈ Icc a b → v ∈ Icc a b → IntervalIntegrable f volume u v :=
    fun hu hv => (hf.mono (uIcc_subset_Icc hu hv)).intervalIntegrable
  have hs : Icc x y ⊆ Icc a b := Icc_subset_Icc hx.1 hy.2
  simp only [integral_interval_sub_left (hi ⟨le_rfl, hx.1.trans hx.2⟩ hy)
    (hi ⟨le_rfl, hx.1.trans hx.2⟩ hx)]
  constructor
  · simpa [mul_comm] using integral_mono_on hxy intervalIntegrable_const (hi hx hy)
      fun t ht => hf hx (hs ht) ht.1
  · simpa [mul_comm] using integral_mono_on hxy (hi hx hy) intervalIntegrable_const
      fun t ht => hf (hs ht) hy ht.2

/-- **Two functions supported by the same `f` differ by a constant.** On a uniform partition
of `[a, b]` into `n` pieces the difference changes by at most `(f b - f a)(b - a)/n`. -/
lemma Supports.sub_eq (hV : Supports f V (Icc a b)) (hW : Supports f W (Icc a b)) (hab : a ≤ b) :
    V b - V a = W b - W a := by
  set d := fun x => V x - W x
  have hd : ∀ x ∈ Icc a b, ∀ y ∈ Icc a b, x ≤ y → |d y - d x| ≤ (f y - f x) * (y - x) := by
    intro x hx y hy hxy
    obtain ⟨h₁, h₂⟩ := hV x hx y hy hxy; obtain ⟨h₃, h₄⟩ := hW x hx y hy hxy
    rw [abs_le]; constructor <;> nlinarith
  have key : ∀ n : ℕ, 1 ≤ n → |d b - d a| ≤ (f b - f a) * (b - a) / n := by
    intro n hn
    have hn : (0 : ℝ) < n := by exact_mod_cast hn
    set h := (b - a) / n
    have hnh : n * h = b - a := by simp only [h]; field_simp
    have h0 : 0 ≤ h := div_nonneg (by linarith) hn.le
    set p : ℕ → ℝ := fun i => a + i * h
    have hp : ∀ i ≤ n, p i ∈ Icc a b := fun i hi => by
      have : (i : ℝ) * h ≤ n * h := by gcongr
      exact ⟨show a ≤ a + i * h by nlinarith, show a + i * h ≤ b by linarith⟩
    have hpn : p n = b := by simp only [p]; linarith
    calc |d b - d a| = |∑ i ∈ range n, (d (p (i + 1)) - d (p i))| := by
          rw [sum_range_sub (fun i => d (p i)), hpn]; simp [p]
      _ ≤ ∑ i ∈ range n, (f (p (i + 1)) - f (p i)) * h := by
          refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun i hi => ?_)
          have hi := mem_range.1 hi
          convert hd _ (hp i hi.le) _ (hp _ hi) (by simp [p]; linarith) using 2
          simp [p]; ring
      _ = (f b - f a) * (b - a) / n := by
          rw [← sum_mul, sum_range_sub (fun i => f (p i)), hpn]; simp [p, h]; ring
  have := ge_of_tendsto (tendsto_const_div_atTop_nhds_zero_nat _) (eventually_atTop.2 ⟨1, key⟩)
  simp only [d] at this; linarith [abs_nonpos_iff.1 this]

/-! ### Mechanisms -/

/-- A direct mechanism: allocation probability `q` and payment `t`. -/
structure Mech where
  q : ℝ → ℝ
  t : ℝ → ℝ

namespace Mech

variable {m : Mech}

/-- Indirect utility from truth-telling. -/
def U (m : Mech) (θ : ℝ) : ℝ := θ * m.q θ - m.t θ

/-- Incentive compatibility on `[a, b]`. -/
def IC (m : Mech) (a b : ℝ) : Prop :=
  ∀ θ ∈ Icc a b, ∀ θ' ∈ Icc a b, θ * m.q θ' - m.t θ' ≤ m.U θ

/-- Individual rationality on `[a, b]`. -/
def IR (m : Mech) (a b : ℝ) : Prop := ∀ θ ∈ Icc a b, 0 ≤ m.U θ

/-- Incentive compatibility means that the allocation supports the indirect utility. -/
lemma IC_iff_supports : m.IC a b ↔ Supports m.q m.U (Icc a b) := by
  have e : ∀ θ θ', θ * m.q θ' - m.t θ' = m.U θ' + (θ - θ') * m.q θ' := fun _ _ => by
    simp only [U]; ring
  simp only [IC, Supports, e]
  refine ⟨fun h x hx y hy _ => ⟨by linarith [h y hy x hx], by linarith [h x hx y hy]⟩,
    fun h θ hθ θ' hθ' => ?_⟩
  rcases le_total θ' θ with hle | hle
  · linarith [(h θ' hθ' θ hθ hle).1]
  · linarith [(h θ hθ θ' hθ' hle).2]

/-- **Myerson's lemma.** A mechanism is IC iff its allocation is monotone and its indirect
utility obeys the envelope formula. -/
theorem IC_iff : m.IC a b ↔
    MonotoneOn m.q (Icc a b) ∧ ∀ θ ∈ Icc a b, m.U θ = m.U a + ∫ s in a..θ, m.q s := by
  rw [IC_iff_supports]
  refine ⟨fun h => ⟨h.monotoneOn, fun θ hθ => ?_⟩, fun ⟨hq, hU⟩ x hx y hy hxy => ?_⟩
  · have hs : Icc a θ ⊆ Icc a b := Icc_subset_Icc_right hθ.2
    have := (h.mono hs).sub_eq (h.monotoneOn.mono hs).supports_integral hθ.1
    simp only [integral_same] at this; linarith
  · rw [hU x hx, hU y hy, add_sub_add_left_eq_sub]
    exact hq.supports_integral x hx y hy hxy

theorem IC.envelope (h : m.IC a b) {θ : ℝ} (hθ : θ ∈ Icc a b) :
    m.U θ = m.U a + ∫ s in a..θ, m.q s :=
  (IC_iff.1 h).2 θ hθ

theorem IC.monotoneOn (h : m.IC a b) : MonotoneOn m.q (Icc a b) :=
  (IC_iff_supports.1 h).monotoneOn

/-- **Revenue equivalence.** IC mechanisms with the same allocation and the same payment from
the lowest type have the same payments. -/
theorem revenue_equivalence {m₁ m₂ : Mech} (h₁ : m₁.IC a b) (h₂ : m₂.IC a b)
    (hq : EqOn m₁.q m₂.q (Icc a b)) (ht : m₁.t a = m₂.t a) : EqOn m₁.t m₂.t (Icc a b) := by
  intro θ hθ
  have ha : a ∈ Icc a b := ⟨le_rfl, hθ.1.trans hθ.2⟩
  have e₁ := h₁.envelope hθ; have e₂ := h₂.envelope hθ
  rw [integral_congr fun s hs => hq (uIcc_subset_Icc ha hθ hs)] at e₁
  simp only [U, hq hθ, hq ha, ht] at e₁ e₂
  linarith

end Mech

open Mech

/-! ### Revenue and virtual surplus -/

/-- **Integration by parts for primitives:** if `Pᵢ = cᵢ + ∫ₐ hᵢ`, then
`∫ₐᵇ (h₁ P₂ + P₁ h₂) = P₁(b) P₂(b) - P₁(a) P₂(a)`. -/
lemma integral_primitive_mul {h₁ h₂ : ℝ → ℝ} (c₁ c₂ : ℝ) (i₁ : IntervalIntegrable h₁ volume a b)
    (i₂ : IntervalIntegrable h₂ volume a b) :
    ∫ x in a..b, h₁ x * (c₂ + ∫ s in a..x, h₂ s) + (c₁ + ∫ s in a..x, h₁ s) * h₂ x =
      (c₁ + ∫ s in a..b, h₁ s) * (c₂ + ∫ s in a..b, h₂ s) - c₁ * c₂ := by
  have ac : ∀ {h : ℝ → ℝ} (c : ℝ), IntervalIntegrable h volume a b →
      AbsolutelyContinuousOnInterval (fun x => c + ∫ s in a..x, h s) a b := fun c i =>
    (LipschitzOnWith.absolutelyContinuousOnInterval (K := 0)
      (LipschitzWith.const c).lipschitzOnWith).add
      (i.absolutelyContinuousOnInterval_intervalIntegral left_mem_uIcc)
  have := (ac c₁ i₁).integral_deriv_mul_eq_sub (ac c₂ i₂)
  simp only [integral_same, add_zero] at this
  rw [← this]
  refine integral_congr_ae ?_
  filter_upwards [i₁.ae_hasDerivAt_integral, i₂.ae_hasDerivAt_integral] with x d₁ d₂ hx
  have hx := uIoc_subset_uIcc hx
  rw [((d₁ hx a left_mem_uIcc).const_add c₁).deriv, ((d₂ hx a left_mem_uIcc).const_add c₂).deriv]

variable (f) in
/-- Cumulative distribution function of the density `f`. -/
noncomputable def cdf (a θ : ℝ) : ℝ := ∫ s in a..θ, f s

variable (f) in
/-- Virtual surplus density `J = θ f - (1 - F) = φ f`, `φ` the virtual value. -/
noncomputable def J (a θ : ℝ) : ℝ := θ * f θ - (1 - cdf f a θ)

variable (f) in
/-- Expected revenue. -/
noncomputable def revenue (a b : ℝ) (m : Mech) : ℝ := ∫ θ in a..b, m.t θ * f θ

lemma J_eq_virtualValue_mul {θ : ℝ} (hf : f θ ≠ 0) :
    J f a θ = (θ - (1 - cdf f a θ) / f θ) * f θ := by
  simp only [J]; field_simp

lemma J_continuousOn (hab : a ≤ b) (hf : ContinuousOn f (Icc a b)) :
    ContinuousOn (J f a) [[a, b]] := by
  rw [uIcc_of_le hab]
  have hF := continuousOn_primitive_interval' (hf.intervalIntegrable_of_Icc (μ := volume) hab)
    left_mem_uIcc
  exact (continuousOn_id.mul hf).sub (continuousOn_const.sub (uIcc_of_le hab ▸ hF))

variable {m : Mech}

/-- **Revenue = virtual surplus** (Myerson 1981, Lemma 3). For a continuous density `f`
on `[a, b]` and an IC mechanism, `E[t] = ∫ q J - U(a)`. -/
theorem revenue_eq_virtualSurplus (hab : a ≤ b) (hf : ContinuousOn f (Icc a b))
    (hF : ∫ s in a..b, f s = 1) (h : m.IC a b) :
    revenue f a b m = (∫ θ in a..b, m.q θ * J f a θ) - m.U a := by
  have hfi := hf.intervalIntegrable_of_Icc (μ := volume) hab
  have hqi : IntervalIntegrable m.q volume a b := (uIcc_of_le hab ▸ h.monotoneOn).intervalIntegrable
  -- `(F - 1) U` vanishes at `b` and equals `-U a` at `a`
  have ibp := integral_primitive_mul (-1) (m.U a) hfi hqi
  rw [hF, neg_add_cancel, zero_mul, zero_sub, neg_one_mul, neg_neg] at ibp
  have hP : IntervalIntegrable (fun x => f x * (m.U a + ∫ s in a..x, m.q s) +
      (-1 + ∫ s in a..x, f s) * m.q x) volume a b :=
    (hfi.mul_continuousOn (continuousOn_const.add (continuousOn_primitive_interval' hqi
      left_mem_uIcc))).add (hqi.continuousOn_mul (continuousOn_const.add
      (continuousOn_primitive_interval' hfi left_mem_uIcc)))
  rw [← ibp, ← integral_sub (hqi.mul_continuousOn (J_continuousOn hab hf)) hP]
  -- pointwise, `t f = q J - (f U + (F - 1) q)` by the envelope formula
  refine integral_congr fun θ hθ => ?_
  rw [uIcc_of_le hab] at hθ
  rw [← h.envelope hθ]; simp only [J, cdf, U]; ring

/-- **Myerson's revenue bound:** an IC, IR mechanism earns at most `∫ max(J, 0)`. -/
theorem revenue_le (hab : a ≤ b) (hf : ContinuousOn f (Icc a b)) (hF : ∫ s in a..b, f s = 1)
    (h : m.IC a b) (hIR : m.IR a b) (hq : ∀ θ ∈ Icc a b, m.q θ ∈ Icc (0 : ℝ) 1) :
    revenue f a b m ≤ ∫ θ in a..b, max (J f a θ) 0 := by
  have hJ := J_continuousOn hab hf
  rw [revenue_eq_virtualSurplus hab hf hF h]
  have := integral_mono_on hab
    ((uIcc_of_le hab ▸ h.monotoneOn).intervalIntegrable.mul_continuousOn hJ)
    (hJ.sup continuousOn_const).intervalIntegrable (μ := volume) fun θ hθ => by
      obtain ⟨h₀, h₁⟩ := hq θ hθ
      nlinarith [le_max_left (J f a θ) 0, le_max_right (J f a θ) 0]
  linarith [hIR a ⟨le_rfl, hab⟩]

/-- Posted price `p`: sell, at price `p`, iff the value is at least `p`. -/
noncomputable def postedPrice (p : ℝ) : Mech :=
  ⟨fun θ => if p ≤ θ then 1 else 0, fun θ => if p ≤ θ then p else 0⟩

lemma postedPrice_U (p θ : ℝ) : (postedPrice p).U θ = max (θ - p) 0 := by
  simp only [U, postedPrice]; split_ifs <;> simp [*]; linarith

lemma postedPrice_IC (p : ℝ) : (postedPrice p).IC a b := fun θ _ θ' _ => by
  rw [postedPrice_U]; simp only [postedPrice]; split_ifs <;> simp

/-- **Posted prices are optimal under regularity** (Myerson 1981; Riley–Zeckhauser 1983):
if `J` crosses zero once, at `p`, then no IC, IR mechanism beats the posted price `p`. -/
theorem postedPrice_optimal (hab : a ≤ b) (hf : ContinuousOn f (Icc a b))
    (hF : ∫ s in a..b, f s = 1) {p : ℝ} (hp : a ≤ p)
    (hreg : ∀ θ ∈ Icc a b, (θ < p → J f a θ ≤ 0) ∧ (p ≤ θ → 0 ≤ J f a θ))
    (h : m.IC a b) (hIR : m.IR a b) (hq : ∀ θ ∈ Icc a b, m.q θ ∈ Icc (0 : ℝ) 1) :
    revenue f a b m ≤ revenue f a b (postedPrice p) := by
  refine (revenue_le hab hf hF h hIR hq).trans_eq ?_
  rw [revenue_eq_virtualSurplus hab hf hF (postedPrice_IC p), postedPrice_U,
    max_eq_right (by linarith), sub_zero]
  refine integral_congr fun θ hθ => ?_
  rw [uIcc_of_le hab] at hθ
  simp only [postedPrice]
  split_ifs with h'
  · rw [max_eq_left ((hreg θ hθ).2 h'), one_mul]
  · rw [max_eq_right ((hreg θ hθ).1 (not_le.1 h')), zero_mul]

end Myerson
