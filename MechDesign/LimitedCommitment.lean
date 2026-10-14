/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import MechDesign.DovalSkreta

/-!
# Limited commitment over many periods (Doval–Skreta 2022)

Over `T` periods a principal, who cannot commit to future mechanisms, offers a mechanism in
each period; the agent, with a persistent private type, plays it; the principal sees the public
outcome and updates her belief. The agent can always walk away: every mechanism has an exit
message that yields the outside allocation `x₀` for sure in that period. We work with
*belief-based* (Markov) assessments: what happens from period `t` on depends only on the
principal's current belief. Values at period `T` are arbitrary terminal values.

An assessment assigns to each period and belief a play of an arbitrary finite mechanism. It is
an **equilibrium** (`IsEquilibrium`) if, at every period and belief, the agent best-responds
given the continuation values, the values are those the play generates, and the principal is
**sequentially rational**: no other mechanism offering exit, with any best-responding agent,
does better.

**Theorem** (`canonical_isEquilibrium`): replacing every play by its canonical version, which
asks for the type (or exit) and announces the posterior, is again an equilibrium with the same
values, in which the agent reports truthfully (`canonical_truthful`) and announced beliefs are
self-consistent (`DovalSkreta.Play.toCanonical_post`). The proof is the one-shot revelation
step of `DovalSkreta.lean`, applied period by period: relabelling changes no value, so the
principal faces the same deviations as before.
-/

open Finset

namespace DovalSkreta

variable {Θ X : Type} [Fintype Θ]

/-- Flow payoffs of the agent and the principal, and the outside allocation. -/
structure Env (Θ X : Type) where
  uA : Θ → X → ℝ
  uP : Θ → X → ℝ
  x₀ : X

/-- A play of some finite mechanism: input messages `M` with a designated exit message,
public outcomes `O`. -/
structure AnyPlay (Θ X : Type) where
  M : Type
  O : Type
  [fM : Fintype M]
  [fO : Fintype O]
  optOut : M
  play : Play Θ M O X

attribute [instance] AnyPlay.fM AnyPlay.fO

/-- **Participation**: the exit message surely yields the outside allocation. -/
def AnyPlay.OffersExit (E : Env Θ X) (Q : AnyPlay Θ X) : Prop :=
  ∀ o, 0 < Q.play.ζ Q.optOut o → Q.play.alloc o = E.x₀

namespace Play

variable {M O : Type} [Fintype M] [Fintype O] (E : Env Θ X) (P : Play Θ M O X)

/-- The agent's continuation-inclusive utility: flow now, `W` from the posterior on. -/
def agentU (W : Θ → (Θ → ℝ) → ℝ) : Θ → X → (Θ → ℝ) → ℝ := fun θ x β => E.uA θ x + W θ β

/-- The agent best-responds to the continuation values `W`. -/
def BestResponds (W : Θ → (Θ → ℝ) → ℝ) : Prop :=
  ∀ θ m, 0 < P.σ θ m → ∀ m', P.payoff (agentU E W) θ m' ≤ P.payoff (agentU E W) θ m

/-- Type `θ`'s value from the play, given continuation values `W`. -/
noncomputable def agentValue (W : Θ → (Θ → ℝ) → ℝ) (θ : Θ) : ℝ :=
  ∑ o, P.outProb θ o * (E.uA θ (P.alloc o) + W θ (P.post o))

/-- The principal's value from the play, given continuation values `V`. -/
noncomputable def principalValue (V : (Θ → ℝ) → ℝ) : ℝ :=
  ∑ θ, P.μ θ * ∑ o, P.outProb θ o * (E.uP θ (P.alloc o) + V (P.post o))

variable {E P} {m₀ : M}

/-- Values are unchanged by the canonical relabelling. -/
lemma toCanonical_agentValue (hP : P.Valid) (W : Θ → (Θ → ℝ) → ℝ) (θ : Θ) :
    (P.toCanonical m₀).agentValue E W θ = P.agentValue E W θ :=
  toCanonical_outcome_eq hP θ fun x β => E.uA θ x + W θ β

lemma toCanonical_principalValue (hP : P.Valid) (V : (Θ → ℝ) → ℝ) :
    (P.toCanonical m₀).principalValue E V = P.principalValue E V :=
  sum_congr rfl fun θ _ => by
    rw [show (P.toCanonical m₀).μ θ = P.μ θ from rfl,
      toCanonical_outcome_eq hP θ fun x β => E.uP θ x + V β]

/-- The canonical play is a best response: only the truthful report is ever sent, and it is
optimal. -/
lemma toCanonical_bestResponds (hP : P.Valid) {W : Θ → (Θ → ℝ) → ℝ}
    (hbr : P.BestResponds E W) : (P.toCanonical m₀).BestResponds E W := by
  intro θ r hr r'
  have : r = some θ := by
    cases r with
    | none => simp [toCanonical] at hr
    | some θ' =>
      simp only [toCanonical, Option.elim] at hr
      split_ifs at hr with h
      exacts [h ▸ rfl, (lt_irrefl _ hr).elim]
  subst this
  exact toCanonical_IC hP (agentU E W) hbr θ r'

end Play

/-- An assessment: for each period and belief of the principal, a play of some mechanism. -/
def Assessment (Θ X : Type) := ℕ → (Θ → ℝ) → AnyPlay Θ X

variable (E : Env Θ X) (T : ℕ)

/-- **A belief-based equilibrium** with principal values `V t β` and agent values `W t θ β`:
at every period `t < T` and belief `β`, the play starts from `β`, is valid, offers exit, the
agent best-responds, the values are those the play generates, and the principal is sequentially
rational: no valid play of any mechanism offering exit, with a best-responding agent, does
better. -/
def IsEquilibrium (A : Assessment Θ X) (V : ℕ → (Θ → ℝ) → ℝ) (W : ℕ → Θ → (Θ → ℝ) → ℝ) :
    Prop :=
  ∀ t < T, ∀ β, IsDist β →
    (A t β).play.μ = β ∧ (A t β).play.Valid ∧ (A t β).OffersExit E ∧
    (A t β).play.BestResponds E (W (t + 1)) ∧
    V t β = (A t β).play.principalValue E (V (t + 1)) ∧
    (∀ θ, W t θ β = (A t β).play.agentValue E (W (t + 1)) θ) ∧
    ∀ Q : AnyPlay Θ X, Q.play.μ = β → Q.play.Valid → Q.OffersExit E →
      Q.play.BestResponds E (W (t + 1)) → Q.play.principalValue E (V (t + 1)) ≤ V t β

/-- The canonical version of an assessment: in every period and belief, the canonical play,
whose exit relabels the original exit. -/
noncomputable def Assessment.canonical (A : Assessment Θ X) : Assessment Θ X :=
  fun t β =>
    { M := Option Θ
      O := (A t β).play.outputs
      optOut := none
      play := (A t β).play.toCanonical (A t β).optOut }

variable {E T}

/-- **Canonical mechanisms are without loss under limited commitment** (Doval–Skreta 2022,
Theorem 1, for belief-based assessments): the canonical version of an equilibrium is an
equilibrium with the same values. -/
theorem canonical_isEquilibrium {A : Assessment Θ X} {V : ℕ → (Θ → ℝ) → ℝ}
    {W : ℕ → Θ → (Θ → ℝ) → ℝ} (h : IsEquilibrium E T A V W) :
    IsEquilibrium E T A.canonical V W := by
  intro t ht β hβ
  obtain ⟨hμ, hP, hx, hbr, hV, hW, hseq⟩ := h t ht β hβ
  -- relabelling preserves validity, exit, best responses and every value; the principal's
  -- deviations are the same as before, so she is still sequentially rational
  refine ⟨hμ, Play.toCanonical_valid hP, Play.toCanonical_exit hx,
    Play.toCanonical_bestResponds hP hbr, ?_, fun θ => ?_, hseq⟩
  · rw [hV]; exact (Play.toCanonical_principalValue hP _).symm
  · rw [hW θ]; exact (Play.toCanonical_agentValue hP _ θ).symm

/-- In the canonical assessment the agent reports truthfully. -/
theorem canonical_truthful (A : Assessment Θ X) (t : ℕ) (β : Θ → ℝ) (θ : Θ) :
    (A.canonical t β).play.σ θ (some θ) = 1 := by
  simp [Assessment.canonical, Play.toCanonical]

end DovalSkreta
