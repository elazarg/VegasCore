/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheoryExtensions.Protocol.FiniteInformation

/-! # Structural action restrictions between execution protocols

A restriction embeds histories, local information and legal choices. Its only
execution law is a commuting square for one actual step under a pure local
joint choice. Beliefs, equilibria and complete-run laws are not fields.
The complete-run correspondence is derived from this local square.
-/

noncomputable section

namespace GameTheory.Protocol.InformationModel

open GameTheory.Math.Probability ExecutionProtocol

variable {Player : Type} {E T : ExecutionProtocol Player}
  (M : InformationModel E) (N : InformationModel T)

/-- One actual execution step with the given local choices. Terminal histories
are absorbed exactly as in the ordinary protocol evaluator. -/
def localStep (history : E.History)
    (choices : ∀ who, M.Choice who (M.infoOf who history.trace)) : PMF E.History := by
  classical
  exact if stopped : E.terminal history.state then PMF.pure history else
    (E.step history.state ⟨fun who => (choices who).1,
      E.legal_of_legalOption stopped (fun who =>
        (M.menu_adequate who history.trace (choices who).1).mp (choices who).2)⟩).bindOnSupport
      (fun _ realized => PMF.pure (history.extend _ realized))

theorem runBehavioralFrom_succ_localStep [Fintype Player]
    (profile : ∀ who, M.BehavioralPolicy who) (fuel : Nat) (history : E.History) :
    M.runBehavioralFrom profile (fuel + 1) history =
      ((independentProduct fun who => profile who (M.infoOf who history.trace)).bind
        (M.localStep history)).bind (M.runBehavioralFrom profile fuel) := by
  classical
  by_cases stopped : E.terminal history.state
  · have one : M.localStep history = fun _ => PMF.pure history := by
      funext choices
      simp only [localStep, dite_eq_left stopped]
    rw [one, PMF.bind_const, PMF.pure_bind,
      M.runBehavioralFrom_of_terminal profile _ stopped,
      M.runBehavioralFrom_of_terminal profile _ stopped]
  · rw [M.runBehavioralFrom_succ_of_not_terminal profile fuel stopped]
    simp only [behavioralJoint, PMF.bind_map, localStep, dite_eq_right stopped,
      PMF.bind_bind, bindOnSupport_bind, PMF.pure_bind]

/-- A genuine local action restriction. Compliant information is preserved
injectively; target information fibers may additionally contain new histories.
No global execution or belief correspondence is assumed. -/
structure ActionRestriction where
  history : E.History ↪ T.History
  information : ∀ who, M.InfoState who ↪ N.InfoState who
  choice : ∀ who info, M.Choice who info ↪ N.Choice who (information who info)
  initial : history E.initHistory = T.initHistory
  length : ∀ original, (history original).trace.length = original.trace.length
  terminal : ∀ original, T.terminal (history original).state ↔ E.terminal original.state
  active : ∀ original who, T.active (history original).state who ↔ E.active original.state who
  observed : ∀ who original,
    N.infoOf who (history original).trace = information who (M.infoOf who original.trace)
  step : ∀ original (choices : ∀ who, M.Choice who (M.infoOf who original.trace)),
    (M.localStep original choices).map history =
      N.localStep (history original) (fun who =>
        Eq.mp (congrArg (N.Choice who) (observed who original).symm)
          (choice who (M.infoOf who original.trace) (choices who)))

namespace ActionRestriction

variable {M N} (restriction : M.ActionRestriction N)

universe v

private theorem transport_injective {α β : Type v} (same : α = β) :
    Function.Injective (fun value : α => Eq.mp same value) := by
  subst β
  exact fun _ _ equal => equal

private theorem map_transport {Index : Type*} {Value : Index → Type*}
    (laws : ∀ index, PMF (Value index)) {first second : Index} (same : first = second) :
    (laws first).map (fun value => Eq.mp (congrArg Value same) value) = laws second := by
  subst second
  exact PMF.map_id _

/-- Embed a local source choice at a concrete history, transporting its target
information index along the observation square. -/
def choiceAt (who : Player) (original : E.History) :
    M.Choice who (M.infoOf who original.trace) ↪
      N.Choice who (N.infoOf who (restriction.history original).trace) where
  toFun action := Eq.mp (congrArg (N.Choice who) (restriction.observed who original).symm)
    (restriction.choice who (M.infoOf who original.trace) action)
  inj' := by
    intro first second equal
    apply (restriction.choice who (M.infoOf who original.trace)).injective
    exact transport_injective _ equal

/-- A source decision remains a target decision at the embedded information
value. This uses activity and the legal local-choice embedding, not a supplied
mapping of equilibrium sites. -/
def site (who : Player) (original : M.InformationSite who) : N.InformationSite who := by
  refine ⟨restriction.information who original.1, ?_⟩
  obtain ⟨witness, running, action, permitted⟩ := original.2
  have sourceActive : E.active witness.1.state who :=
    ((M.menu_adequate who witness.1.trace (some action)).mp
      (by simpa only [witness.2] using permitted)).1
  have targetActive := (restriction.active witness.1 who).mpr sourceActive
  have targetRunning : ¬ T.terminal (restriction.history witness.1).state :=
    fun terminal => running ((restriction.terminal witness.1).mp terminal)
  obtain ⟨target, observed⟩ := N.exists_informationSite_of_active who
    (restriction.history witness.1) targetRunning targetActive
  have same : target.1 = restriction.information who original.1 :=
    observed.trans ((restriction.observed who witness.1).trans
      (congrArg (restriction.information who) witness.2))
  exact same ▸ target.2

@[simp] theorem site_val (who : Player) (original : M.InformationSite who) :
    (restriction.site who original).1 = restriction.information who original.1 := rfl

theorem site_injective (who : Player) : Function.Injective (restriction.site who) := by
  intro first second same
  apply Subtype.ext
  exact (restriction.information who).injective (congrArg Subtype.val same)

/-- Only actual source decisions constrain the target extension. -/
def ExtendsProfile (source : ∀ who, M.BehavioralPolicy who)
    (target : ∀ who, N.BehavioralPolicy who) : Prop :=
  ∀ who (original : M.InformationSite who),
    target who (restriction.information who original.1) =
      (source who original.1).map (restriction.choice who original.1)

theorem extends_at_history (source : ∀ who, M.BehavioralPolicy who)
    (target : ∀ who, N.BehavioralPolicy who)
    (agrees : restriction.ExtendsProfile source target)
    (original : E.History) (running : ¬ E.terminal original.state) (who : Player) :
    target who (N.infoOf who (restriction.history original).trace) =
      (source who (M.infoOf who original.trace)).map (restriction.choiceAt who original) := by
  by_cases active : E.active original.state who
  · obtain ⟨decision, observed⟩ := M.exists_informationSite_of_active who original running active
    have indexed : target who (restriction.information who (M.infoOf who original.trace)) =
        (source who (M.infoOf who original.trace)).map
          (restriction.choice who (M.infoOf who original.trace)) := by
      rcases decision with ⟨info, permitted⟩
      dsimp only at observed
      subst info
      exact agrees who ⟨_, permitted⟩
    calc
      _ = (target who (restriction.information who (M.infoOf who original.trace))).map
          (fun action => Eq.mp
            (congrArg (N.Choice who) (restriction.observed who original).symm) action) :=
        (map_transport (target who) (restriction.observed who original).symm).symm
      _ = _ := by rw [indexed, PMF.map_comp]; rfl
  · have inactive : ¬ T.active (restriction.history original).state who :=
      fun enabled => active ((restriction.active original who).mp enabled)
    let _ := N.subsingleton_choice_of_not_active (restriction.history original).trace inactive
    obtain ⟨witness, _⟩ :=
      (target who (N.infoOf who (restriction.history original).trace)).support_nonempty
    exact (eq_pure_of_subsingleton _ witness).trans
      (eq_pure_of_subsingleton _ witness).symm

end ActionRestriction

end GameTheory.Protocol.InformationModel
