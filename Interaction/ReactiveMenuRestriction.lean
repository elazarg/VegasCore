/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.ReactiveResponseMenu
import Interaction.ReactiveResponseEvaluation
import GameTheoryExtensions.Protocol.ActionRestriction

/-! # Action restrictions from nested reactive response menus

Both games use the same application, initial law, scheduler and horizon. Menu
inclusion embeds every legal history without changing any state, response or
observation. The structural one-step square follows from the shared transition
kernel; no execution, information or incentive premise is added.
-/

noncomputable section

namespace Interaction.ReactiveApplication.ResponseMenu

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Principal : Type} {app : ReactiveApplication Principal}

/-- Inclusion at every possible local input, independent of policies or reachability. -/
def IncludedIn (smaller larger : app.ResponseMenu) : Prop :=
  ∀ who past view, smaller.actions who past view ⊆ larger.actions who past view

namespace IncludedIn

variable {smaller larger : app.ResponseMenu} (included : smaller.IncludedIn larger)
  [DecidableEq Principal]
  (initial : PMF app.State) (horizon : Nat) (scheduler : app.Scheduler)

include included in
theorem legal {state : app.ProtocolState} {joint : Principal → Option app.Action}
    (permitted : (smaller.protocol initial horizon scheduler).Legal state joint) :
    (larger.protocol initial horizon scheduler).Legal state joint := by
  refine ⟨permitted.1, fun who => ?_⟩
  have localLegal := permitted.2 who
  cases chosen : joint who with
  | none => simpa only [chosen, protocol] using localLegal
  | some response =>
      rw [chosen] at localLegal
      refine ⟨localLegal.1, ?_⟩
      cases state with
      | none => trivial
      | some control => exact included who _ _ localLegal.2

def trace : ∀ {state}, (smaller.protocol initial horizon scheduler).Trace state →
    (larger.protocol initial horizon scheduler).Trace state
  | _, .start => .start
  | _, .extend prior joint permitted realized =>
      .extend (trace prior) joint (included.legal initial horizon scheduler permitted) realized

def history (original : (smaller.protocol initial horizon scheduler).History) :
    (larger.protocol initial horizon scheduler).History :=
  ⟨original.state, included.trace initial horizon scheduler original.trace⟩

theorem trace_injective {state} :
    Function.Injective (included.trace initial horizon scheduler (state := state)) := by
  intro first second same
  induction first with
  | start => cases second <;> cases same; rfl
  | extend prior joint permitted realized ih =>
      cases second with
      | start => cases same
      | extend other otherJoint otherLegal otherRealized =>
          simp only [trace, Trace.extend.injEq] at same
          rcases same with ⟨rfl, priorEq, jointEq⟩
          have equal := ih (eq_of_heq priorEq)
          cases equal
          cases jointEq
          rfl

theorem history_injective : Function.Injective (included.history initial horizon scheduler) := by
  rintro ⟨first, firstTrace⟩ ⟨second, secondTrace⟩ same
  have stateEq := congrArg History.state same
  change first = second at stateEq
  subst second
  have traceEq := History.mk.inj same
  have equal := included.trace_injective initial horizon scheduler (eq_of_heq traceEq.2)
  cases equal
  rfl

@[simp] theorem history_state (original : (smaller.protocol initial horizon scheduler).History) :
    (included.history initial horizon scheduler original).state = original.state := rfl

@[simp] theorem trace_length {state}
    (original : (smaller.protocol initial horizon scheduler).Trace state) :
    (included.trace initial horizon scheduler original).length = original.length := by
  induction original with
  | start => rfl
  | extend prior joint permitted realized ih => exact congrArg Nat.succ ih

/-- The complete native information value is preserved, including pending reads and own recall. -/
theorem observed (who : Principal)
    (original : (smaller.protocol initial horizon scheduler).History) :
    (larger.information initial horizon scheduler).infoOf who
        (included.history initial horizon scheduler original).trace =
      (smaller.information initial horizon scheduler).infoOf who original.trace := by
  change (larger.signals initial horizon scheduler).infoOf who _ =
    (smaller.signals initial horizon scheduler).infoOf who _
  rw [larger.info, smaller.info]
  rfl

def choice (who : Principal) (info : app.Info)
    (original : (smaller.information initial horizon scheduler).Choice who info) :
    (larger.information initial horizon scheduler).Choice who info := by
  refine ⟨original.1, ?_⟩
  have member := original.2
  cases info with
  | none => exact member
  | some data =>
      obtain ⟨response, permitted, same⟩ := member
      exact ⟨response, included who data.1 data.2 permitted, same⟩

theorem choice_injective (who : Principal) (info : app.Info) :
    Function.Injective (included.choice initial horizon scheduler who info) := by
  intro first second same
  apply Subtype.ext
  exact congrArg (fun chosen => chosen.1) same

/-- Changing the menu does not change the distribution of a retained local step. -/
theorem localStep (original : (smaller.protocol initial horizon scheduler).History)
    (choices : ∀ who, (smaller.information initial horizon scheduler).Choice who
      ((smaller.information initial horizon scheduler).infoOf who original.trace)) :
    ((smaller.information initial horizon scheduler).localStep original choices).map
        (included.history initial horizon scheduler) =
      (larger.information initial horizon scheduler).localStep
        (included.history initial horizon scheduler original) (fun who =>
          Eq.mp (congrArg ((larger.information initial horizon scheduler).Choice who)
            (included.observed initial horizon scheduler who original).symm)
              (included.choice initial horizon scheduler who _ (choices who))) := by
  by_cases stopped : app.terminal original.state
  · simp only [InformationModel.localStep, history_state,
      show (smaller.protocol initial horizon scheduler).terminal original.state from stopped,
      show (larger.protocol initial horizon scheduler).terminal original.state from stopped,
      dite_eq_left, PMF.pure_map]
  · rcases original with ⟨state, original⟩
    change ¬ app.terminal state at stopped
    cases original with
    | start =>
      change ¬ app.terminal none at stopped
      simp only [InformationModel.localStep, history, protocol,
        dite_eq_right stopped, map_bindOnSupport]
      apply bindOnSupport_congr _
      intro target realized
      rw [PMF.pure_map]
      rfl
    | extend prior joint permitted realized =>
      simp only [InformationModel.localStep, history, protocol,
        dite_eq_right stopped, map_bindOnSupport]
      apply bindOnSupport_congr _
      intro target realized
      rw [PMF.pure_map]
      rfl

/-- Nested finite menus give the structural restriction used by the general SE theorem. -/
def actionRestriction :
    (smaller.information initial horizon scheduler).ActionRestriction
      (larger.information initial horizon scheduler) where
  history := ⟨included.history initial horizon scheduler,
    included.history_injective initial horizon scheduler⟩
  information _ := Function.Embedding.refl _
  choice who info := ⟨included.choice initial horizon scheduler who info,
    included.choice_injective initial horizon scheduler who info⟩
  initial := rfl
  length original := included.trace_length initial horizon scheduler original.trace
  terminal _ := Iff.rfl
  active _ _ := Iff.rfl
  observed := included.observed initial horizon scheduler
  step := included.localStep initial horizon scheduler

/-- An additional local choice is exactly a physical response absent from the
smaller menu. The result applies to every input, not only reached histories. -/
theorem extra_choice_response (who : Principal)
    (past : List app.PlayerEntry) (view : app.PlayerView)
    (action : (larger.information initial horizon scheduler).Choice who (some (past, view)))
    (extra : action ∉ Set.range
      ((included.actionRestriction initial horizon scheduler).choice who (some (past, view)))) :
    ∃ response, action.1 = some response ∧ response ∈ larger.actions who past view ∧
      response ∉ smaller.actions who past view := by
  obtain ⟨response, allowed, same⟩ := action.2
  refine ⟨response, same, allowed, ?_⟩
  intro permitted
  let original : (smaller.information initial horizon scheduler).Choice who (some (past, view)) :=
    ⟨some response, response, permitted, rfl⟩
  exact extra ⟨original, Subtype.ext same.symm⟩

/-- Extending a behavioral profile means answering with the same physical
response law at each retained decision input. -/
theorem decoded_at_site
    (source : ∀ who, (smaller.information initial horizon scheduler).BehavioralPolicy who)
    (target : ∀ who, (larger.information initial horizon scheduler).BehavioralPolicy who)
    (agrees : (included.actionRestriction initial horizon scheduler).ExtendsProfile source target)
    (who : Principal) (site : (smaller.information initial horizon scheduler).InformationSite who)
    (past : List app.PlayerEntry) (view : app.PlayerView) (observed : site.1 = some (past, view)) :
    larger.decodeProfile initial horizon scheduler target who past view =
      smaller.decodeProfile initial horizon scheduler source who past view := by
  have same := agrees who site
  change target who site.1 =
    (source who site.1).map (included.choice initial horizon scheduler who site.1) at same
  rw [observed] at same
  simp only [decodeProfile, ReactiveApplication.decodePolicy, embedPolicy, PMF.map_comp]
  rw [same, PMF.map_comp]
  rfl

end IncludedIn
end Interaction.ReactiveApplication.ResponseMenu
