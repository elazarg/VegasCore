/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.ReactiveDecisionInformation

/-! # Reactive runtime instances with explicit finite response menus

A menu depends only on the player's recall and current observation. The
instance uses the application's existing transition, scheduler, observation
rule and clock. All legal histories of the instance embed into the full
runtime. This is a restriction of available responses, not a claim that omitted
responses are strategically redundant or that equilibria transfer to the full
runtime. Policies remain arbitrary mathematical functions of their inputs.
-/

noncomputable section

namespace Interaction.ReactiveApplication

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Principal : Type} (app : ReactiveApplication Principal)

/-- An explicit runtime premise, independent of utilities and prescribed play.
All responses within this menu, including errors, are available to deviations. -/
structure ResponseMenu where
  actions : Principal → List app.PlayerEntry → app.PlayerView → Finset app.Action
  nonempty : ∀ who past view, (actions who past view).Nonempty

namespace ResponseMenu

variable {app} (menu : app.ResponseMenu) [DecidableEq Principal]

def available (state : app.ProtocolState) (who : Principal) : Set app.Action :=
  match state with
  | none => Set.univ
  | some control => menu.actions who (control.execution.recall who)
      (control.execution.observe app who)

/-- Only availability changes. Every realized transition is the original one. -/
def protocol (initial : FinDist app.State) (horizon : Nat) (scheduler : app.Scheduler) :
    ExecutionProtocol Principal where
  State := app.ProtocolState
  Action _ := app.Action
  init := none
  active state who := app.actor state = some who
  available := menu.available
  terminal := app.terminal
  step state joint := app.transition initial horizon scheduler state joint.1
  progress state _ := by
    classical
    cases state with
    | none => exact ⟨fun _ => none, fun _ => by simp [actor]⟩
    | some control =>
        let action := fun who => (menu.nonempty who (control.execution.recall who)
          (control.execution.observe app who)).choose
        refine ⟨fun who => if control.actor = some who then some (action who) else none, ?_⟩
        intro who
        by_cases active : control.actor = some who
        · simpa only [active, ↓reduceIte, actor, Option.bind_some, available,
            Finset.mem_coe] using
            And.intro active (menu.nonempty who (control.execution.recall who)
              (control.execution.observe app who)).choose_spec
        · simp [active, actor]

theorem legal_raw (initial : FinDist app.State) (horizon : Nat) (scheduler : app.Scheduler)
    {state : app.ProtocolState} {joint : Principal → Option app.Action}
    (legal : (menu.protocol initial horizon scheduler).Legal state joint) :
    (app.protocol initial horizon scheduler).Legal state joint := by
  refine ⟨legal.1, fun who => ?_⟩
  have localLegal := legal.2 who
  cases chosen : joint who <;> rw [chosen] at localLegal
  · exact localLegal
  · exact ⟨localLegal.1, Set.mem_univ _⟩

def toRawTrace (initial : FinDist app.State) (horizon : Nat) (scheduler : app.Scheduler) :
    ∀ {state}, (menu.protocol initial horizon scheduler).Trace state →
      (app.protocol initial horizon scheduler).Trace state
  | _, .start => .start
  | _, .extend prior joint legal realized =>
      .extend (toRawTrace initial horizon scheduler prior) joint
        (menu.legal_raw initial horizon scheduler legal) realized

def toRawHistory (initial : FinDist app.State) (horizon : Nat) (scheduler : app.Scheduler)
    (history : (menu.protocol initial horizon scheduler).History) :
    (app.protocol initial horizon scheduler).History :=
  ⟨history.state, menu.toRawTrace initial horizon scheduler history.trace⟩

theorem toRawTrace_injective (initial : FinDist app.State) (horizon : Nat)
    (scheduler : app.Scheduler) {state} :
    Function.Injective (menu.toRawTrace initial horizon scheduler (state := state)) := by
  intro first second same
  induction first with
  | start => cases second <;> cases same; rfl
  | extend prior joint legal realized ih =>
      cases second with
      | start => cases same
      | extend other otherJoint otherLegal otherRealized =>
          simp only [toRawTrace, Trace.extend.injEq] at same
          rcases same with ⟨rfl, priorEq, jointEq⟩
          have equal := ih (eq_of_heq priorEq)
          cases equal
          cases jointEq
          rfl

theorem toRawHistory_injective (initial : FinDist app.State) (horizon : Nat)
    (scheduler : app.Scheduler) :
    Function.Injective (menu.toRawHistory initial horizon scheduler) := by
  rintro ⟨first, firstTrace⟩ ⟨second, secondTrace⟩ same
  have stateEq := congrArg History.state same
  change first = second at stateEq
  subst second
  have traceEq := History.mk.inj same
  have equal := menu.toRawTrace_injective initial horizon scheduler (eq_of_heq traceEq.2)
  cases equal
  rfl

@[simp]
theorem toRawTrace_length (initial : FinDist app.State) (horizon : Nat)
    (scheduler : app.Scheduler) {state}
    (trace : (menu.protocol initial horizon scheduler).Trace state) :
    (menu.toRawTrace initial horizon scheduler trace).length = trace.length := by
  induction trace with
  | start => rfl
  | extend prior joint legal realized ih => exact congrArg Nat.succ ih

theorem bounded (initial : FinDist app.State) (horizon : Nat) (scheduler : app.Scheduler) :
    (menu.protocol initial horizon scheduler).BoundedHorizon (2 * horizon + 1) := by
  intro state trace enough
  apply app.bounded initial horizon scheduler state
    (menu.toRawTrace initial horizon scheduler trace)
  simpa only [toRawTrace_length] using enough

def signals (initial : FinDist app.State) (horizon : Nat) (scheduler : app.Scheduler) :
    InfoSignals (menu.protocol initial horizon scheduler) where
  PublicSignal := Unit
  PrivateSignal _ := app.Info
  initialPublic := ()
  initialPrivate _ := none
  publicSignal _ := ()
  privateSignal who event := app.observe who event.target
  InfoState _ := app.Info
  initInfo _ view _ := view
  pushInfo _ _ _ view _ := view

theorem info (initial : FinDist app.State) (horizon : Nat) (scheduler : app.Scheduler)
    (who : Principal) : ∀ {state} (trace : (menu.protocol initial horizon scheduler).Trace state),
    (menu.signals initial horizon scheduler).infoOf who trace = app.observe who state
  | _, .start => rfl
  | _, .extend _ _ _ _ => rfl

def information (initial : FinDist app.State) (horizon : Nat) (scheduler : app.Scheduler) :
    InformationModel (menu.protocol initial horizon scheduler) where
  toInfoSignals := menu.signals initial horizon scheduler
  menu who info := match info with
    | none => {none}
    | some (past, view) => {choice | ∃ action ∈ menu.actions who past view, choice = some action}
  menu_adequate := by
    intro who state trace choice
    rw [menu.info initial horizon scheduler who trace]
    cases state with
    | none => cases choice <;> simp [observe, LegalOption, protocol, actor]
    | some control =>
        by_cases active : control.actor = some who
        all_goals cases choice
        all_goals simp [observe, active, LegalOption, protocol, actor, available]

/-- The finite presentation leaves the player's complete observation unchanged. -/
theorem info_toRawTrace (initial : FinDist app.State) (horizon : Nat)
    (scheduler : app.Scheduler) (who : Principal) {state}
    (trace : (menu.protocol initial horizon scheduler).Trace state) :
    (app.information initial horizon scheduler).infoOf who
        (menu.toRawTrace initial horizon scheduler trace) =
      (menu.information initial horizon scheduler).infoOf who trace := by
  change (app.signals initial horizon scheduler).infoOf who _ =
    (menu.signals initial horizon scheduler).infoOf who _
  rw [app.info, menu.info]

variable (initial : FinDist app.State) (horizon : Nat) (scheduler : app.Scheduler)

def rawChoice (who : Principal) (info : app.Info)
    (choice : (menu.information initial horizon scheduler).Choice who info) :
    (app.information initial horizon scheduler).Choice who info := by
  refine ⟨choice.1, ?_⟩
  have member := choice.2
  cases info with
  | none =>
      change choice.1 = none at member
      change choice.1.isSome = false
      rw [member]; rfl
  | some data =>
      obtain ⟨action, _, same⟩ := member
      change choice.1.isSome = true
      rw [same]; rfl

def rawSite (who : Principal)
    (site : (menu.information initial horizon scheduler).InformationSite who) :
    (app.information initial horizon scheduler).InformationSite who := by
  refine ⟨site.1, ?_⟩
  obtain ⟨history, running, action, legal⟩ := site.2
  refine ⟨⟨menu.toRawHistory initial horizon scheduler history.1, ?_⟩,
    running, action, ?_⟩
  · exact (menu.info_toRawTrace initial horizon scheduler who history.1.trace).trans history.2
  · exact (menu.rawChoice initial horizon scheduler who site.1 ⟨some action, legal⟩).2

def rawInformationHistory (who : Principal)
    (site : (menu.information initial horizon scheduler).InformationSite who)
    (history : (menu.information initial horizon scheduler).InformationHistory who site.1) :
    (app.information initial horizon scheduler).InformationHistory who
      (menu.rawSite initial horizon scheduler who site).1 :=
  ⟨menu.toRawHistory initial horizon scheduler history.1,
    (menu.info_toRawTrace initial horizon scheduler who history.1.trace).trans history.2⟩

theorem reaches_raw {first last : (menu.protocol initial horizon scheduler).History}
    {fuel : Nat} (path : (menu.protocol initial horizon scheduler).ReachesWithin fuel first last) :
    (app.protocol initial horizon scheduler).ReachesWithin fuel
      (menu.toRawHistory initial horizon scheduler first)
      (menu.toRawHistory initial horizon scheduler last) := by
  induction path with
  | refl _ history => exact .refl _ _
  | step joint legal realized rest ih =>
      exact .step joint (menu.legal_raw initial horizon scheduler legal) realized ih

theorem informationSite_allNonterminal (who : Principal)
    (site : (menu.information initial horizon scheduler).InformationSite who) :
    site.AllNonterminal := by
  intro history
  exact app.informationSite_allNonterminal initial horizon scheduler who
    (menu.rawSite initial horizon scheduler who site)
    (menu.rawInformationHistory initial horizon scheduler who site history)

theorem decisionInformationAntichain :
    (menu.information initial horizon scheduler).DecisionInformationAntichain := by
  intro who site first second joint legal target realized fuel path
  exact app.decisionInformationAntichain initial horizon scheduler who
    (menu.rawSite initial horizon scheduler who site)
    (menu.rawInformationHistory initial horizon scheduler who site first)
    (menu.rawInformationHistory initial horizon scheduler who site second)
    joint (menu.legal_raw initial horizon scheduler legal) target realized fuel
    (menu.reaches_raw initial horizon scheduler path)

end ResponseMenu
end Interaction.ReactiveApplication
