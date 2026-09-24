/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.ReactiveHistory

/-! # Proper subgames after a deterministic response prefix

In a one-player protocol, two initially scheduled responses with deterministic
activation observations form a proper subgame root. Own action recall identifies
the prefix inside every subsequent decision information set. Scheduling after
this prefix is unrestricted.
-/

noncomputable section

namespace Interaction.ReactiveApplication

open GameTheory.Protocol GameTheory.Math.Probability

/-- Data identifying a deterministic initial pair of player responses.
No restriction is imposed on either raw response or the remaining scheduler. -/
structure TwoResponsePrefix (app : ReactiveApplication Unit) where
  initialState : app.State
  remaining : Nat
  scheduler : app.Scheduler
  schedules : ∀ history view, history.length < 2 →
    scheduler history view = FinDist.pure (.activate ())
  activation : ∀ execution : app.Execution,
    execution.environmentStep app (.activate ()) = FinDist.pure
      { execution with environmentRecall := execution.environmentRecall ++
        [⟨execution.observeEnvironment app, .activate ()⟩] }

namespace TwoResponsePrefix

variable {app : ReactiveApplication Unit} (stem : app.TwoResponsePrefix)

abbrev arena := app.protocol (FinDist.pure stem.initialState) (stem.remaining + 2)
  stem.scheduler
abbrev model := app.information (FinDist.pure stem.initialState) (stem.remaining + 2)
  stem.scheduler

def initial : app.Execution := .initial app stem.initialState

def activated (_stem : app.TwoResponsePrefix) (execution : app.Execution) : app.Execution :=
  { execution with environmentRecall := execution.environmentRecall ++
    [⟨execution.observeEnvironment app, .activate ()⟩] }

def afterFirst (action : app.Action) : app.Execution :=
  (stem.activated stem.initial).respond app () action

def afterSecond (one two : app.Action) : app.Execution :=
  (stem.activated (stem.afterFirst one)).respond app () two

private def extendPure (history : stem.arena.History) (joint : Unit → Option app.Action)
    (legal : stem.arena.Legal history.state joint) (target : stem.arena.State)
    (law : stem.arena.step history.state ⟨joint, legal⟩ = FinDist.pure target) :
    stem.arena.History :=
  history.extend legal (by rw [law]; exact FinDist.mem_support_pure.mpr rfl)

private def setupHistory : stem.arena.History :=
  stem.extendPure stem.arena.initHistory (fun _ => none)
    ⟨by change ¬ False; simp, fun _ => by change ¬ (none : Option Unit) = some _; simp⟩
    (some ⟨(stem.remaining + 2), none, stem.initial⟩) (by
      change (FinDist.pure stem.initialState).map _ = _
      rw [FinDist.map_pure]; rfl)

private def firstActivation : stem.arena.History :=
  stem.extendPure stem.setupHistory (fun _ => none)
    ⟨by change ¬ ((stem.remaining + 2) = 0 ∧ _); simp,
      fun _ => by change ¬ (none : Option Unit) = some _; simp⟩
    (some ⟨(stem.remaining + 1), some (), stem.activated stem.initial⟩) (by
      change (stem.scheduler _ _).bind _ = _
      rw [stem.schedules _ _ (by change 0 < 2; decide), FinDist.pure_bind,
        stem.activation, FinDist.map_pure]; rfl)

private def firstHistory (action : app.Action) : stem.arena.History :=
  stem.extendPure stem.firstActivation (fun _ => some action)
    ⟨by change ¬ ((stem.remaining + 1) = 0 ∧ _); omega,
      fun who => by cases who; exact ⟨rfl, Set.mem_univ _⟩⟩
    (some ⟨(stem.remaining + 1), none, stem.afterFirst action⟩) rfl

private theorem afterFirst_environment (action : app.Action) :
    (stem.afterFirst action).environmentRecall = (stem.activated stem.initial).environmentRecall :=
  app.respond_environmentRecall (stem.activated stem.initial) () action

private def secondActivation (action : app.Action) : stem.arena.History :=
  stem.extendPure (stem.firstHistory action) (fun _ => none)
    ⟨by change ¬ ((stem.remaining + 1) = 0 ∧ _); simp,
      fun _ => by change ¬ (none : Option Unit) = some _; simp⟩
    (some ⟨stem.remaining, some (), stem.activated (stem.afterFirst action)⟩) (by
      change (stem.scheduler (stem.afterFirst action).environmentRecall _).bind _ = _
      rw [stem.afterFirst_environment]
      rw [stem.schedules _ _ (by change 1 < 2; decide), FinDist.pure_bind,
        stem.activation, FinDist.map_pure]; rfl)

def secondHistory (one two : app.Action) : stem.arena.History :=
  stem.extendPure (stem.secondActivation one) (fun _ => some two)
    ⟨by change ¬ (stem.remaining = 0 ∧ _); simp,
      fun who => by cases who; exact ⟨rfl, Set.mem_univ _⟩⟩
    (some ⟨stem.remaining, none, stem.afterSecond one two⟩) rfl

private theorem extendPure_unique (history : stem.arena.History) (joint : Unit → Option app.Action)
    (legal : stem.arena.Legal history.state joint) (target : stem.arena.State)
    (law : stem.arena.step history.state ⟨joint, legal⟩ = FinDist.pure target)
    (otherLegal : stem.arena.Legal history.state joint) (other : stem.arena.State)
    (supported : other ∈ (stem.arena.step history.state ⟨joint, otherLegal⟩).support) :
    history.extend otherLegal supported = stem.extendPure history joint legal target law := by
  rw [law] at supported
  have same := FinDist.mem_support_pure.mp supported
  subst other
  rfl

private theorem inactive_joint (history : stem.arena.History) (joint : Unit → Option app.Action)
    (legal : stem.arena.Legal history.state joint)
    (inactive : ∀ who, ¬ stem.arena.active history.state who) : joint = fun _ => none := by
  funext who
  cases choice : joint who with
  | none => rfl
  | some action =>
      have valid := legal.2 who
      rw [choice] at valid
      exact False.elim (inactive who valid.1)

private theorem active_joint (history : stem.arena.History) (joint : Unit → Option app.Action)
    (legal : stem.arena.Legal history.state joint) (active : stem.arena.active history.state ()) :
    ∃ action, joint = fun _ => some action := by
  obtain ⟨action, chosen⟩ := LegalOption.exists_eq_some_of_active (joint ())
    (ExecutionProtocol.legalOption_of_legal legal ()) active
  exact ⟨action, funext fun who => by cases who; exact chosen⟩

private def Classified (history : stem.arena.History) : Prop :=
  history = stem.arena.initHistory ∨ history = stem.setupHistory ∨ history = stem.firstActivation ∨
    (∃ action, history = stem.firstHistory action) ∨
    (∃ action, history = stem.secondActivation action) ∨
      ∃ one two, stem.arena.HistoryReaches (stem.secondHistory one two) history

private theorem classified_step (history : stem.arena.History)
    (classification : stem.Classified history)
    (joint : Unit → Option app.Action) (legal : stem.arena.Legal history.state joint)
    (target : stem.arena.State)
    (supported : target ∈ (stem.arena.step history.state ⟨joint, legal⟩).support) :
    stem.Classified (history.extend legal supported) := by
  rcases classification with
    rfl | rfl | rfl | ⟨action, rfl⟩ | ⟨action, rfl⟩ | ⟨one, two, reached⟩
  · have same := stem.inactive_joint _ joint legal (fun _ h => by cases h)
    subst joint
    exact Or.inr (Or.inl (stem.extendPure_unique _ _ _ _ _ legal target supported))
  · have same := stem.inactive_joint _ joint legal (fun _ h => by cases h)
    subst joint
    exact Or.inr (Or.inr (Or.inl (stem.extendPure_unique _ _ _ _ _ legal target supported)))
  · obtain ⟨action, rfl⟩ := stem.active_joint _ joint legal rfl
    exact Or.inr (Or.inr (Or.inr (Or.inl
      ⟨action, stem.extendPure_unique _ _ _ _ _ legal target supported⟩)))
  · have same := stem.inactive_joint _ joint legal (fun _ h => by cases h)
    subst joint
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨action, stem.extendPure_unique _ _ _ _ _ legal target supported⟩))))
  · obtain ⟨next, rfl⟩ := stem.active_joint _ joint legal rfl
    have same : (stem.secondActivation action).extend legal supported =
        stem.secondHistory action next :=
      stem.extendPure_unique _ _ _ _ _ legal target supported
    refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨action, next, ?_⟩))))
    rw [same]
    exact ExecutionProtocol.HistoryReaches.refl stem.arena _
  · obtain ⟨fuel, path⟩ := reached
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨one, two, fuel + 1,
      path.trans (.step joint legal supported (.refl 0 _))⟩))))

private theorem classified :
    ∀ {state} (trace : stem.arena.Trace state), stem.Classified ⟨state, trace⟩
  | _, .start => Or.inl rfl
  | _, .extend prior joint legal supported =>
      stem.classified_step _ (classified prior) joint legal _ supported

private def actionRecall (control : app.Control) : List app.Action :=
  (control.execution.recall ()).map ReactiveApplication.PlayerEntry.action

private theorem first_actions (action : app.Action) :
    ((stem.afterFirst action).recall ()).map ReactiveApplication.PlayerEntry.action = [action] :=
  app.respond_actions (stem.activated stem.initial) () action

private theorem second_actions (one two : app.Action) :
    ((stem.afterSecond one two).recall ()).map ReactiveApplication.PlayerEntry.action =
      [one, two] := by
  rw [afterSecond, app.respond_actions]
  change ((stem.afterFirst one).recall ()).map _ ++ [two] = _
  rw [stem.first_actions]; rfl

private theorem initial_actions_recalled (one two : app.Action)
    (history : stem.arena.History) (control : app.Control)
    (reached : stem.arena.HistoryReaches (stem.secondHistory one two) history)
    (stateEq : history.state = some control) : [one, two] <+: actionRecall control := by
  obtain ⟨fuel, path⟩ := reached
  have retained := app.reaches_recall_prefix (FinDist.pure stem.initialState)
    (stem.remaining + 2) stem.scheduler path
    ⟨stem.remaining, none, stem.afterSecond one two⟩ control rfl stateEq ()
  have mapped := retained.map ReactiveApplication.PlayerEntry.action
  simpa only [stem.second_actions, actionRecall] using mapped

private theorem recalled_initial_actions_reached (one two : app.Action)
    (history : stem.arena.History) (control : app.Control) (stateEq : history.state = some control)
    (recalled : [one, two] <+: actionRecall control) :
    stem.arena.HistoryReaches (stem.secondHistory one two) history := by
  have casesHistory : stem.Classified history := stem.classified history.trace
  rcases casesHistory with
    rfl | rfl | rfl | ⟨action, rfl⟩ | ⟨action, rfl⟩ | ⟨a, b, reached⟩
  · cases stateEq
  · cases Option.some.inj stateEq
    have bound := recalled.length_le
    change 2 ≤ 0 at bound
    omega
  · cases Option.some.inj stateEq
    have bound := recalled.length_le
    change 2 ≤ 0 at bound
    omega
  · cases Option.some.inj stateEq
    change [one, two] <+: ((stem.afterFirst action).recall ()).map _ at recalled
    rw [stem.first_actions] at recalled
    have bound := recalled.length_le
    simp only [List.length_cons, List.length_nil] at bound
    omega
  · cases Option.some.inj stateEq
    change [one, two] <+: ((stem.afterFirst action).recall ()).map _ at recalled
    rw [stem.first_actions] at recalled
    have bound := recalled.length_le
    simp only [List.length_cons, List.length_nil] at bound
    omega
  · have actual := stem.initial_actions_recalled a b history control reached stateEq
    have same : [one, two] = [a, b] :=
      (List.prefix_iff_eq_take.mp recalled).trans (List.prefix_iff_eq_take.mp actual).symm
    have components := List.cons.inj same
    cases components.1
    cases (List.cons.inj components.2).1
    exact reached

/-- Own response recall identifies the deterministic prefix. Every future
decision information set stays inside the resulting continuation. -/
theorem secondHistory_isSubgameRoot (one two : app.Action) :
    stem.model.IsSubgameRoot (stem.secondHistory one two) := by
  intro who inside outside reached _ insideActive _ outsideActive sameInfo
  cases who
  have controls (history : stem.arena.History) (active : stem.arena.active history.state ()) :
      ∃ control, history.state = some control ∧ control.actor = some () := by
    cases stateEq : history.state with
    | none =>
        change app.actor history.state = some () at active
        rw [stateEq] at active
        cases active
    | some control =>
        refine ⟨control, rfl, ?_⟩
        change app.actor history.state = some () at active
        rwa [stateEq] at active
  obtain ⟨insideControl, insideEq, insideActs⟩ := controls inside insideActive
  obtain ⟨outsideControl, outsideEq, outsideActs⟩ := controls outside outsideActive
  have infoEq : app.observe () inside.state = app.observe () outside.state := by
    simpa only [model, ReactiveApplication.information, app.info] using sameInfo
  rw [insideEq, outsideEq, ReactiveApplication.observe, ite_eq_left insideActs,
    ReactiveApplication.observe, ite_eq_left outsideActs] at infoEq
  have recallEq := congrArg Prod.fst (Option.some.inj infoEq)
  have actionsEq : actionRecall insideControl = actionRecall outsideControl :=
    congrArg (List.map ReactiveApplication.PlayerEntry.action) recallEq
  exact stem.recalled_initial_actions_reached one two outside outsideControl outsideEq
    (actionsEq ▸ stem.initial_actions_recalled one two inside insideControl reached insideEq)

end TwoResponsePrefix
end Interaction.ReactiveApplication
