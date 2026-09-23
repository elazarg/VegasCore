/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import VegasTests.PendingMenus
import Interaction.ReactiveHistory
import Vegas.Pending.ReactiveServiceCompletion
import Vegas.Pending.ReactiveStateInvariant
import Vegas.Pending.ReactiveSafety

/-! # A pending-menu obstruction in the reactive reserved service

Two submitted commitments have fixed meanings 1 and 2. The network randomly
delivers one of them before activating the player again. Inclusion selects an
old commitment according to both that signal and the player's new traffic.
Every activation permits just one optional transmission. The service uses its
ordinary event visits, four network opportunities, and reserved inclusion.
Delivery of an already-known own envelope is observable in this information
model. It signals a scheduler choice used by the later inclusion rule; the
example depends on that observation and responsive scheduling capability.
-/

noncomputable section

namespace VegasTests.ReactiveMenus

open GameTheory.Protocol GameTheory.Math.Probability Interaction Vegas Vegas.EventGraphRuntime

abbrev graph := PendingMenus.graph
abbrev runtime := PendingMenus.runtime
abbrev input := PendingMenus.input
abbrev app := runtime.reactiveApplication
abbrev chosen := ServiceOrder.increasing graph

def signalId (bit : Bool) : MessageId Unit := ((), if bit then 0 else 1)

def signal (network : MessageNetwork Unit (Payload graph)) : Bool :=
  (network.inbox ()).head?.any (fun message => message.id = ((), 0))

def selectedId (network : MessageNetwork Unit (Payload graph)) : MessageId Unit :=
  ((), if (network.lookup ((), 2)).isSome == signal network then 0 else 1)

/-- The scheduler uses only its own command recall and public packet traffic. -/
def network : runtime.NetworkPolicy := fun history view =>
  match history.length % (interactionEpoch chosen 4).length with
  | 2 | 4 => FinDist.pure (.activate ())
  | 3 => (FinDist.uniformOfFintype (α := Bool)).map (fun bit => .deliver () (signalId bit))
  | 5 => FinDist.pure (.include (selectedId view.network))
  | _ => FinDist.pure .wait

abbrev scheduler := runtime.interactionScheduler chosen 4 network
abbrev horizon := runtime.interactionHorizon chosen 4
abbrev initialLaw := FinDist.pure (State.initial input)
abbrev arena := app.protocol initialLaw horizon scheduler
abbrev model := app.information initialLaw horizon scheduler

def record (execution : app.Execution) (command : app.Command) (next : app.Execution) :
    app.Execution :=
  { next with environmentRecall := execution.environmentRecall ++
    [⟨execution.observeEnvironment app, command⟩] }

def activate (execution : app.Execution) : app.Execution :=
  record execution (.activate ()) execution

def grant (execution : app.Execution) (event : graph.EventId) : app.Execution :=
  record execution (.application (.grant event))
    { execution with application := { execution.application with serviceGrant := some event } }

def included (execution : app.Execution) (id : MessageId Unit) : app.Execution :=
  record execution (.include id) (execution.includePending app id)

def delivered (execution : app.Execution) (bit : Bool) : app.Execution :=
  record execution (.deliver () (signalId bit))
    { execution with network := execution.network.deliver () (signalId bit) }

theorem grant_step (execution : app.Execution) (event : graph.EventId) :
    execution.environmentStep app (.application (.grant event)) =
      FinDist.pure (grant execution event) := by
  change ((environmentStep runtime execution.application (.grant event)).map _).map _ = _
  simp only [environmentStep, FinDist.map_pure]
  rfl

theorem activate_step (execution : app.Execution) :
    execution.environmentStep app (.activate ()) = FinDist.pure (activate execution) := by
  simp only [ReactiveApplication.Execution.environmentStep, FinDist.map_pure]
  rfl

def setup : app.Execution := .initial app (State.initial input)
def start : app.Execution := activate (grant setup 0)
def afterFirst (action : app.Action) : app.Execution := start.respond app () action
def beforeSecond (action : app.Action) : app.Execution := activate (afterFirst action)
def afterSecond (first second : app.Action) : app.Execution :=
  (beforeSecond first).respond app () second

def first : app.Action := runtime.reactiveBinding () 0 .int (.success 1) 0
def second : app.Action := runtime.reactiveBinding () 0 .int (.success 2) 1
def contested : app.Execution := afterSecond first second
def rootControl (one two : app.Action) : app.Control := ⟨horizon - 3, none, afterSecond one two⟩

theorem epoch_length : (interactionEpoch chosen 4).length = 19 := rfl
theorem horizon_eq : horizon = 114 := rfl

theorem scheduler_zero (execution : app.Execution)
    (length : execution.environmentRecall.length = 0) :
    scheduler execution.environmentRecall (execution.observeEnvironment app) =
      FinDist.pure (.application (.grant 0)) := by
  simp only [interactionScheduler, length]
  rfl

theorem scheduler_one (execution : app.Execution)
    (length : execution.environmentRecall.length = 1) :
    scheduler execution.environmentRecall (execution.observeEnvironment app) =
      FinDist.pure (.activate ()) := by
  simp only [interactionScheduler, length]
  rfl

theorem scheduler_two (execution : app.Execution)
    (length : execution.environmentRecall.length = 2) :
    scheduler execution.environmentRecall (execution.observeEnvironment app) =
      FinDist.pure (.activate ()) := by
  unfold scheduler interactionScheduler
  simp only [length]
  change ((network execution.environmentRecall (execution.observeEnvironment app)).map
    (NetworkChoice.command runtime)) = _
  simp only [network, length]
  change (FinDist.pure (.activate () : NetworkChoice Unit)).map _ = _
  rw [FinDist.map_pure]
  rfl

private def extendPure (history : arena.History) (joint : Unit → Option app.Action)
    (legal : arena.Legal history.state joint) (target : arena.State)
    (law : arena.step history.state ⟨joint, legal⟩ = FinDist.pure target) : arena.History :=
  history.extend legal (by rw [law]; exact FinDist.mem_support_pure.mpr rfl)

private def setupHistory : arena.History :=
  extendPure arena.initHistory (fun _ => none)
    ⟨by change ¬ False; simp, fun _ => by change ¬ (none : Option Unit) = some _; simp⟩
    (some ⟨horizon, none, setup⟩) (by
      simp only [arena, ReactiveApplication.protocol, ReactiveApplication.transition,
        FinDist.map_pure]
      rfl)

private def grantHistory : arena.History :=
  extendPure setupHistory (fun _ => none)
    ⟨by change ¬ (114 = 0 ∧ _); simp,
      fun _ => by change ¬ (none : Option Unit) = some _; simp⟩
    (some ⟨horizon - 1, none, grant setup 0⟩) (by
      change (scheduler setup.environmentRecall (setup.observeEnvironment app)).bind _ = _
      rw [scheduler_zero setup rfl, FinDist.pure_bind]
      rw [grant_step, FinDist.map_pure]
      rfl)

private def activeHistory : arena.History :=
  extendPure grantHistory (fun _ => none)
    ⟨by change ¬ (113 = 0 ∧ _); simp,
      fun _ => by change ¬ (none : Option Unit) = some _; simp⟩
    (some ⟨horizon - 2, some (), start⟩) (by
      change (scheduler (grant setup 0).environmentRecall
        ((grant setup 0).observeEnvironment app)).bind _ = _
      rw [scheduler_one _ rfl, FinDist.pure_bind]
      simp only [ReactiveApplication.Execution.environmentStep, FinDist.map_pure]
      rfl)

private def firstHistory (action : app.Action) : arena.History :=
  extendPure activeHistory (fun _ => some action)
    ⟨by change ¬ (112 = 0 ∧ _); simp,
      fun who => by cases who; exact ⟨rfl, Set.mem_univ _⟩⟩
    (some ⟨horizon - 2, none, afterFirst action⟩) rfl

private def reactivatedHistory (action : app.Action) : arena.History :=
  extendPure (firstHistory action) (fun _ => none)
    ⟨by change ¬ (112 = 0 ∧ _); simp,
      fun _ => by change ¬ (none : Option Unit) = some _; simp⟩
    (some ⟨horizon - 3, some (), beforeSecond action⟩) (by
      change (scheduler (afterFirst action).environmentRecall
        ((afterFirst action).observeEnvironment app)).bind _ = _
      have length : (afterFirst action).environmentRecall.length = 2 := by
        rcases action with ⟨memory, transmission⟩
        cases transmission with
        | none => rfl
        | some transmission => cases transmission <;> rfl
      rw [scheduler_two _ length, FinDist.pure_bind]
      simp only [ReactiveApplication.Execution.environmentStep, FinDist.map_pure]
      rfl)

def rootHistory (one two : app.Action) : arena.History :=
  extendPure (reactivatedHistory one) (fun _ => some two)
    ⟨by change ¬ (111 = 0 ∧ _); simp,
      fun who => by cases who; exact ⟨rfl, Set.mem_univ _⟩⟩
    (some (rootControl one two)) rfl

private theorem extendPure_unique (history : arena.History) (joint : Unit → Option app.Action)
    (legal : arena.Legal history.state joint) (target : arena.State)
    (law : arena.step history.state ⟨joint, legal⟩ = FinDist.pure target)
    (otherLegal : arena.Legal history.state joint) (other : arena.State)
    (supported : other ∈ (arena.step history.state ⟨joint, otherLegal⟩).support) :
    history.extend otherLegal supported = extendPure history joint legal target law := by
  rw [law] at supported
  have same := FinDist.mem_support_pure.mp supported
  subst other
  rfl

private theorem inactive_joint (history : arena.History) (joint : Unit → Option app.Action)
    (legal : arena.Legal history.state joint)
    (inactive : ∀ who, ¬ arena.active history.state who) : joint = fun _ => none := by
  funext who
  cases choice : joint who with
  | none => rfl
  | some action =>
      have valid := legal.2 who
      rw [choice] at valid
      exact False.elim (inactive who valid.1)

private theorem active_joint (history : arena.History) (joint : Unit → Option app.Action)
    (legal : arena.Legal history.state joint) (active : arena.active history.state ()) :
    ∃ action, joint = fun _ => some action := by
  obtain ⟨action, chosen⟩ := LegalOption.exists_eq_some_of_active (joint ())
    (ExecutionProtocol.legalOption_of_legal legal ()) active
  exact ⟨action, funext fun who => by cases who; exact chosen⟩

private def Classified (history : arena.History) : Prop :=
  history = arena.initHistory ∨ history = setupHistory ∨ history = grantHistory ∨
    history = activeHistory ∨ (∃ action, history = firstHistory action) ∨
      (∃ action, history = reactivatedHistory action) ∨
        ∃ one two, arena.HistoryReaches (rootHistory one two) history

private theorem classified_step (history : arena.History) (classified : Classified history)
    (joint : Unit → Option app.Action) (legal : arena.Legal history.state joint)
    (target : arena.State)
    (supported : target ∈ (arena.step history.state ⟨joint, legal⟩).support) :
    Classified (history.extend legal supported) := by
  rcases classified with rfl | rfl | rfl | rfl | ⟨action, rfl⟩ | ⟨action, rfl⟩ |
    ⟨one, two, reached⟩
  · have same := inactive_joint _ joint legal (fun _ h => by cases h)
    subst joint
    exact Or.inr (Or.inl (extendPure_unique _ _ _ _ _ legal target supported))
  · have same := inactive_joint _ joint legal (fun _ h => by cases h)
    subst joint
    exact Or.inr (Or.inr (Or.inl (extendPure_unique _ _ _ _ _ legal target supported)))
  · have same := inactive_joint _ joint legal (fun _ h => by cases h)
    subst joint
    exact Or.inr (Or.inr (Or.inr (Or.inl
      (extendPure_unique _ _ _ _ _ legal target supported))))
  · obtain ⟨action, rfl⟩ := active_joint _ joint legal rfl
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨action, extendPure_unique _ _ _ _ _ legal target supported⟩))))
  · have same := inactive_joint _ joint legal (fun _ h => by cases h)
    subst joint
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨action, extendPure_unique _ _ _ _ _ legal target supported⟩)))))
  · obtain ⟨next, rfl⟩ := active_joint _ joint legal rfl
    have same : (reactivatedHistory action).extend legal supported = rootHistory action next :=
      extendPure_unique _ _ _ _ _ legal target supported
    refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨action, next, ?_⟩)))))
    rw [same]
    exact ExecutionProtocol.HistoryReaches.refl arena _
  · obtain ⟨fuel, path⟩ := reached
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨one, two, fuel + 1,
      path.trans (.step joint legal supported (.refl 0 _))⟩)))))

private theorem classified : ∀ {state} (trace : arena.Trace state), Classified ⟨state, trace⟩
  | _, .start => Or.inl rfl
  | _, .extend prior joint legal supported =>
      classified_step _ (classified prior) joint legal _ supported

private def actionRecall (control : app.Control) : List app.Action :=
  (control.execution.recall ()).map ReactiveApplication.PlayerEntry.action

theorem afterFirst_actions (action : app.Action) :
    ((afterFirst action).recall ()).map ReactiveApplication.PlayerEntry.action = [action] := by
  rw [afterFirst, app.respond_actions]
  rfl

theorem afterSecond_actions (one two : app.Action) :
    ((afterSecond one two).recall ()).map ReactiveApplication.PlayerEntry.action = [one, two] := by
  rw [afterSecond, app.respond_actions]
  change ((afterFirst one).recall ()).map ReactiveApplication.PlayerEntry.action ++ [two] = _
  rw [afterFirst_actions]
  rfl

private theorem initial_actions_recalled (one two : app.Action)
    (history : arena.History) (control : app.Control)
    (reached : arena.HistoryReaches (rootHistory one two) history)
    (stateEq : history.state = some control) : [one, two] <+: actionRecall control := by
  obtain ⟨fuel, path⟩ := reached
  have retained := app.reaches_recall_prefix initialLaw horizon scheduler path
    (rootControl one two) control rfl stateEq ()
  have actions := retained.map ReactiveApplication.PlayerEntry.action
  change ((afterSecond one two).recall ()).map ReactiveApplication.PlayerEntry.action <+:
    actionRecall control at actions
  rwa [afterSecond_actions] at actions

private theorem recalled_initial_actions_reached (one two : app.Action)
    (history : arena.History) (control : app.Control) (stateEq : history.state = some control)
    (recalled : [one, two] <+: actionRecall control) :
    arena.HistoryReaches (rootHistory one two) history := by
  have casesHistory : Classified history := classified history.trace
  rcases casesHistory with rfl | rfl | rfl | rfl | ⟨action, rfl⟩ | ⟨action, rfl⟩ |
    ⟨a, b, reached⟩
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
    have bound := recalled.length_le
    change 2 ≤ 0 at bound
    omega
  · cases Option.some.inj stateEq
    change [one, two] <+: ((afterFirst action).recall ()).map _ at recalled
    rw [afterFirst_actions] at recalled
    have bound := recalled.length_le
    change 2 ≤ 1 at bound
    omega
  · cases Option.some.inj stateEq
    change [one, two] <+: ((afterFirst action).recall ()).map _ at recalled
    rw [afterFirst_actions] at recalled
    have bound := recalled.length_le
    change 2 ≤ 1 at bound
    omega
  · have actual := initial_actions_recalled a b history control reached stateEq
    have same : [one, two] = [a, b] :=
      (List.prefix_iff_eq_take.mp recalled).trans (List.prefix_iff_eq_take.mp actual).symm
    have components := List.cons.inj same
    cases components.1
    cases (List.cons.inj components.2).1
    exact reached

/-- Every future decision information set stays below this actual initialized
history. The root precedes the network signal and the response to that signal. -/
theorem root_isSubgameRoot : model.IsSubgameRoot (rootHistory first second) := by
  intro who inside outside reached _ insideActive _ outsideActive sameInfo
  cases who
  have insideCases : ∃ control, inside.state = some control := by
    cases stateEq : inside.state with
    | none =>
        simp only [ReactiveApplication.protocol, stateEq, ReactiveApplication.actor] at insideActive
        cases insideActive
    | some control => exact ⟨control, rfl⟩
  have outsideCases : ∃ control, outside.state = some control := by
    cases stateEq : outside.state with
    | none =>
        simp only [ReactiveApplication.protocol, stateEq, ReactiveApplication.actor]
          at outsideActive
        cases outsideActive
    | some control => exact ⟨control, rfl⟩
  obtain ⟨insideControl, insideEq⟩ := insideCases
  obtain ⟨outsideControl, outsideEq⟩ := outsideCases
  have infoEq : app.observe () inside.state = app.observe () outside.state := by
    change (app.signals initialLaw horizon scheduler).infoOf () inside.trace =
      (app.signals initialLaw horizon scheduler).infoOf () outside.trace at sameInfo
    simpa only [app.info] using sameInfo
  change app.actor inside.state = some () at insideActive
  change app.actor outside.state = some () at outsideActive
  have insideActs : insideControl.actor = some () := by
    simpa only [insideEq, ReactiveApplication.actor, Option.bind_some] using insideActive
  have outsideActs : outsideControl.actor = some () := by
    simpa only [outsideEq, ReactiveApplication.actor, Option.bind_some] using outsideActive
  simp only [insideEq, outsideEq, ReactiveApplication.observe, insideActs, outsideActs,
    ↓reduceIte] at infoEq
  have recallEq := congrArg Prod.fst (Option.some.inj infoEq)
  have actionsEq : actionRecall insideControl = actionRecall outsideControl :=
    congrArg (List.map ReactiveApplication.PlayerEntry.action) recallEq
  exact recalled_initial_actions_reached first second outside outsideControl outsideEq
    (actionsEq ▸ initial_actions_recalled first second inside insideControl reached insideEq)

end VegasTests.ReactiveMenus
