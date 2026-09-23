/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import VegasTests.PendingMenusSource
import Vegas.Pending.ReactiveServiceProgress
import Vegas.Pending.ReactiveSafety
import Interaction.ReactiveHistory

/-! # Public scheduling can restrict a reactive continuation

The scheduler activates one player for separate public transmissions. Once two
valid commitments are pending, a further transmission determines which older
packet is included. There are no private preparation actions, leak samples,
or deliveries to the sender. The information model and histories below are
those of the actual reactive application.
-/

noncomputable section

namespace VegasTests.ReactivePendingMenus

open GameTheory.Protocol GameTheory.Math.Probability Interaction Vegas Vegas.EventGraphRuntime

abbrev graph := PendingMenus.graph
abbrev runtime := PendingMenus.runtime
abbrev input := PendingMenus.input

def leaks : MessageNetwork.ObservationRule Unit (Payload graph) := fun _ _ => FinDist.pure ∅
abbrev app := runtime.reactiveApplication leaks

def initialState : State graph := { State.initial input with serviceGrant := some 0 }
def initial : app.Execution := .initial app initialState

def first : app.Action := runtime.reactiveBinding leaks () 0 .int (.success 1) 0
def second : app.Action := runtime.reactiveBinding leaks () 0 .int (.success 2) 1

/-- The inclusion decision consults public traffic only. All candidate
meanings were fixed before this decision. -/
def scheduler : app.Scheduler := fun history view =>
  FinDist.pure (match history.length with
    | 0 | 1 | 2 => .activate ()
    | 3 => .include ((), if
        (view.network.pending.find? (fun message => message.id = ((), 2))).isSome then 0 else 1)
    | 4 => .application (.grant 1)
    | 5 => .activate ()
    | _ => runtime.reactiveLatest leaks 1 () view)

abbrev arena := app.protocol (FinDist.pure initialState) 7 scheduler
abbrev model := app.information (FinDist.pure initialState) 7 scheduler

def activated (execution : app.Execution) : app.Execution :=
  { execution with environmentRecall := execution.environmentRecall ++
    [⟨execution.observeEnvironment app, .activate ()⟩] }

def afterFirst (action : app.Action) : app.Execution := (activated initial).respond app () action
def afterSecond (one two : app.Action) : app.Execution :=
  (activated (afterFirst one)).respond app () two
def contested : app.Execution := afterSecond first second

private theorem activation (execution : app.Execution) :
    execution.environmentStep app (.activate ()) = FinDist.pure (activated execution) := by
  simp only [ReactiveApplication.Execution.environmentStep, app, reactiveApplication, leaks,
    FinDist.map_pure, MessageNetwork.learn_empty]
  rfl

private def extendPure (history : arena.History) (joint : Unit → Option app.Action)
    (legal : arena.Legal history.state joint) (target : arena.State)
    (law : arena.step history.state ⟨joint, legal⟩ = FinDist.pure target) : arena.History :=
  history.extend legal (by rw [law]; exact FinDist.mem_support_pure.mpr rfl)

private def setupHistory : arena.History :=
  extendPure arena.initHistory (fun _ => none)
    ⟨by change ¬ False; simp, fun _ => by change ¬ (none : Option Unit) = some _; simp⟩
    (some ⟨7, none, initial⟩) (by
      change (FinDist.pure initialState).map _ = _
      rw [FinDist.map_pure]; rfl)

private def firstActivation : arena.History :=
  extendPure setupHistory (fun _ => none)
    ⟨by change ¬ (7 = 0 ∧ _); simp, fun _ => by change ¬ (none : Option Unit) = some _; simp⟩
    (some ⟨6, some (), activated initial⟩) (by
      change (FinDist.pure (.activate () : app.Command)).bind _ = _
      rw [FinDist.pure_bind, activation, FinDist.map_pure]; rfl)

private def firstHistory (action : app.Action) : arena.History :=
  extendPure firstActivation (fun _ => some action)
    ⟨by change ¬ (6 = 0 ∧ _); simp,
      fun who => by cases who; exact ⟨rfl, Set.mem_univ _⟩⟩
    (some ⟨6, none, afterFirst action⟩) rfl

private theorem afterFirst_environment (action : app.Action) :
    (afterFirst action).environmentRecall = (activated initial).environmentRecall :=
  app.respond_environmentRecall (activated initial) () action

private def secondActivation (action : app.Action) : arena.History :=
  extendPure (firstHistory action) (fun _ => none)
    ⟨by change ¬ (6 = 0 ∧ _); simp, fun _ => by change ¬ (none : Option Unit) = some _; simp⟩
    (some ⟨5, some (), activated (afterFirst action)⟩) (by
      change (scheduler (afterFirst action).environmentRecall _).bind _ = _
      rw [afterFirst_environment]
      change (FinDist.pure (.activate () : app.Command)).bind _ = _
      rw [FinDist.pure_bind, activation, FinDist.map_pure]; rfl)

def secondHistory (one two : app.Action) : arena.History :=
  extendPure (secondActivation one) (fun _ => some two)
    ⟨by change ¬ (5 = 0 ∧ _); simp,
      fun who => by cases who; exact ⟨rfl, Set.mem_univ _⟩⟩
    (some ⟨5, none, afterSecond one two⟩) rfl

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
  history = arena.initHistory ∨ history = setupHistory ∨ history = firstActivation ∨
    (∃ action, history = firstHistory action) ∨ (∃ action, history = secondActivation action) ∨
      ∃ one two, arena.HistoryReaches (secondHistory one two) history

private theorem classified_step (history : arena.History) (classified : Classified history)
    (joint : Unit → Option app.Action) (legal : arena.Legal history.state joint)
    (target : arena.State)
    (supported : target ∈ (arena.step history.state ⟨joint, legal⟩).support) :
    Classified (history.extend legal supported) := by
  rcases classified with
    rfl | rfl | rfl | ⟨action, rfl⟩ | ⟨action, rfl⟩ | ⟨one, two, reached⟩
  · have same := inactive_joint _ joint legal (fun _ h => by cases h)
    subst joint
    exact Or.inr (Or.inl (extendPure_unique _ _ _ _ _ legal target supported))
  · have same := inactive_joint _ joint legal (fun _ h => by cases h)
    subst joint
    exact Or.inr (Or.inr (Or.inl (extendPure_unique _ _ _ _ _ legal target supported)))
  · obtain ⟨action, rfl⟩ := active_joint _ joint legal rfl
    exact Or.inr (Or.inr (Or.inr (Or.inl
      ⟨action, extendPure_unique _ _ _ _ _ legal target supported⟩)))
  · have same := inactive_joint _ joint legal (fun _ h => by cases h)
    subst joint
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨action, extendPure_unique _ _ _ _ _ legal target supported⟩))))
  · obtain ⟨next, rfl⟩ := active_joint _ joint legal rfl
    have same : (secondActivation action).extend legal supported = secondHistory action next :=
      extendPure_unique _ _ _ _ _ legal target supported
    refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨action, next, ?_⟩))))
    rw [same]
    exact ExecutionProtocol.HistoryReaches.refl arena _
  · obtain ⟨fuel, path⟩ := reached
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨one, two, fuel + 1,
      path.trans (.step joint legal supported (.refl 0 _))⟩))))

private theorem classified : ∀ {state} (trace : arena.Trace state), Classified ⟨state, trace⟩
  | _, .start => Or.inl rfl
  | _, .extend prior joint legal supported =>
      classified_step _ (classified prior) joint legal _ supported

private def actionRecall (control : app.Control) : List app.Action :=
  (control.execution.recall ()).map ReactiveApplication.PlayerEntry.action

private theorem first_actions (action : app.Action) :
    ((afterFirst action).recall ()).map ReactiveApplication.PlayerEntry.action = [action] :=
  app.respond_actions (activated initial) () action

private theorem second_actions (one two : app.Action) :
    ((afterSecond one two).recall ()).map ReactiveApplication.PlayerEntry.action = [one, two] := by
  rw [afterSecond, app.respond_actions]
  change ((afterFirst one).recall ()).map _ ++ [two] = _
  rw [first_actions]; rfl

private theorem initial_actions_recalled (one two : app.Action)
    (history : arena.History) (control : app.Control)
    (reached : arena.HistoryReaches (secondHistory one two) history)
    (stateEq : history.state = some control) : [one, two] <+: actionRecall control := by
  obtain ⟨fuel, path⟩ := reached
  have retained := app.reaches_recall_prefix (FinDist.pure initialState) 7 scheduler path
    ⟨5, none, afterSecond one two⟩ control rfl stateEq ()
  have mapped := retained.map ReactiveApplication.PlayerEntry.action
  simpa only [second_actions, actionRecall] using mapped

private theorem recalled_initial_actions_reached (one two : app.Action)
    (history : arena.History) (control : app.Control) (stateEq : history.state = some control)
    (recalled : [one, two] <+: actionRecall control) :
    arena.HistoryReaches (secondHistory one two) history := by
  have casesHistory : Classified history := classified history.trace
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
    change [one, two] <+: ((afterFirst action).recall ()).map _ at recalled
    rw [first_actions] at recalled
    have bound := recalled.length_le
    simp only [List.length_cons, List.length_nil] at bound
    omega
  · cases Option.some.inj stateEq
    change [one, two] <+: ((afterFirst action).recall ()).map _ at recalled
    rw [first_actions] at recalled
    have bound := recalled.length_le
    simp only [List.length_cons, List.length_nil] at bound
    omega
  · have actual := initial_actions_recalled a b history control reached stateEq
    have same : [one, two] = [a, b] :=
      (List.prefix_iff_eq_take.mp recalled).trans (List.prefix_iff_eq_take.mp actual).symm
    have components := List.cons.inj same
    cases components.1
    cases (List.cons.inj components.2).1
    exact reached

/-- Own response recall identifies the deterministic prefix. Every future
decision information set stays inside the resulting continuation. -/
theorem contested_isSubgameRoot : model.IsSubgameRoot (secondHistory first second) := by
  intro who inside outside reached _ insideActive _ outsideActive sameInfo
  cases who
  have controls (history : arena.History) (active : arena.active history.state ()) :
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
  exact recalled_initial_actions_reached first second outside outsideControl outsideEq
    (actionsEq ▸ initial_actions_recalled first second inside insideControl reached insideEq)

def afterAction (action : app.Action) : app.Execution :=
  (activated contested).respond app () action

/-- The application-level inclusion calculation is shared with the two-value
fixture. This projection discards private memory, which has no application effect. -/
def projectedAction (action : app.Action) : PlayerAction graph where
  memory := []
  transmission := action.transmission.map fun transmission => match transmission with
    | .submit material => .submit material
    | .replay id => .replay id

private theorem afterAction_application (action : app.Action) :
    (afterAction action).application =
      (PendingMenus.afterAction (projectedAction action)).native.application := by
  rcases action with ⟨memory, transmission⟩
  cases transmission with
  | none => rfl
  | some transmission => cases transmission <;> rfl

private theorem afterAction_pending (action : app.Action) :
    (afterAction action).network.pending =
      (PendingMenus.afterAction (projectedAction action)).native.pool.pending := by
  rcases action with ⟨memory, transmission⟩
  cases transmission with
  | none => rfl
  | some transmission =>
      cases transmission with
      | submit material => rfl
      | replay id =>
          have compare (network : MessageNetwork Unit (Payload graph))
              (pool : MessagePool Unit (Payload graph))
              (pending : network.pending = pool.pending)
              (known : (network.known ()).find? (fun envelope => envelope.id = id) =
                (pool.observe ()).known? id) :
              (network.replay () id).2.pending = (pool.replay () id).state.pending := by
            simp only [MessageNetwork.replay, MessagePool.replay, known]
            cases (pool.observe ()).known? id <;> exact pending ▸ rfl
          exact compare (activated contested).network PendingMenus.contested.native.pool rfl rfl

def selected (action : app.Action) : Nat :=
  if ((afterAction action).network.lookup ((), 2)).isSome then 0 else 1

def included (action : app.Action) : app.Execution :=
  let before := afterAction action
  { before.includePending app ((), selected action) with
    environmentRecall := before.environmentRecall ++
      [⟨before.observeEnvironment app, .include ((), selected action)⟩] }

private theorem selected_eq (action : app.Action) :
    selected action = PendingMenus.selected (projectedAction action) := by
  simp only [selected, MessageNetwork.lookup, afterAction_pending,
    PendingMenus.selected, MessagePool.lookup]
  rfl

theorem included_application (action : app.Action) : (included action).application =
    (PendingMenus.included (projectedAction action)).application := by
  have lookup : (afterAction action).network.lookup ((), selected action) =
      (PendingMenus.afterAction (projectedAction action)).native.pool.lookup
        ((), PendingMenus.selected (projectedAction action)) := by
    simp only [MessageNetwork.lookup, MessagePool.lookup, selected_eq, afterAction_pending]
    rfl
  dsimp only [included, ReactiveApplication.Execution.includePending, MessageNetwork.includePending]
  rw [lookup]
  unfold PendingMenus.included MessageApplication.includePending MessagePool.includeApplication
    MessagePool.includePending
  cases found : (PendingMenus.afterAction (projectedAction action)).native.pool.lookup
    ((), PendingMenus.selected (projectedAction action)) with
  | none => exact afterAction_application action
  | some message =>
      change (handle runtime (afterAction action).application message).getD
        (afterAction action).application = _
      rw [afterAction_application]
      dsimp only [PendingMenus.app, application]
      cases handle runtime (PendingMenus.afterAction (projectedAction action)).native.application
        message <;> rfl

/-- Every raw response, including arbitrary memory, replay, and malformed
traffic, leaves one of the two earlier commitments as the accepted binding. -/
theorem selected_binding (action : app.Action) :
    (included action).application.config.outputs 0 = some (.success
      (PendingMenus.selectedValue (projectedAction action))) := by
  rw [included_application]
  exact PendingMenus.selected_binding (projectedAction action)

end VegasTests.ReactivePendingMenus
