/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import VegasTests.PendingMenusSource
import Vegas.Pending.ReactiveServiceProgress
import Vegas.Pending.ReactiveSafety
import Interaction.ReactiveSubgamePrefix

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

/-- Only the initial two scheduling decisions constrain the subgame-root proof. -/
def responsePrefix : app.TwoResponsePrefix where
  initialState := initialState
  remaining := 5
  scheduler := scheduler
  schedules history view early := by
    have casesLength : history.length = 0 ∨ history.length = 1 := by omega
    rcases casesLength with zero | one
    · simp only [scheduler, zero]
    · simp only [scheduler, one]
  activation execution := by
    simp only [ReactiveApplication.Execution.environmentStep, app, reactiveApplication, leaks,
      FinDist.map_pure, MessageNetwork.learn_empty]

abbrev activated := responsePrefix.activated
abbrev afterFirst := responsePrefix.afterFirst
abbrev afterSecond := responsePrefix.afterSecond
abbrev secondHistory := responsePrefix.secondHistory

def contested : app.Execution := afterSecond first second

theorem activation (execution : app.Execution) :
    execution.environmentStep app (.activate ()) = FinDist.pure (activated execution) :=
  responsePrefix.activation execution

/-- Recall identifies this prefix inside every future decision information set. -/
theorem contested_isSubgameRoot : model.IsSubgameRoot (secondHistory first second) :=
  responsePrefix.secondHistory_isSubgameRoot first second

def afterAction (action : app.Action) : app.Execution :=
  (activated contested).respond app () action

/-- The application-level inclusion calculation is shared with the two-value
fixture. The command-service projection uses empty auxiliary memory. -/
def projectedAction (action : app.Action) : PlayerAction graph where
  memory := []
  transmission := action.transmission.map fun transmission => match transmission with
    | .submit material => .submit material
    | .replay id => .replay id

private theorem afterAction_application (action : app.Action) :
    (afterAction action).application =
      (PendingMenus.afterAction (projectedAction action)).native.application := by
  rcases action with ⟨transmission⟩
  cases transmission with
  | none => rfl
  | some transmission => cases transmission <;> rfl

private theorem afterAction_pending (action : app.Action) :
    (afterAction action).network.pending =
      (PendingMenus.afterAction (projectedAction action)).native.pool.pending := by
  rcases action with ⟨transmission⟩
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
