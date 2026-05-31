import Vegas.Examples.MessageInFlight

/-!
# Explicit protocol-message compilation bridge

This Bool fixture checks the `compile(addMessages(game))` shape for the first
runtime slice. The encoded message backend refines the explicit Bool
message-in-flight protocol while preserving protocol-level `send` and `deliver`
events. Only encoded administrative audit events are erased at this boundary.

Erasure from the explicit Bool message protocol back to the original Bool game
is handled by `Machine.messageInFlight.refinement` in
`Vegas.Examples.MessageInFlight`.
-/

namespace Vegas

open GameTheory
open Math.Probability

namespace Examples
namespace Refinement

def encodedMessageProtocolProjectState
    (state : encodedMessageInFlightMachine.State) :
    boolMessageInFlightMachine.State :=
  { source := EncodedState.project state.source,
    pending := state.pending,
    delivered := state.delivered }

def encodedMessageProtocolProjectEvent? :
    encodedMessageInFlightMachine.Event →
      Option boolMessageInFlightMachine.Event
  | .play player (.send message) =>
      some (.play player (.send message))
  | .play player (.spec action) =>
      some (.play player (.spec action))
  | .internal .deliver =>
      some (.internal .deliver)
  | .internal (.spec _event) =>
      none

def encodedMessageProtocolProjectEventBatch
    (batch : List encodedMessageInFlightMachine.Event) :
    List boolMessageInFlightMachine.Event :=
  batch.filterMap encodedMessageProtocolProjectEvent?

def encodedMessageProtocolProjectPublic
    (view : encodedMessageInFlightMachine.Public) :
    boolMessageInFlightMachine.Public :=
  (EncodedState.publicProject view.1, view.2.1, view.2.2)

def encodedMessageProtocolProjectObs
    (view : encodedMessageInFlightMachine.Obs PUnit.unit) :
    boolMessageInFlightMachine.Obs PUnit.unit :=
  (EncodedState.publicProject view.1, view.2.1, view.2.2)

set_option linter.flexible false in
theorem encodedMessageProtocol_step_project
    (event : encodedMessageInFlightMachine.Event)
    (state : encodedMessageInFlightMachine.State) :
    PMF.map encodedMessageProtocolProjectState
        (encodedMessageInFlightMachine.step event state) =
      match encodedMessageProtocolProjectEvent? event with
      | some specEvent =>
          boolMessageInFlightMachine.step specEvent
            (encodedMessageProtocolProjectState state)
      | none =>
          PMF.pure (encodedMessageProtocolProjectState state) := by
  rcases state with ⟨encodedState, pending, delivered⟩
  rcases encodedState with ⟨payload, audit⟩
  cases event with
  | play player action =>
      cases action with
      | send message =>
          simp [encodedMessageProtocolProjectState,
            encodedMessageProtocolProjectEvent?,
            encodedMessageInFlightMachine, boolMessageInFlightMachine,
            Machine.messageInFlight, Machine.step]
          rw [PMF.pure_map]
          rfl
      | spec action =>
          cases action
          · let restoreImpl
                (sourceValue : EncodedState) :
                encodedMessageInFlightMachine.State :=
              { source := sourceValue,
                pending := pending,
                delivered := delivered }
            let restoreSpec
                (sourceValue : Option Bool) :
                boolMessageInFlightMachine.State :=
              { source := sourceValue,
                pending := pending,
                delivered := delivered }
            change
              PMF.map encodedMessageProtocolProjectState
                  (PMF.map restoreImpl
                    (PMF.pure
                      ({ payload := some 0, audit := audit } :
                        EncodedState))) =
                PMF.map restoreSpec (PMF.pure (some false))
            rw [PMF.map_comp]
            rw [PMF.pure_map
              (f := encodedMessageProtocolProjectState ∘ restoreImpl)]
            rw [PMF.pure_map (f := restoreSpec)]
            change
              PMF.pure
                  (encodedMessageProtocolProjectState
                    (restoreImpl { payload := some 0, audit := audit })) =
                PMF.pure (restoreSpec (some false))
            rfl
          · let restoreImpl
                (sourceValue : EncodedState) :
                encodedMessageInFlightMachine.State :=
              { source := sourceValue,
                pending := pending,
                delivered := delivered }
            let restoreSpec
                (sourceValue : Option Bool) :
                boolMessageInFlightMachine.State :=
              { source := sourceValue,
                pending := pending,
                delivered := delivered }
            change
              PMF.map encodedMessageProtocolProjectState
                  (PMF.map restoreImpl
                    (PMF.pure
                      ({ payload := some 1, audit := audit } :
                        EncodedState))) =
                PMF.map restoreSpec (PMF.pure (some true))
            rw [PMF.map_comp]
            rw [PMF.pure_map
              (f := encodedMessageProtocolProjectState ∘ restoreImpl)]
            rw [PMF.pure_map (f := restoreSpec)]
            change
              PMF.pure
                  (encodedMessageProtocolProjectState
                    (restoreImpl { payload := some 1, audit := audit })) =
                PMF.pure (restoreSpec (some true))
            rfl
  | internal event =>
      cases event with
      | deliver =>
          cases pending with
          | nil =>
              simp [encodedMessageProtocolProjectState,
                encodedMessageProtocolProjectEvent?,
                encodedMessageInFlightMachine, boolMessageInFlightMachine,
                Machine.messageInFlight, Machine.step]
              rw [PMF.pure_map]
              rfl
          | cons message rest =>
              simp [encodedMessageProtocolProjectState,
                encodedMessageProtocolProjectEvent?,
                encodedMessageInFlightMachine, boolMessageInFlightMachine,
                Machine.messageInFlight, Machine.step]
              rw [PMF.pure_map]
              rfl
      | spec event =>
          cases payload <;>
            simp [encodedMessageProtocolProjectState,
              encodedMessageProtocolProjectEvent?,
              encodedMessageInFlightMachine, boolMessageInFlightMachine,
              Machine.messageInFlight, encodedImplMachine,
              EncodedState.project, Machine.step] <;>
            rw [PMF.pure_map, PMF.pure_map] <;>
            rfl

theorem encodedMessageProtocol_runEventsFrom_project_eq
    (events : List encodedMessageInFlightMachine.Event)
    (state : encodedMessageInFlightMachine.State) :
    PMF.map encodedMessageProtocolProjectState
        (encodedMessageInFlightMachine.runEventsFrom events state) =
      boolMessageInFlightMachine.runEventsFrom
        (encodedMessageProtocolProjectEventBatch events)
        (encodedMessageProtocolProjectState state) := by
  induction events generalizing state with
  | nil =>
      change
        PMF.map encodedMessageProtocolProjectState (PMF.pure state) =
          PMF.pure (encodedMessageProtocolProjectState state)
      rw [PMF.pure_map]
  | cons event events ih =>
      rw [Machine.runEventsFrom_cons_bind]
      rw [PMF.map_bind]
      simp_rw [ih]
      change
        (encodedMessageInFlightMachine.step event state).bind
            ((fun specState =>
                boolMessageInFlightMachine.runEventsFrom
                  (encodedMessageProtocolProjectEventBatch events)
                  specState) ∘
              encodedMessageProtocolProjectState) =
          boolMessageInFlightMachine.runEventsFrom
            (encodedMessageProtocolProjectEventBatch (event :: events))
            (encodedMessageProtocolProjectState state)
      rw [← PMF.bind_map
        (p := encodedMessageInFlightMachine.step event state)
        (f := encodedMessageProtocolProjectState)
        (q := fun specState =>
          boolMessageInFlightMachine.runEventsFrom
            (encodedMessageProtocolProjectEventBatch events) specState)]
      rw [encodedMessageProtocol_step_project event state]
      cases hproject : encodedMessageProtocolProjectEvent? event with
      | none =>
          simp [encodedMessageProtocolProjectEventBatch, hproject,
            PMF.pure_bind]
      | some specEvent =>
          simp [encodedMessageProtocolProjectEventBatch, hproject,
            Machine.runEventsFrom_cons_bind]

/-- In this Bool fixture, compiling after adding explicit protocol messages
preserves the protocol-level message boundary: send/deliver survive projection,
while encoded audit events are administrative. -/
noncomputable def encodedMessageProtocolRefinement :
    Machine.StochasticRefinement encodedMessageInFlightMachine
      boolMessageInFlightMachine where
  projectState := encodedMessageProtocolProjectState
  projectEvent? := encodedMessageProtocolProjectEvent?
  projectEventBatch := encodedMessageProtocolProjectEventBatch
  projectPublic := encodedMessageProtocolProjectPublic
  projectObs := fun _ => encodedMessageProtocolProjectObs
  projectOutcome := decodeNat
  init_project := rfl
  available_project := by
    intro state event specEvent havailable hproject
    rcases state with ⟨encodedState, pending, delivered⟩
    rcases encodedState with ⟨payload, audit⟩
    cases event with
    | play player action =>
        cases action with
        | send message =>
            cases hproject
            change ¬ encodedImplMachine.terminal
                { payload := payload, audit := audit } at havailable
            change ¬ boolSpecMachine.terminal
              (EncodedState.project { payload := payload, audit := audit })
            intro hterminal
            exact havailable (encodedRefinement.terminal_reflect hterminal)
        | spec action =>
            cases hproject
            change action ∈
              encodedImplMachine.available
                { payload := payload, audit := audit } player at havailable
            change action ∈
              boolSpecMachine.available
                (EncodedState.project { payload := payload, audit := audit })
                player
            exact
              encodedRefinement.available_project
                (event := .play player action) havailable rfl
    | internal event =>
        cases event with
        | deliver =>
            cases hproject
            rcases havailable with ⟨hpending, hnonterminal⟩
            change Machine.MessageInFlightInternal.deliver ∈
              boolMessageInFlightMachine.availableInternal
                { source := EncodedState.project
                    { payload := payload, audit := audit },
                  pending := pending, delivered := delivered }
            constructor
            · exact hpending
            · intro hterminal
              exact hnonterminal
                (encodedRefinement.terminal_reflect hterminal)
        | spec event =>
            simp [encodedMessageProtocolProjectEvent?] at hproject
  step_project := by
    intro event source
    cases hproject : encodedMessageProtocolProjectEvent? event with
    | none =>
        rw [encodedMessageProtocol_step_project event source]
        simp [hproject]
    | some specEvent =>
        rw [encodedMessageProtocol_step_project event source]
        simp [hproject]
  eventBatch_project := by
    intro events source
    exact encodedMessageProtocol_runEventsFrom_project_eq events source
  publicView_project := by
    intro state
    rcases state with ⟨encodedState, pending, delivered⟩
    rcases encodedState with ⟨payload, audit⟩
    rfl
  observe_project := by
    intro player state
    cases player
    rcases state with ⟨encodedState, pending, delivered⟩
    rcases encodedState with ⟨payload, audit⟩
    rfl
  terminal_project := by
    intro state hterminal
    exact encodedRefinement.terminal_project hterminal
  terminal_reflect := by
    intro state hterminal
    exact encodedRefinement.terminal_reflect hterminal
  outcome_project := by
    intro state
    rcases state with ⟨encodedState, pending, delivered⟩
    exact encodedRefinement.outcome_project encodedState
  utility_project := by
    intro outcome player
    exact encodedRefinement.utility_project outcome player

noncomputable def encodedMessageProtocolLawLift :
    encodedMessageProtocolRefinement.EventBatchLawFamilyLift
      (fun _ : PUnit => Bool × Bool)
      boolMessageInFlightLawFamily where
  impl := encodedMessageInFlightLawFamily
  compatible := by
    intro profile trace
    rcases trace with ⟨batches, state⟩
    rcases state with ⟨encodedState, pending, delivered⟩
    cases pending with
    | nil =>
        change
          PMF.map encodedMessageProtocolProjectEventBatch
              (PMF.pure
                [.play PUnit.unit (.send (profile PUnit.unit).1),
                  .internal .deliver,
                  .internal (.spec PUnit.unit),
                  .play PUnit.unit (.spec (profile PUnit.unit).2)]) =
            PMF.pure
              [.play PUnit.unit (.send (profile PUnit.unit).1),
                .internal .deliver,
                .play PUnit.unit (.spec (profile PUnit.unit).2)]
        rw [PMF.pure_map]
        rfl
    | cons old rest =>
        change
          PMF.map encodedMessageProtocolProjectEventBatch
              (PMF.pure
                [.play PUnit.unit (.send (profile PUnit.unit).1),
                  .internal (.spec PUnit.unit),
                  .play PUnit.unit (.spec (profile PUnit.unit).2)]) =
            PMF.pure
              [.play PUnit.unit (.send (profile PUnit.unit).1),
                .play PUnit.unit (.spec (profile PUnit.unit).2)]
        rw [PMF.pure_map]
        rfl

noncomputable def encodedMessageProtocolErasureRefinement :
    Machine.StochasticRefinement encodedMessageInFlightMachine
      boolSpecMachine :=
  boolMessageInFlightRefinement.compose encodedMessageProtocolRefinement

noncomputable def encodedMessageProtocolErasureLawLift :
    encodedMessageProtocolErasureRefinement.EventBatchLawFamilyLift
      (fun _ : PUnit => Bool × Bool)
      boolMessageSpecInertLawFamily.enriched :=
  Machine.StochasticRefinement.EventBatchLawFamilyLift.compose
    boolMessageInFlightLawLift
    encodedMessageProtocolLawLift

example (state : encodedMessageInFlightMachine.State) :
    encodedMessageProtocolErasureRefinement.projectState state =
      encodedMessageInFlightComposedRefinement.projectState state := by
  rfl

example (event : encodedMessageInFlightMachine.Event) :
    encodedMessageProtocolErasureRefinement.projectEvent? event =
      encodedMessageInFlightComposedRefinement.projectEvent? event := by
  cases event with
  | play player action =>
      cases action <;> rfl
  | internal event =>
      cases event <;> rfl

example (message action : Bool) :
    encodedMessageProtocolRefinement.projectEventBatch
        [.play PUnit.unit (.send message),
          .internal .deliver,
          .internal (.spec PUnit.unit),
          .play PUnit.unit (.spec action)] =
      [.play PUnit.unit (.send message),
        .internal .deliver,
        .play PUnit.unit (.spec action)] := by
  rfl

example (message action : Bool) :
    encodedMessageProtocolErasureRefinement.projectEventBatch
        [.play PUnit.unit (.send message),
          .internal .deliver,
          .internal (.spec PUnit.unit),
          .play PUnit.unit (.spec action)] =
      encodedMessageInFlightComposedRefinement.projectEventBatch
        [.play PUnit.unit (.send message),
          .internal .deliver,
          .internal (.spec PUnit.unit),
          .play PUnit.unit (.spec action)] := by
  rfl

example (profile : ∀ _player : PUnit, Bool × Bool) :
    PMF.map encodedMessageProtocolRefinement.projectEventBatchTrace
        ((Machine.eventBatchTraceKernelGame
            encodedMessageInFlightMachine
            (fun _ : PUnit => Bool × Bool)
            encodedMessageProtocolLawLift.impl
            (fun _ => 0) 3).outcomeKernel profile) =
      ((Machine.eventBatchTraceKernelGame
          boolMessageInFlightMachine (fun _ : PUnit => Bool × Bool)
          boolMessageInFlightLawFamily
          (fun _ => 0) 3).outcomeKernel profile) :=
  encodedMessageProtocolRefinement.eventBatchTraceKernelGame_projectTrace_eq
    encodedMessageProtocolLawLift (fun _ => 0) 3 profile

example (profile : ∀ _player : PUnit, Bool × Bool) :
    PMF.map encodedMessageProtocolErasureRefinement.projectEventBatchTrace
        ((Machine.eventBatchTraceKernelGame
            encodedMessageInFlightMachine
            (fun _ : PUnit => Bool × Bool)
            encodedMessageProtocolErasureLawLift.impl
            (fun _ => 0) 3).outcomeKernel profile) =
      ((Machine.eventBatchTraceKernelGame
          boolSpecMachine (fun _ : PUnit => Bool × Bool)
          boolMessageSpecInertLawFamily.enriched
          (fun _ => 0) 3).outcomeKernel profile) :=
  encodedMessageProtocolErasureRefinement
    |>.eventBatchTraceKernelGame_projectTrace_eq
      encodedMessageProtocolErasureLawLift (fun _ => 0) 3 profile

theorem boolMessageInFlight_inertMessage_true_nash (message : Bool) :
    (Machine.eventBatchTraceKernelGame
        boolMessageInFlightMachine (fun _ : PUnit => Bool × Bool)
        boolMessageInFlightLawFamily (fun _ => 0) 3).IsNash
      (fun _ : PUnit => (message, true)) := by
  exact
    boolMessageInFlightRefinement
      |>.eventBatchTraceKernelGame_nash_pullback_of_inert_projected_nash
        boolMessageSpecInertLawFamily boolMessageInFlightLawLift
        (fun _ => 0) 3
        (CImpl := fun _ => 1) (CSpec := fun _ => 1)
        boolMessageInFlightTraceUtility_bound boolSpecTraceUtility_bound
        boolSpecTraceGame_true_nash_three

theorem encodedMessageProtocol_inertMessage_true_nash (message : Bool) :
    (Machine.eventBatchTraceKernelGame
        encodedMessageInFlightMachine (fun _ : PUnit => Bool × Bool)
        encodedMessageProtocolLawLift.impl (fun _ => 0) 3).IsNash
      (fun _ : PUnit => (message, true)) := by
  exact
    encodedMessageProtocolRefinement
      |>.eventBatchTraceKernelGame_nash_pullback_of_bounded
        encodedMessageProtocolLawLift
        (fun _ => 0) 3
        (CImpl := fun _ => 1) (CSpec := fun _ => 1)
        encodedMessageInFlightTraceUtility_bound
        boolMessageInFlightTraceUtility_bound
        (boolMessageInFlight_inertMessage_true_nash message)

end Refinement
end Examples
end Vegas
