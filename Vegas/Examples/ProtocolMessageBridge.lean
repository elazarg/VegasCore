import Vegas.Examples.MessageInFlight

/-!
# Explicit protocol-message compilation bridge

Property boundary: this file proves preservation of the explicit message
protocol boundary under compilation, not that erased messages are strategically
irrelevant.

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

/-- In this Bool fixture, compiling after adding explicit protocol messages
preserves the protocol-level message boundary: send/deliver survive projection,
while encoded audit events are administrative. -/
noncomputable def encodedMessageProtocolRefinement :
    Machine.StochasticRefinement encodedMessageInFlightMachine
      boolMessageInFlightMachine :=
  Machine.messageInFlight.mapRefinement
    (fun _ : PUnit => Bool) encodedRefinement

noncomputable def encodedMessageProtocolProjectState :
    encodedMessageInFlightMachine.State →
      boolMessageInFlightMachine.State :=
  encodedMessageProtocolRefinement.projectState

noncomputable def encodedMessageProtocolProjectEvent? :
    encodedMessageInFlightMachine.Event →
      Option boolMessageInFlightMachine.Event :=
  encodedMessageProtocolRefinement.projectEvent?

noncomputable def encodedMessageProtocolProjectEventBatch :
    List encodedMessageInFlightMachine.Event →
      List boolMessageInFlightMachine.Event :=
  encodedMessageProtocolRefinement.projectEventBatch

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
