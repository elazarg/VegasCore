/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import VegasTests.MonitoredGuessingNativeResolution

/-! # Protected inclusion of the initialized commitments' ordinary openings -/

noncomputable section

namespace VegasTests.MonitoredGuessing

open Vegas Vegas.EventGraphRuntime Interaction GameTheory.Math.Probability

def resolutionValue (bit : Bool) (event : nativeGraph.EventId) : Bool :=
  if event = bobPublication then true else bit

def resolutionHandle (event : nativeGraph.EventId) : Handle nativeGraph :=
  if event = bobPublication then bobHandle else aliceHandle

def resolutionRef (event : nativeGraph.EventId) :
    EventGraph.FieldRef nativeGraph.layout (.publication .bool) :=
  ⟨.inr event, by fin_cases event <;> rfl⟩

theorem resolution_opening_accepted (bit : Bool) (state : State nativeGraph)
    (valid : NativeFixed bit state) (event : nativeGraph.EventId)
    (ready : state.config.cut.Ready event) (timely : state.WithinDeadline nativeRuntime event)
    (serial : Nat) :
    ∃ next, handle nativeRuntime state
        ⟨(nativeOwner event, serial), .opening event (resolutionHandle event)
          ⟨.bool, resolutionValue bit event⟩⟩ = some next ∧
      (resolutionRef event).get? next.config.store = some (.success (resolutionValue bit event)) :=
    by
  fin_cases event
  · refine ⟨_, handle_opening_eq nativeRuntime state (bob, serial) bobPublication bobHandle
      bob .bool bobBindingRef [] rfl rfl bob_node ready timely rfl rfl valid.2.2.2
      true valid.bob_candidate valid.bob_stored (.success true) ?_, ?_⟩
    · simp only [EventGraph.EventCode.resolveOutput?, valid.bob_stored]
      rfl
    · simp [resolutionRef, resolutionValue, bobPublication, State.complete,
        EventGraph.Config.store, EventGraph.FieldRef.get?]
  · refine ⟨_, handle_opening_eq nativeRuntime state (alice, serial) alicePublication aliceHandle
      alice .bool aliceBindingRef [] rfl rfl alice_node ready timely rfl rfl valid.2.2.1
      bit valid.alice_candidate valid.alice_stored (.success bit) ?_, ?_⟩
    · simp only [EventGraph.EventCode.resolveOutput?, valid.alice_stored]
      rfl
    · simp [resolutionRef, resolutionValue, bobPublication, State.complete,
        EventGraph.Config.store, EventGraph.FieldRef.get?]

theorem resolution_withhold_accepted (state : State nativeGraph)
    (ready : state.config.cut.Ready bobPublication)
    (timely : state.WithinDeadline nativeRuntime bobPublication)
    (remembered : state.remembered bobPublication = none) (serial : Nat) :
    ∃ next, handle nativeRuntime state ⟨(bob, serial), .withhold bobPublication⟩ = some next ∧
      bobPublicationRef.get? next.config.store = some .failure := by
  refine ⟨_, handle_withhold_unremembered_eq nativeRuntime state (bob, serial) bobPublication
    bob .bool bobBindingRef [] rfl rfl bob_node ready timely rfl remembered, ?_⟩
  simp [bobPublicationRef, State.complete, EventGraph.Config.store, EventGraph.FieldRef.get?]

/-- The exact application and receipt law for a fresh canonical submission.
Any earlier pending envelopes are allowed; reserved selection chooses this
new addressed envelope. The unchanged-application premise is discharged by
ordinary opening and withholding responses below. -/
theorem resolution_submission_inclusion (players : Player → nativeApp.Policy)
    (execution : nativeApp.Execution) (who : Player) (event : nativeGraph.EventId)
    (submission : WitnessedSubmission nativeGraph) (next : State nativeGraph)
    (serials : execution.network.SerialsBeforeNext)
    (addressed : submission.call.packet.event? nativeGraph = some event)
    (unchanged : (execution.respond nativeApp who ⟨some (.submit submission)⟩).application =
      execution.application)
    (accepted : handle nativeRuntime execution.application
      ⟨(who, execution.network.nextSerial who), submission.call.packet⟩ = some next) :
    (nativeRuntime.interactionStep nativeLeaks players nativeNetwork (.includeLatest event who)
      (execution.respond nativeApp who ⟨some (.submit submission)⟩)).map
        (fun result => (result.application, result.receipts)) =
      FinDist.pure
        (next, execution.receipts ++ [((who, execution.network.nextSerial who), true)]) :=
    by
  have selected := nativeRuntime.reactiveLatest_after_submit nativeLeaks who event execution
    serials submission addressed
  simp only [interactionStep, interactionInstruction, selected, FinDist.pure_bind,
    ReactiveApplication.dispatch, ReactiveApplication.Execution.environmentStep,
    FinDist.map_pure, ReactiveApplication.Command.actor?, ReactiveApplication.resume]
  have lookup : (execution.respond nativeApp who ⟨some (.submit submission)⟩).network.lookup
      (who, execution.network.nextSerial who) =
      some ⟨(who, execution.network.nextSerial who),
        submission.emit (execution.respond nativeApp who ⟨some (.submit submission)⟩).application
          who (execution.network.known who)⟩ := serials.lookup_submit who _
  unfold ReactiveApplication.Execution.includePending MessageNetwork.includePending
  rw [lookup]
  change FinDist.pure
    (((handle nativeRuntime
      (execution.respond nativeApp who ⟨some (.submit submission)⟩).application
      ⟨(who, execution.network.nextSerial who), submission.call.packet⟩).getD
        (execution.respond nativeApp who ⟨some (.submit submission)⟩).application),
      (execution.respond nativeApp who ⟨some (.submit submission)⟩).receipts ++
        [((who, execution.network.nextSerial who), (handle nativeRuntime
          (execution.respond nativeApp who ⟨some (.submit submission)⟩).application
          ⟨(who, execution.network.nextSerial who), submission.call.packet⟩).isSome)]) = _
  rw [unchanged, accepted, nativeApp.respond_receipts]
  rfl

theorem resolution_opening_inclusion (players : Player → nativeApp.Policy)
    (execution : nativeApp.Execution) (who : Player) (event : nativeGraph.EventId)
    (candidate : Handle nativeGraph) (bit : Bool) (next : State nativeGraph)
    (serials : execution.network.SerialsBeforeNext)
    (accepted : handle nativeRuntime execution.application
      ⟨(who, execution.network.nextSerial who), .opening event candidate ⟨.bool, bit⟩⟩ =
        some next) :
    (nativeRuntime.interactionStep nativeLeaks players nativeNetwork (.includeLatest event who)
      (execution.respond nativeApp who (nativeOpeningAction event candidate bit))).map
        (fun result => (result.application, result.receipts)) =
      FinDist.pure
        (next, execution.receipts ++ [((who, execution.network.nextSerial who), true)]) :=
  resolution_submission_inclusion players execution who event _ next serials rfl rfl accepted

theorem resolution_withhold_inclusion (players : Player → nativeApp.Policy)
    (execution : nativeApp.Execution) (next : State nativeGraph)
    (serials : execution.network.SerialsBeforeNext)
    (accepted : handle nativeRuntime execution.application
      ⟨(bob, execution.network.nextSerial bob), .withhold bobPublication⟩ = some next) :
    (nativeRuntime.interactionStep nativeLeaks players nativeNetwork
      (.includeLatest bobPublication bob)
      (execution.respond nativeApp bob (nativeGuessAction false))).map
        (fun result => (result.application, result.receipts)) =
      FinDist.pure
        (next, execution.receipts ++ [((bob, execution.network.nextSerial bob), true)]) :=
  resolution_submission_inclusion players execution bob bobPublication _ next serials rfl rfl
    accepted

theorem rejectedAlice_accepted (receipts : List (MessageId Player × Bool))
    (id : MessageId Player) :
    rejectedAlice (receipts ++ [(id, true)]) = rejectedAlice receipts := by
  simp [rejectedAlice]

end VegasTests.MonitoredGuessing
