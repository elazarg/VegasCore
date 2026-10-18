/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedSignallingFinishedOwner
import Vegas.Examples.CommitSeedSignallingProtectedTail
import Vegas.Examples.CommitSeedSignallingCalendarClocks
import Vegas.Examples.CommitSeedSignallingSubmissionShape
import Interaction.ReactiveInvariantPrefix

/-! # Survival along the original trace after a successful publication response -/

noncomputable section

namespace Vegas.Examples.CommitSeedSignalling

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Protocol.InformationModel
  GameTheory.Math.Probability GameTheory.Enforcement
open OnePacketCommitRevealHypotheses (Player alice bob setup program)

private theorem family_tail_ready_timely (seed : Seeds) (remaining : Nat)
    (execution : app.Execution) (owner : Player)
    (trace : (countedMenu.protocol initial horizon (family seed)).Trace
      (some ⟨remaining, some owner, execution⟩))
    (coordinate : CommitAttemptEvent graph) (retired : coordinate.attempt ≠ originalAttempt)
    (request : execution.application.SeedRequest owner coordinate) :
    execution.application.current.native.WithinDeadline runtime coordinate.event := by
  have clocks := tail_service_clocks countedMenu
    (PhaseCount.silence_onePacket runtime leaks bounds) seed
      ⟨remaining, some owner, execution⟩ trace owner rfl coordinate retired request
  have current : (PhaseSeedScheduler.informationInput runtime leaks coordinate owner
      (execution.recall owner) (execution.observe app owner)).elapsed ∈
      PhaseSeedScheduler.serviceClocks runtime leaks coordinate owner
        (execution.recall owner) (execution.observe app owner) := by
    change _ ∈ _ ++ [_]
    exact List.mem_append_right _ (List.mem_singleton_self _)
  rw [clocks] at current
  have zero := List.mem_singleton.mp current
  have valid := raw_native_valid (family seed) ⟨remaining, some owner, execution⟩
    (countedMenu.toRawTrace initial horizon (family seed) trace)
  obtain ⟨entered, found⟩ := Option.isSome_iff_exists.mp
    ((valid.active.activated_iff coordinate.event).mpr
      ⟨request.2.2.1, by simp only [request.2.2.2.1, Option.isSome_some]⟩)
  change execution.application.current.native.clock -
    (execution.application.current.native.activatedAt coordinate.event).getD
      execution.application.current.native.clock = 0 at zero
  rw [found, Option.getD_some] at zero
  rw [State.WithinDeadline, found]
  change execution.application.current.native.clock - entered < 6
  omega

private theorem publication_inclusion_finished
    (selected : app.Scheduler) (remaining : Nat) (execution : app.Execution) (owner : Player)
    (trace : (countedMenu.protocol initial horizon selected).Trace
      (some ⟨remaining + 1, some owner, execution⟩))
    (request : execution.application.SeedRequest owner
      ⟨execution.application.attempt, revealEvent owner⟩)
    (value : Bool)
    (stored : execution.application.current.native.config.store (.inr (bindingEvent owner)) =
      some (cast (congrArg EventField.Value (bindingEvent_layout owner).symm)
        (PublicationResult.success value)))
    (timely : execution.application.current.native.WithinDeadline runtime
      (revealEvent owner))
    (material : WitnessedSubmission graph)
    (offered : (⟨some material⟩ : (phaseApplication runtime leaks).Action) ∈
      (PhaseCount.onePacketMenu runtime leaks bounds).actions owner (execution.recall owner)
        (execution.observe (phaseApplication runtime leaks) owner))
    (postTrace : (countedMenu.protocol initial horizon selected).Trace
      (some ⟨remaining + 1, none, execution.respond app owner ⟨some material⟩⟩))
    (next : app.Execution)
    (included : next ∈ ((execution.respond app owner ⟨some material⟩).environmentStep app
      (.include (owner, execution.network.nextSerial owner))).support) :
    next.application.phases <:+ [publicationPhase] ∧
      (∀ event, graph.actor? event = some owner →
        event ∈ next.application.current.native.config.cut.completed) ∧
      owner ∉ next.application.current.excluded := by
  obtain ⟨candidate, rawValue, packet⟩ :=
    counted_submission_opening_shape selected (remaining + 1) execution owner trace request
      material offered
  let after := execution.respond app owner ⟨some material⟩
  have application : after.application = execution.application := by
    rcases material with ⟨⟨call, preparation⟩, evidence⟩
    dsimp only at packet
    subst call
    rfl
  let message : Message Player (CommitAttemptPacket graph) :=
    ⟨(owner, execution.network.nextSerial owner), app.packet after.application owner
      (execution.network.known owner) material⟩
  have attempt : message.payload.attempt = execution.application.attempt := by
    change after.application.attempt = execution.application.attempt
    rw [application]
  have call : message.payload.packet.call = .opening (revealEvent owner) candidate rawValue := by
    change (after.application.emit owner (execution.network.known owner) material).packet.call = _
    simp only [PhaseRuntimeState.emit, RecoveryState.emit]
    split <;> split <;> exact packet
  have member : message ∈ after.network.inputs :=
    List.mem_append_right _ (List.mem_singleton_self _)
  have serials := app.serialsBeforeNext_history selected initial horizon
    (countedMenu.toRawTrace initial horizon selected trace)
  have lookup : after.network.lookup message.id = some message := serials.lookup_submit owner
    (app.packet after.application owner (execution.network.known owner) material)
  have actualRequest : after.application.SeedRequest message.sender
      ⟨message.payload.attempt, revealEvent owner⟩ := by
    change after.application.SeedRequest owner _
    rw [application, attempt]
    exact request
  have afterTimely : after.application.current.native.WithinDeadline runtime
      (revealEvent owner) := by rwa [application]
  have afterStored : after.application.current.native.config.store (.inr (bindingEvent owner)) =
      some (cast (congrArg EventField.Value (bindingEvent_layout owner).symm)
        (PublicationResult.success value)) := by rwa [application]
  exact counted_successful_opening_finished selected ⟨remaining + 1, none, after⟩ postTrace
    owner message member lookup candidate rawValue call actualRequest afterTimely value afterStored
      next included

/-- A genuine admitted opening at a successful tail publication protects its
owner at every later prefix of the same original history. Its actual timely
request and next inclusion command feed the native finished-owner invariant,
without a newly selected future policy. -/
theorem publication_after_submission_survives
    (selected : app.Scheduler) (remaining : Nat) (execution : app.Execution) (owner : Player)
    (sourceTrace : (countedMenu.protocol initial horizon selected).Trace
      (some ⟨remaining, some owner, execution⟩))
    (request : execution.application.SeedRequest owner
      ⟨execution.application.attempt, revealEvent owner⟩)
    (value : Bool)
    (stored : execution.application.current.native.config.store (.inr (bindingEvent owner)) =
      some (cast (congrArg EventField.Value (bindingEvent_layout owner).symm)
        (PublicationResult.success value)))
    (material : WitnessedSubmission graph)
    (offered : (⟨some material⟩ : (phaseApplication runtime leaks).Action) ∈
      (PhaseCount.onePacketMenu runtime leaks bounds).actions owner (execution.recall owner)
        (execution.observe (phaseApplication runtime leaks) owner))
    (timely : execution.application.current.native.WithinDeadline runtime
      (revealEvent owner))
    (scheduled : selected (execution.respond app owner ⟨some material⟩).environmentRecall
      ((execution.respond app owner ⟨some material⟩).observeEnvironment app) =
        PMF.pure (.include (owner, execution.network.nextSerial owner)))
    (postTrace : (countedMenu.protocol initial horizon selected).Trace
      (some ⟨remaining, none, execution.respond app owner ⟨some material⟩⟩))
    (final : app.Control)
    (trace : (countedMenu.protocol initial horizon selected).Trace (some final))
    (kept : TracePrefix postTrace trace) :
    owner ∉ final.execution.application.current.excluded := by
  let after := execution.respond app owner ⟨some material⟩
  let start : app.Control := ⟨remaining, none, after⟩
  have path := kept.reachesWithin
  rcases path.eq_or_step with equal | ⟨joint, legal, reached, supported, _fuel, suffix⟩
  · have same : start = final :=
      Option.some.inj (congrArg History.state equal)
    subst final
    exact request.2.2.2.2
  · have moved : reached ∈
        (app.transition initial horizon selected (some start) joint).support := supported
    obtain ⟨middle, stateEq, _retained⟩ :=
      app.transition_recall_prefix initial horizon selected start reached joint moved
    subst reached
    cases remaining with
    | zero => exact (legal.1 ⟨rfl, rfl⟩).elim
    | succ remaining =>
        obtain ⟨command, chosen, commandMoved⟩ :=
          Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ moved)
        change command ∈ (selected after.environmentRecall
          (after.observeEnvironment app)).support at chosen
        rw [scheduled, PMF.mem_support_pure_iff] at chosen
        subst command
        obtain ⟨result, included, exactControl⟩ := PMF.support_map .. ▸ commandMoved
        cases Option.some.inj exactControl
        have finished := publication_inclusion_finished selected remaining execution owner
          sourceTrace request value stored timely material offered postTrace result included
        have preserved := (finished_owner_invariant owner).reaches initial horizon selected
          (countedMenu.reaches_raw initial horizon selected suffix)
          ⟨remaining, none, result⟩ final rfl rfl finished
        exact preserved.2.2

/-- The original fixed-family callback supplies both its actual timely request and
its next inclusion command to the same retained-trace survival proof. -/
theorem family_publication_after_submission_survives
    (seed : Seeds) (remaining : Nat) (execution : app.Execution) (owner : Player)
    (sourceTrace : (countedMenu.protocol initial horizon (family seed)).Trace
      (some ⟨remaining, some owner, execution⟩))
    (retired : execution.application.attempt ≠ originalAttempt)
    (request : execution.application.SeedRequest owner
      ⟨execution.application.attempt, revealEvent owner⟩)
    (value : Bool)
    (stored : execution.application.current.native.config.store (.inr (bindingEvent owner)) =
      some (cast (congrArg EventField.Value (bindingEvent_layout owner).symm)
        (PublicationResult.success value)))
    (material : WitnessedSubmission graph)
    (offered : (⟨some material⟩ : (phaseApplication runtime leaks).Action) ∈
      (PhaseCount.onePacketMenu runtime leaks bounds).actions owner (execution.recall owner)
        (execution.observe (phaseApplication runtime leaks) owner))
    (postTrace : (countedMenu.protocol initial horizon (family seed)).Trace
      (some ⟨remaining, none, execution.respond app owner ⟨some material⟩⟩))
    (final : app.Control)
    (trace : (countedMenu.protocol initial horizon (family seed)).Trace (some final))
    (kept : TracePrefix postTrace trace) :
    owner ∉ final.execution.application.current.excluded := by
  have timely := family_tail_ready_timely seed remaining execution owner sourceTrace
    ⟨execution.application.attempt, revealEvent owner⟩ retired request
  obtain ⟨chosen, past, view, recalled, serial⟩ := tail_response_command seed
    (countedMenu.toRawTrace initial horizon (family seed) sourceTrace) owner rfl retired
      ⟨some material⟩
  have response : responseCommand owner
      (execution.respond app owner ⟨some material⟩).environmentRecall
      ((execution.respond app owner ⟨some material⟩).observeEnvironment app) =
        .include (owner, execution.network.nextSerial owner) := by
    rw [app.respond_environmentRecall, recalled,
      responseCommand_transmission execution owner past ⟨view, .activate owner⟩ rfl serial
        material]
  rw [response] at chosen
  have scheduled : (family seed)
      (execution.respond app owner ⟨some material⟩).environmentRecall
      ((execution.respond app owner ⟨some material⟩).observeEnvironment app) =
        PMF.pure (.include (owner, execution.network.nextSerial owner)) := by
    rw [family_apply, chosen]
  exact publication_after_submission_survives (family seed) remaining execution owner sourceTrace
    request value stored material offered timely scheduled postTrace final trace kept

end Vegas.Examples.CommitSeedSignalling
