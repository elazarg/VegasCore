/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Pending.ReservedEpochDelivery
import Vegas.Pending.ReservedEpochFinite
import Vegas.Examples.CommitTimingInformationInitialGeometry
import Vegas.Pending.PhasePreparedBinding
import Vegas.Pending.PhaseReadyResolution
import Vegas.Pending.PhasePreparedOnePacket
import Interaction.ReactiveMessageReadout
import GameTheoryExtensions.Math.Probability.Uniform

/-! # Concurrent pending commitments under a correlated epoch environment -/

noncomputable section

namespace Vegas.Examples.ReservedEpochConcurrency

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Math.Probability
open CommitTimingInformation

abbrev Player := CommitTimingInformation.Player
abbrev graph := CommitTimingInformation.graph
abbrev runtime := CommitTimingInformation.runtime
abbrev leaks := CommitTimingInformation.leaks
abbrev app := CommitTimingInformation.app

def tape (reverse : Bool) : ReservedEpoch.Tape Player 2 where
  order := fun _ => (Fintype.equivFin Player).trans
    (if reverse then Equiv.swap alice bob else Equiv.refl Player)
  activation := fun _ _ => true
  processing := fun cycle => if cycle.val = 1 then !reverse else true

def prior : PMF (ReservedEpoch.Tape Player 2) := bitLaw.map tape

def selectedScheduler : app.Scheduler :=
  (ReservedEpoch.implementation runtime leaks 2 prior).scheduler

def response (owner : Player) : app.Action :=
  phaseBindingResponse runtime leaks owner (bindingEvent owner) .bool (.success true) 0

def players (owner : Player) : app.Policy := fun _ _ => PMF.pure (response owner)

def waitState (execution : app.Execution) : app.Execution :=
  { execution with environmentRecall := execution.environmentRecall ++
      [⟨execution.observeEnvironment app, .wait⟩] }

def offer (execution : app.Execution) (owner : Player) : app.Execution :=
  let active := execution.sampledActivation app owner
    (execution.network.pending.map Message.id).toFinset
  active.respond app owner (response owner)

def first (reverse : Bool) : Player := if reverse then bob else alice
def second (reverse : Bool) : Player := if reverse then alice else bob

def beforeOffers (bit : Bool) : app.Execution :=
  waitState (waitState (initialExecution bit))

def afterFirst (reverse bit : Bool) : app.Execution := offer (beforeOffers bit) (first reverse)

def afterBoth (reverse bit : Bool) : app.Execution :=
  offer (afterFirst reverse bit) (second reverse)

theorem tape_owner_first (reverse : Bool) : (tape reverse).owner 0 0 = first reverse := by
  simp [ReservedEpoch.Tape.owner, tape, first, Equiv.trans_apply]
  cases reverse <;> rfl

theorem tape_owner_second (reverse : Bool) : (tape reverse).owner 0 1 = second reverse := by
  simp [ReservedEpoch.Tape.owner, tape, second, Equiv.trans_apply]
  cases reverse <;> rfl

private theorem completeActivation (execution : app.Execution) (owner : Player) :
    execution.environmentStep app (.activate owner) =
      PMF.pure (execution.sampledActivation app owner
        (execution.network.pending.map Message.id).toFinset) := by
  rw [ReactiveApplication.Execution.activation_samples]
  change (MessageNetwork.completePendingObservation owner execution.network.pending).map _ = _
  simp only [MessageNetwork.completePendingObservation, PMF.pure_map]

private theorem round_wait (reverse : Bool) (slot : Nat) (execution : app.Execution)
    (cursor : execution.environmentRecall.length = slot) (early : slot < 2)
    (empty : execution.network.pending = []) :
    app.round (ReservedEpoch.family runtime leaks 2 (tape reverse)) players execution =
      PMF.pure (waitState execution) := by
  have command := ReservedEpoch.processing_at runtime leaks 2 (tape reverse) 0 slot
    (execution.observeEnvironment app) early (by rfl)
  simp only [Nat.zero_mul, Nat.zero_add] at command
  have selected : ReservedEpoch.command runtime leaks 2 (tape reverse)
      execution.environmentRecall.length (execution.observeEnvironment app) = .wait := by
    rw [cursor, command]
    exact ReservedEpoch.processing_empty runtime leaks _ empty
  simp only [ReactiveApplication.round, ReservedEpoch.family, PMF.pure_bind, selected,
    ReactiveApplication.dispatch, ReactiveApplication.Execution.environmentStep,
    ReactiveApplication.Command.actor?, ReactiveApplication.resume, PMF.pure_map]
  rfl

private theorem round_offer (reverse : Bool) (position : Fin 2) (execution : app.Execution)
    (cursor : execution.environmentRecall.length = 2 + position.val) :
    app.round (ReservedEpoch.family runtime leaks 2 (tape reverse)) players execution =
      PMF.pure (offer execution ((tape reverse).owner 0 position)) := by
  have selected := ReservedEpoch.activation_at runtime leaks 2 (tape reverse) 0 position
    (execution.observeEnvironment app) (by rfl)
  simp only [Nat.zero_mul, Nat.zero_add] at selected
  simp only [ReactiveApplication.round, ReservedEpoch.family, PMF.pure_bind, cursor, selected,
    ReactiveApplication.dispatch, completeActivation, PMF.pure_bind,
    ReactiveApplication.Command.actor?, ReactiveApplication.resume, ReactiveApplication.invoke,
    players, PMF.pure_map, offer]

theorem first_callbacks_law (reverse bit : Bool) :
    app.runRounds (ReservedEpoch.family runtime leaks 2 (tape reverse)) players 4
      (initialExecution bit) = PMF.pure (afterBoth reverse bit) := by
  have round0 := round_wait reverse 0 (initialExecution bit) rfl (by decide) rfl
  have round1 := round_wait reverse 1 (waitState (initialExecution bit)) rfl
    (by decide) rfl
  have round2 := round_offer reverse 0 (beforeOffers bit) rfl
  have round3 := round_offer reverse 1 (afterFirst reverse bit) (by
    simp [afterFirst, offer, beforeOffers, waitState,
      ReactiveApplication.Execution.sampledActivation,
      ReactiveApplication.respond_environmentRecall, initialExecution,
      ReactiveApplication.Execution.initial])
  rw [tape_owner_first] at round2
  rw [tape_owner_second] at round3
  simp only [ReactiveApplication.runRounds, round0, PMF.pure_bind, round1]
  change (app.round _ _ (beforeOffers bit)).bind _ = _
  rw [round2, PMF.pure_bind]
  change (app.round _ _ (afterFirst reverse bit)).bind _ = _
  rw [round3, PMF.pure_bind]
  rfl

theorem two_packets_pending (reverse bit : Bool) :
    (afterBoth reverse bit).network.pending.length = 2 ∧
      (afterBoth reverse bit).network.ledger = [] ∧
      ((afterBoth reverse bit).network.pending.map Message.sender) =
        [first reverse, second reverse] := by
  cases reverse <;>
    simp [afterBoth, afterFirst, beforeOffers, waitState, offer, first, second, response,
      phaseBindingResponse, initialExecution, ReactiveApplication.Execution.initial,
      ReactiveApplication.Execution.sampledActivation, ReactiveApplication.Execution.respond,
      MessageNetwork.learn, MessageNetwork.submit, MessageNetwork.empty, Message.sender]

theorem distinct_pending_owners (reverse : Bool) : first reverse ≠ second reverse := by
  cases reverse <;> decide

def commitmentMessage (owner : Player) : Message Player app.Payload :=
  ⟨(owner, 0), ⟨originalAttempt,
    ⟨.commitment (bindingEvent owner) (owner, .prepared 0), none,
      some ⟨bindingEvent owner⟩⟩⟩⟩

private theorem offer_request (execution : app.Execution) (actor owner : Player)
    (request : execution.application.SeedRequest owner (originalCoordinate owner)) :
    (offer execution actor).application.SeedRequest owner (originalCoordinate owner) := by
  exact respond_request runtime leaks _ actor (response actor) owner _ request

private theorem offer_pending (execution : app.Execution) (owner : Player)
    (request : execution.application.SeedRequest owner (originalCoordinate owner))
    (serial : execution.network.nextSerial owner = 0) :
    (offer execution owner).network.pending =
      execution.network.pending ++ [commitmentMessage owner] := by
  let material : WitnessedSubmission graph :=
    ⟨⟨.commitment (bindingEvent owner) (owner, .prepared 0), some ⟨.bool, true⟩⟩, .none⟩
  have allowed : PhaseCount.allows execution.application.publicView
      material.call.packet = true := by
    rw [PhaseCount.allows_publicView]
    obtain ⟨phase, head, inside⟩ := request.2.1
    simp only [PhaseRuntimeState.allows, Option.mem_def.mp head, material, Payload.event?]
    exact decide_eq_true inside
  have unexcluded : PhaseCount.excludedCall execution.application.publicView
      material.call.packet = false := by
    simp only [PhaseCount.excludedCall, material, Payload.event?, bindingEvent_actor,
      Option.any_some]
    exact decide_eq_false request.2.2.2.2
  have token := execution.application.current.native.publicView_tokenFor_of_ready
    material.call.packet (bindingEvent owner) rfl request.2.2.1
  change execution.network.pending ++ [⟨(owner, execution.network.nextSerial owner),
    (execution.application.submit owner material).emit owner _ material⟩] = _
  rw [PhaseCount.emit_after_submit, serial]
  have original : execution.application.attempt = originalAttempt := request.1.symm
  simp only [original, PhaseCount.maskPacket, allowed, unexcluded, Bool.false_eq_true,
    ↓reduceIte, token, material, EvidenceRequest.resolve, commitmentMessage]

theorem canonical_pending (reverse bit : Bool) :
    (afterBoth reverse bit).network.pending =
      [commitmentMessage (first reverse), commitmentMessage (second reverse)] := by
  have initialRequest (owner : Player) :
      (beforeOffers bit).application.SeedRequest owner (originalCoordinate owner) :=
    initial_binding_request bit owner
  have firstPending := offer_pending (beforeOffers bit) (first reverse)
    (initialRequest _) rfl
  have secondRequest := offer_request (beforeOffers bit) (first reverse) (second reverse)
    (initialRequest _)
  have serial : (afterFirst reverse bit).network.nextSerial (second reverse) = 0 := by
    cases reverse <;>
      simp [afterFirst, offer, beforeOffers, waitState, first, second, response,
        phaseBindingResponse, initialExecution, ReactiveApplication.Execution.initial,
        ReactiveApplication.Execution.sampledActivation, ReactiveApplication.Execution.respond,
        MessageNetwork.learn, MessageNetwork.submit, MessageNetwork.empty]
  have secondPending := offer_pending (afterFirst reverse bit) (second reverse) secondRequest serial
  rw [afterBoth, secondPending, afterFirst, firstPending]
  rfl

theorem commitment_permitted (owner : Player)
    (traffic : List (Message Player (CommitAttemptPacket graph))) :
    PhaseCount.permits traffic (commitmentMessage owner) = true := by
  rw [PhaseCount.permits_eq_true_iff]
  refine ⟨WitnessedPacket.tokenValid_commitment _ _ _, ?_, ?_, trivial⟩
  · change CountCallCorrect _ (⟨(owner, 0),
      ⟨.commitment (bindingEvent owner) (owner, .prepared 0), none,
        some ⟨bindingEvent owner⟩⟩⟩ : Message Player (WitnessedPacket graph))
    refine ⟨?_, rfl, rfl, ⟨0, rfl⟩, ?_⟩
    · have output : graph.outputLayout (bindingEvent owner) = .binding owner .bool :=
        bindingEvent_layout owner
      simp only [bindingOwnedBy, Message.sender, output, decide_true]
    · intro prior earlier _named _call
      exact (Nat.not_lt_zero prior.id.2 earlier.2.2).elim
  · intro prior earlier
    have smaller := earlier.2.2
    change prior.id.2 < 0 at smaller
    omega

/-- Both pending packets satisfy the authentic count rule; they are not
arbitrary malformed traffic used merely to witness queue length. -/
theorem pending_permitted (reverse bit : Bool)
    (message : Message Player (CommitAttemptPacket graph))
    (pending : message ∈ (afterBoth reverse bit).network.pending) :
    PhaseCount.permits (afterBoth reverse bit).network.pending message = true := by
  rw [canonical_pending] at pending ⊢
  simp only [List.mem_cons, List.not_mem_nil, or_false] at pending
  rcases pending with rfl | rfl <;> exact commitment_permitted _ _

theorem tape_supported (reverse : Bool) : tape reverse ∈ prior.support := by
  rw [prior, PMF.support_map]
  exact ⟨reverse, bitLaw_fullSupport reverse, rfl⟩

theorem concurrent_prefix_supported (reverse bit : Bool) :
    afterBoth reverse bit ∈ (app.runRounds selectedScheduler players 4
      (initialExecution bit)).support := by
  have realized := ReservedEpoch.realize runtime leaks 2 prior players 4 (initialState bit)
  change (prior.bind fun tape => app.runRounds (ReservedEpoch.family runtime leaks 2 tape)
    players 4 (initialExecution bit)) =
      app.runRounds selectedScheduler players 4 (initialExecution bit) at realized
  rw [← realized, PMF.support_bind]
  refine Set.mem_iUnion₂.mpr ⟨tape reverse, tape_supported reverse, ?_⟩
  rw [first_callbacks_law]
  exact (PMF.mem_support_pure_iff _ _).mpr rfl

end Vegas.Examples.ReservedEpochConcurrency
