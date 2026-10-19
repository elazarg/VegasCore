/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.ReservedEpochStoppedBinding
import Vegas.Game.PhasePublicSourceChronology
import Vegas.Game.PhaseCommitmentProposalArchive
import Vegas.Pending.PhaseAttemptReceiptSnapshot
import Vegas.Pending.ReservedEpochOpportunity
import Vegas.Pending.ReservedEpochReceiptContract

/-! # Original binding records at an actual stopped reserved attempt -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [Fintype Player] [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
  (runtime : EventGraphRuntime (serviceGraph setup mode))
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))
  (bounds : MessageBounds (serviceGraph setup mode))
  (plan : RuntimePhasePlan (serviceGraph setup mode))

local notation "graph" => serviceGraph setup mode
local notation "app" => phaseApplication runtime leaks
local notation "menu" => PhaseCount.onePacketMenu runtime leaks bounds
local notation "inputs" => setup.initialLaw.map encodeInputs

/-- The stopped law retains its real closing transition and its original
drained image. Per-rank misses are read from that image's accepted table;
an unusable accepted handle is not confused with a missing acceptance.
Every newly excluded owner's miss comes from its literal old anchor episode.
On a failed close, the exact image and address occur in the actual archive. -/
theorem phaseProposalUnflagged_stopped_binding_image
    (complete : leaks = MessageNetwork.completePendingObservation)
    (coveredValues : bounds.CoversOutputValues)
    (maximal : plan.phases.IsChain fun first last =>
      first.kind ≠ last.kind ∨ first.kind = .sample)
    (ordered : (graph).RevealRelaxedOrdered)
    (values : ∀ who (key : setup.ProposalRecoveryComponent who),
      PMF (setup.CommitRecoveryValueChoice who key.1))
    (fullValues : ∀ who key, FullSupport (values who key))
    {length : Nat} (tape : ReservedEpoch.Tape Player length)
    (activationGap processingGap : Nat)
    (gaps : tape.BoundedGaps (ReservedEpoch.completionCycles runtime)
      activationGap processingGap)
    (margin : runtime.AsyncTimely (fun _ => activationGap + 1) (fun _ => processingGap + 1))
    (capacity : ReservedEpoch.executionHorizon runtime ≤ bounds.candidateCount)
    (remaining : Nat) (anchor : (app).Execution)
    (trace : ((menu).protocol ((inputs).map (PhaseRuntimeState.initial plan))
      (ReservedEpoch.executionHorizon runtime)
        (ReservedEpoch.family runtime leaks (ReservedEpoch.packetCapacity runtime) tape)).Trace
          (some ⟨remaining, none, anchor⟩))
    (phase : RuntimePhase graph) (installed : phase ∈ anchor.application.phases.head?)
    (commitment : phase.kind = .commitment) :
    let initial := (inputs).map (PhaseRuntimeState.initial plan)
    let horizon := ReservedEpoch.executionHorizon runtime
    let scheduler := ReservedEpoch.family runtime leaks (ReservedEpoch.packetCapacity runtime) tape
    let players := ReactiveApplication.anchoredPolicy anchor
      (phaseProposalUnflaggedPolicy setup mode runtime leaks bounds plan values)
    let profile := fun who => (menu).restrictPolicy initial horizon scheduler who (players who)
    let stopped := fun history : ((menu).protocol initial horizon scheduler).History =>
      match history.state with
      | none => False
      | some control => control.execution.application.attempt ≠ anchor.application.attempt
    ∀ final ∈ (((menu).information initial horizon scheduler).runBehavioralUntil
        ((menu).bounded initial horizon scheduler).wellFoundedHistories profile stopped
          ⟨some ⟨remaining, none, anchor⟩, trace⟩).support,
      ∃ (ending before : (app).Control)
        (prior : ((menu).protocol initial horizon scheduler).Trace (some before))
        (joint : Player → Option (app).Action)
        (legal : ((menu).protocol initial horizon scheduler).Legal (some before) joint)
        (realized : some ending ∈ ((app).transition initial horizon scheduler
          (some before) joint).support) (raw : RecoveryState graph),
        final.state = some ending ∧ ending.actor = none ∧
          ending.execution.application.attempt ≠ anchor.application.attempt ∧
          TracePrefix trace prior ∧ TracePrefix (prior.extend joint legal realized) final.trace ∧
          before.execution.application.attempt = anchor.application.attempt ∧
          phase ∈ before.execution.application.phases.head? ∧
          ending.execution.application =
            ({ before.execution.application with current := raw } :
              PhaseRuntimeState graph).normalize ∧
          PhaseClosingEffect runtime leaks before.execution ending.execution raw ∧
          phase.Finished (phase.drain raw) ∧ (phase.drain raw).native.BindingInvariant ∧
          (phase.drain raw).FailureCoverage ∧
          (phase.drain raw).excluded = ending.execution.application.current.excluded ∧
          (phase.drain raw).native.accepted = raw.native.accepted ∧
          (phase.drain raw).native.candidates = raw.native.candidates ∧
          PhaseProposal.sourceArchive ending.execution.network.inputs =
            PhaseProposal.sourceArchive anchor.network.inputs ∧
          (∀ event ∈ phase.events, (phase.drain raw).native.PublicFailure event ↔
            raw.native.accepted (.inr event) = none) ∧
          (∀ owner, owner ∉ anchor.application.current.excluded →
            owner ∈ ending.execution.application.current.excluded →
            ∃ event ∈ phase.events,
              anchor.application.SeedRequest owner ⟨anchor.application.attempt, event⟩ ∧
                PhaseCount.ResponseRecorded runtime leaks owner
                  ⟨anchor.application.attempt, event⟩ (anchor.recall owner) ∧
                (phase.drain raw).native.PublicFailure event) ∧
          ((((phase.drain raw).excluded \ before.execution.application.entry.excluded) ∩
            phase.owners).Nonempty →
            (⟨anchor.application.attempt, (phase.drain raw).native⟩ : RetiredCommitAttempt graph) ∈
              ending.execution.application.retired ∧
            (anchor.application.attempt, (phase.drain raw).native.sourceFailureFootprint) ∈
              PhaseRuntimeState.sourceControlRecords ending.execution.application.retired) := by
  classical
  intro initial horizon scheduler players profile stopped final supported
  have contract : PhaseService.AsyncContract runtime leaks initial horizon scheduler
      (fun _ => activationGap + 1) (fun _ => processingGap + 1) := {
    opportunity := ReservedEpoch.family_opportunity runtime leaks
      (ReservedEpoch.packetCapacity runtime) (ReservedEpoch.completionCycles runtime) tape
        activationGap processingGap gaps plan ordered maximal inputs
    inclusion := ReservedEpoch.family_protectedInclusion runtime leaks
      (ReservedEpoch.completionCycles runtime) tape activationGap processingGap gaps plan inputs
    completes := ReservedEpoch.family_completesPlay runtime leaks tape plan ordered maximal inputs }
  obtain ⟨ending, stateEq, changed, idle, snapshot, finished, valid, coverage, excluded,
    receipts, before, prior, joint, legal, realized, raw, fromStart, toFinal, same, phaseInstalled,
    snapshotEq, normalized, effect⟩ :=
    phase_attempt_stopped_receipt_snapshot runtime leaks (menu) plan inputs horizon scheduler
      (fun _ => activationGap + 1) (fun _ => processingGap + 1) contract profile
        ⟨remaining, none, anchor⟩ trace phase installed final (by
          convert supported using 1
          congr 3
          funext history
          dsimp only [stopped]
          cases history.state <;> rfl)
  subst snapshot
  obtain ⟨archiveEnding, archiveState, oldArchive⟩ :=
    PhaseProposal.phase_attempt_stopped_sourceArchive runtime leaks bounds plan ordered inputs
      horizon scheduler profile ⟨remaining, none, anchor⟩ trace phase installed commitment final
        (by
          convert supported using 1
          congr 3
          funext history
          dsimp only [stopped]
          cases history.state <;> rfl)
  have sameEnding : archiveEnding = ending :=
    Option.some.inj (archiveState.symm.trans stateEq)
  subst archiveEnding
  have tables := phase.drain_tables raw
  have failures : ∀ event ∈ phase.events, (phase.drain raw).native.PublicFailure event ↔
      raw.native.accepted (.inr event) = none := by
    intro event inside
    obtain ⟨owner, payload, binding⟩ := commitment ▸ phase.fields event
      ((phase.mem_events event).mp inside).1 ((phase.mem_events event).mp inside).2
    rw [(phase.drain raw).native.publicFailure_iff_accepted_none event owner payload binding
      (finished inside), tables.1]
  refine ⟨ending, before, prior, joint, legal, realized, raw, stateEq, idle, changed, fromStart,
    toFinal, same, phaseInstalled, normalized, effect, finished, valid, coverage, excluded,
    tables.1,
    tables.2.1, oldArchive, failures, ?_, ?_⟩
  · intro owner active failed
    obtain ⟨event, inside, request, recorded, unaccepted⟩ :=
      phaseProposalUnflagged_stopped_exclusion_request setup mode runtime leaks bounds plan
        complete coveredValues maximal ordered values fullValues tape activationGap processingGap
          gaps margin capacity remaining anchor trace phase installed commitment owner active
            final supported ending stateEq failed
    refine ⟨event, inside, request, recorded, (failures event inside).mpr ?_⟩
    by_contra present
    obtain ⟨candidate, accepted⟩ := Option.ne_none_iff_exists'.mp present
    have acceptedSnapshot : (phase.drain raw).native.accepted (.inr event) = some candidate := by
      rwa [tables.1]
    obtain ⟨payload, binding⟩ := valid.accepted_typed (.inr event) candidate acceptedSnapshot
    have candidateOwner : candidate.1 = owner := Option.some.inj
      (((graph).actor?_of_outputLayout_binding binding).symm.trans request.2.2.2.1)
    have lower : anchor.application.attempt.phase ≤ event.val := by
      have head := Option.mem_def.mp installed
      simpa only [PhaseRuntimeState.attempt, head, Option.map_some, Option.getD_some] using
        ((phase.mem_events event).mp inside).1
    have received := receipts event candidate lower acceptedSnapshot
    exact unaccepted (by simpa only [candidateOwner] using received)
  · intro failed
    obtain ⟨rest, phases⟩ := List.head?_eq_some_iff.mp (Option.mem_def.mp phaseInstalled)
    have record : (⟨anchor.application.attempt, (phase.drain raw).native⟩ :
        RetiredCommitAttempt graph) ∈ ending.execution.application.retired := by
      have address : (⟨phase.low, before.execution.application.generation⟩ : CommitAttemptId) =
          anchor.application.attempt := by
        rw [← same]
        simp only [PhaseRuntimeState.attempt, phases, List.head?_cons, Option.map_some,
          Option.getD_some]
      rw [normalized]
      change (⟨anchor.application.attempt, (phase.drain raw).native⟩ : RetiredCommitAttempt graph) ∈
        (PhaseRuntimeState.settle before.execution.application.phases
          before.execution.application.generation before.execution.application.entry raw
            before.execution.application.retired).retired
      rw [phases]
      by_cases survivors : (phase.owners \ (phase.drain raw).excluded).Nonempty
      · rw [PhaseRuntimeState.settle_retry phase rest before.execution.application.generation
          before.execution.application.entry raw before.execution.application.retired finished
            commitment failed survivors]
        rw [← address]
        exact List.mem_append_right _ (List.mem_singleton_self _)
      · rw [PhaseRuntimeState.settle_exhausted phase rest before.execution.application.generation
          before.execution.application.entry raw before.execution.application.retired finished
            commitment failed survivors]
        apply (PhaseRuntimeState.settle_archive _ _ _ _ _).subset
        rw [← address]
        exact List.mem_append_right _ (List.mem_singleton_self _)
    refine ⟨record, ?_⟩
    exact List.mem_map_of_mem (f := fun record : RetiredCommitAttempt graph =>
      (record.attempt, record.state.sourceFailureFootprint)) record

end Vegas
