/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseProposalSourceArchive
import Vegas.Game.PhaseObservableSourceQuery
import Vegas.Game.ProposalRecoveryPrescription
import Vegas.Pending.PhaseProposalEmissionOrder
import Vegas.Pending.PhaseBindingResponseWitness

/-! # Observable source queries with the complete typed proposal archive

The actual local query retains the existing normalized failure/address controls
and adjoins the archive reconstructed from own recall and complete packet
observation. Its source component uses the owning all-raw genuine-query theorem.
This readout does not assert any equality of conditional beliefs.
-/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Protocol
  GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]

/-- The source control query and canonical proposals are both functions of the
actual ordinary decision input; neither reads the scheduler's private history. -/
def phaseProposalQuery? (setup : Setup (Player := Player) (L := L))
    (mode : ExecutionMode) (runtime : EventGraphRuntime (serviceGraph setup mode))
    (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))
    (plan : RuntimePhasePlan (serviceGraph setup mode)) (who : Player)
    (event : (serviceGraph setup mode).EventId)
    (past : List (phaseApplication runtime leaks).PlayerEntry)
    (view : (phaseApplication runtime leaks).PlayerView) :
    Option (setup.commitRecoveryModel.InfoState who × Finset (ProposalRecoveryProposal L)) :=
  (phaseVirtualSourceQuery? setup mode runtime leaks plan who event view).map fun source =>
    (source, PhaseProposal.observedSourceArchive runtime leaks past view)

/-- At every actual ready binding decision, the source component is genuine
and the archive is exactly the typed proposal set of the physical submitted
traffic, including failed and stale openings. The source witness is supplied by
the existing all-raw source query; no counterpart or posterior premise is used. -/
theorem phaseProposalQuery?_genuine_base
    (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
    (runtime : EventGraphRuntime (serviceGraph setup mode))
    (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))
    (complete : leaks = MessageNetwork.completePendingObservation)
    (plan : RuntimePhasePlan (serviceGraph setup mode))
    (maximal : plan.phases.IsChain fun before after =>
      before.kind ≠ after.kind ∨ before.kind = .sample)
    (horizon : Nat) (scheduler : (phaseApplication runtime leaks).Scheduler) {control}
    (trace : ((phaseApplication runtime leaks).protocol
      (setup.initialLaw.map fun draw => PhaseRuntimeState.initial plan (encodeInputs draw))
      horizon scheduler).Trace (some control))
    (who : Player) (active : control.actor = some who)
    (event : (serviceGraph setup mode).EventId) (payload : L.Ty)
    (binding : (serviceGraph setup mode).outputLayout event = .binding who payload)
    (request : control.execution.application.SeedRequest who
      ⟨control.execution.application.attempt, event⟩) :
    ∃ (current : CommitRecoveryState setup.program)
      (sourceTrace : setup.commitRecoveryProtocol.Trace (some current)),
      ProtocolState.actor setup.program current.point = some who ∧
      instructionCount setup.program - ProtocolState.remaining setup.program current.point =
        event.val ∧
      setup.commitRecoveryModel.IsDecisionInfo who
        (setup.commitRecoveryModel.infoOf who sourceTrace) ∧
      phaseProposalQuery? setup mode runtime leaks plan who event
          (control.execution.recall who)
          (control.execution.observe (phaseApplication runtime leaks) who) =
        some (setup.commitRecoveryErasedInformation who
          (setup.commitRecoveryNoMissInformation who
            (setup.commitRecoveryModel.infoOf who sourceTrace)),
          PhaseProposal.sourceArchive control.execution.network.inputs) := by
  obtain ⟨current, sourceTrace, actor, rank, decision, queried⟩ :=
    phaseVirtualSourceQuery?_genuine_of_ready_binding setup mode runtime leaks plan maximal
      horizon scheduler trace who event payload binding request
  refine ⟨current, sourceTrace, actor, rank, decision, ?_⟩
  simp only [phaseProposalQuery?, queried, Option.map_some]
  rw [PhaseProposal.observedSourceArchive_eq_submitted runtime leaks complete _ horizon scheduler
    control trace who active]

/-- A returned ready-binding query retains its literal physical namespace and
static event rank. The recall argument changes only the proposal archive. -/
theorem phaseProposalQuery?_binding_address
    (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
    (runtime : EventGraphRuntime (serviceGraph setup mode))
    (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))
    (plan : RuntimePhasePlan (serviceGraph setup mode))
    (maximal : plan.phases.IsChain fun before after =>
      before.kind ≠ after.kind ∨ before.kind = .sample)
    (horizon : Nat) (scheduler : (phaseApplication runtime leaks).Scheduler) {control}
    (trace : ((phaseApplication runtime leaks).protocol
      ((setup.initialLaw.map encodeInputs).map (PhaseRuntimeState.initial plan))
      horizon scheduler).Trace (some control))
    (who : Player) (event : (serviceGraph setup mode).EventId) (payload : L.Ty)
    (binding : (serviceGraph setup mode).outputLayout event = .binding who payload)
    (request : control.execution.application.SeedRequest who
      ⟨control.execution.application.attempt, event⟩)
    (past : List (phaseApplication runtime leaks).PlayerEntry)
    (key : setup.ProposalRecoveryComponent who)
    (queried : phaseProposalQuery? setup mode runtime leaks plan who event past
      (control.execution.observe (phaseApplication runtime leaks) who) = some key) :
    key.1.1.1.2.2 = (control.execution.application.attempt.generation,
      control.execution.application.attempt.phase) ∧
    (key.1.1.1.1.map (ProtocolView.position who setup.program)) = some event.val := by
  have initialEq : (setup.initialLaw.map encodeInputs).map (PhaseRuntimeState.initial plan) =
      setup.initialLaw.map (fun theta => PhaseRuntimeState.initial plan (encodeInputs theta)) :=
    PMF.map_comp _ _ _
  have raw : ((phaseApplication runtime leaks).protocol
      (setup.initialLaw.map fun theta => PhaseRuntimeState.initial plan (encodeInputs theta))
      horizon scheduler).Trace (some control) := by
    rw [← initialEq]
    exact trace
  obtain ⟨_original, virtual, _originalTrace, _virtualTrace, _excluded, _generation, _actor,
    rank, _played, typed, _publicRecall, _controls, _addresses⟩ :=
    phaseVirtualSourceView?_genuine_of_ready_binding setup mode runtime leaks plan maximal
      horizon scheduler raw who event payload binding request
  let view := control.execution.observe (phaseApplication runtime leaks) who
  let controls :=
    (((view.application.2.retired.map fun record => record.2.sourceFailureFootprint.2).foldr
        (fun first rest => first ∪ rest) ∅) ∪
      view.application.2.native.sourceFailureFootprint.1 view.application.2.attempt.phase,
      view.application.2.attempt.generation, view.application.2.attempt.phase)
  let addresses := (view.application.2.sourcePublicAddressWord plan event.val).reverse ++
    [(none, (∅, 0, 0))]
  let read := setup.commitRecoveryErasedRead who
    (ProtocolView.eraseHistory who setup.program
      (ProtocolState.observe who setup.program virtual.point)) controls addresses
  unfold phaseProposalQuery? phaseVirtualSourceQuery? at queried
  rw [typed, Option.map_some, Option.map_some] at queried
  have first : key.1 = setup.commitRecoveryErasedInformation who
      (setup.commitRecoveryNoMissInformation who read) :=
    (congrArg Prod.fst (Option.some.inj queried)).symm
  have unchanged : (setup.commitRecoveryNoMissInformation who read).1.1.1 = read.1.1.1 ∧
      (setup.commitRecoveryNoMissInformation who read).1.1.2.2 = read.1.1.2.2 := by
    unfold Setup.commitRecoveryNoMissInformation
    split
    · exact ⟨(setup.commitRecoveryWithAttemptExclusions_controls who _ _ read).1,
        (setup.commitRecoveryWithAttemptExclusions_controls who _ _ read).2.1⟩
    · exact ⟨rfl, rfl⟩
  have erasedPosition (observation : ProtocolView who setup.program) :
      ProtocolView.position who setup.program
          (ProtocolView.eraseHistory who setup.program observation) =
        ProtocolView.position who setup.program observation := by
    have equal := congrArg (ProtocolView.position who setup.program)
      (ProtocolView.publicOnly_eraseHistory who setup.program observation)
    simpa only [ProtocolView.position_publicOnly] using equal
  constructor
  · rw [first]
    change (setup.commitRecoveryNoMissInformation who read).1.1.2.2 = _
    rw [unchanged.2]
    rfl
  · rw [first]
    change ((setup.commitRecoveryNoMissInformation who read).1.1.1.map
      (ProtocolView.eraseHistory who setup.program)).map
        (ProtocolView.position who setup.program) = some event.val
    rw [unchanged.1]
    have position := ProtocolView.position_add_remaining who setup.program virtual.point
    have bounded := ProtocolState.remaining_le_instructionCount setup.program virtual.point
    have exactRank : ProtocolView.position who setup.program
        (ProtocolState.observe who setup.program virtual.point) = event.val := by omega
    simpa only [read, Setup.commitRecoveryErasedRead, Option.map_some, erasedPosition]
      using congrArg (some : Nat → Option Nat) exactRank

/-- A proper earlier SEND and a current nonsilent ready binding cannot consume
the same query cell. Persistent sent recall supplies freshness, even when the
earlier packet was lost or its attempt was canceled. -/
theorem phaseProposalQuery_ne_of_recalled_binding_send
    (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
    (runtime : EventGraphRuntime (serviceGraph setup mode))
    (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))
    (bounds : MessageBounds (serviceGraph setup mode))
    (plan : RuntimePhasePlan (serviceGraph setup mode))
    (maximal : plan.phases.IsChain fun before after =>
      before.kind ≠ after.kind ∨ before.kind = .sample)
    (horizon : Nat) (scheduler : (phaseApplication runtime leaks).Scheduler)
    (remaining : Nat) (who : Player) (execution : (phaseApplication runtime leaks).Execution)
    (trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      ((setup.initialLaw.map encodeInputs).map (PhaseRuntimeState.initial plan))
      horizon scheduler).Trace (some ⟨remaining, some who, execution⟩))
    (earlier : (phaseApplication runtime leaks).PlayerEntry)
    (recorded : earlier ∈ execution.recall who)
    (oldMaterial : WitnessedSubmission (serviceGraph setup mode))
    (oldSent : earlier.action.transmission = some oldMaterial)
    (oldEvent : (serviceGraph setup mode).EventId) (oldCandidate : Handle (serviceGraph setup mode))
    (oldNamed : oldMaterial.call.packet = .commitment oldEvent oldCandidate)
    (oldPayload : L.Ty)
    (oldBinding : (serviceGraph setup mode).outputLayout oldEvent = .binding who oldPayload)
    (event : (serviceGraph setup mode).EventId) (payload : L.Ty)
    (binding : (serviceGraph setup mode).outputLayout event = .binding who payload)
    (request : execution.application.SeedRequest who ⟨execution.application.attempt, event⟩)
    (material : WitnessedSubmission (serviceGraph setup mode))
    (offered : (⟨some material⟩ : (phaseApplication runtime leaks).Action) ∈
      PhaseCount.onePacketActions runtime leaks bounds who (execution.recall who)
        (execution.observe (phaseApplication runtime leaks) who))
    (oldPast : List (phaseApplication runtime leaks).PlayerEntry)
    (oldKey key : setup.ProposalRecoveryComponent who)
    (oldQueried : phaseProposalQuery? setup mode runtime leaks plan who oldEvent oldPast
      earlier.beforeView = some oldKey)
    (queried : phaseProposalQuery? setup mode runtime leaks plan who event (execution.recall who)
      (execution.observe (phaseApplication runtime leaks) who) = some key) : oldKey ≠ key := by
  let menu := PhaseCount.onePacketMenu runtime leaks bounds
  let inputs := setup.initialLaw.map encodeInputs
  let initial := inputs.map (PhaseRuntimeState.initial plan)
  have ordered := serviceGraph_revealRelaxedOrdered setup mode
  obtain ⟨before, prior, _retained, _acting, viewed, oldRequest⟩ :=
    phase_recorded_binding_request runtime leaks bounds plan inputs horizon ordered scheduler
      trace who earlier recorded oldMaterial oldSent oldEvent oldCandidate oldNamed
  have oldAddress := phaseProposalQuery?_binding_address setup mode runtime leaks plan maximal
    horizon scheduler (menu.toRawTrace initial horizon scheduler prior) who oldEvent oldPayload
      oldBinding oldRequest oldPast oldKey (by simpa only [viewed] using oldQueried)
  have address := phaseProposalQuery?_binding_address setup mode runtime leaks plan maximal
    horizon scheduler (menu.toRawTrace initial horizon scheduler trace) who event payload binding
      request (execution.recall who) key queried
  intro equal
  subst key
  have controls := oldAddress.1.symm.trans address.1
  have sameAttempt : before.execution.application.attempt = execution.application.attempt := by
    cases first : before.execution.application.attempt with
    | mk firstPhase firstGeneration =>
        cases second : execution.application.attempt with
        | mk secondPhase secondGeneration =>
            have fields : (firstGeneration, firstPhase) = (secondGeneration, secondPhase) := by
              simpa only [first, second] using controls
            obtain ⟨rfl, rfl⟩ := Prod.mk.inj fields
            rfl
  have recalledAttempt : earlier.beforeView.application.2.attempt =
      execution.application.attempt := by
    rw [viewed]
    exact sameAttempt
  have ranks : oldEvent.val = event.val := Option.some.inj (oldAddress.2.symm.trans address.2)
  have unsent := PhaseCount.unsent_of_nonsilent runtime leaks bounds plan ordered inputs horizon
    scheduler remaining who execution trace ⟨execution.application.attempt, event⟩ request
      material offered
  have strict := phase_recorded_binding_rank_lt_of_unsent_request runtime leaks bounds plan inputs
    horizon ordered scheduler trace who earlier recorded oldMaterial oldSent oldEvent oldCandidate
      oldNamed recalledAttempt event request unsent
  omega

end Vegas
