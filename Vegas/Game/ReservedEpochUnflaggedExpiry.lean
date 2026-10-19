/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReservedEpochExpiredRequest
import Vegas.Pending.ReservedEpochFreshBinding
import Vegas.Game.PhaseProposalUnflaggedBinding
import Interaction.ReactiveAnchoredMixture

/-! # No fresh binding expiry in the actual unflagged continuation -/

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

/-- Every genuine binding expiry in the prescribed unflagged continuation
belongs to an episode already offered at the literal anchor. Newly enabled
owned successors cannot acquire a delivery miss. Old WAIT, SENT, pending and
rejected episodes are retained; no claim is made that they are fresh. -/
theorem phaseProposalUnflagged_expiry_recorded_at_anchor
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
    (anchorControl : (app).Control)
    (anchorTrace : ((menu).protocol ((inputs).map (PhaseRuntimeState.initial plan))
      (ReservedEpoch.executionHorizon runtime)
        (ReservedEpoch.family runtime leaks (ReservedEpoch.packetCapacity runtime) tape)).Trace
          (some anchorControl))
    (dueControl : (app).Control)
    (dueTrace : ((menu).protocol ((inputs).map (PhaseRuntimeState.initial plan))
      (ReservedEpoch.executionHorizon runtime)
        (ReservedEpoch.family runtime leaks (ReservedEpoch.packetCapacity runtime) tape)).Trace
          (some dueControl))
    (anchorKept : TracePrefix anchorTrace dueTrace)
    (owner : Player) (event : (graph).EventId) (payload : L.Ty)
    (binding : (graph).outputLayout event = .binding owner payload)
    (request : dueControl.execution.application.SeedRequest owner
      ⟨dueControl.execution.application.attempt, event⟩)
    (entered : Nat)
    (stamp : dueControl.execution.application.current.native.activatedAt event = some entered)
    (due : runtime.deadline event ≤
      dueControl.execution.application.current.native.clock - entered)
    (expired : (app).Execution) (expiryRemaining : Nat)
    (expiry : expired ∈ (dueControl.execution.environmentStep (app)
      (.application (.expire event))).support)
    (expiryTrace : ((menu).protocol ((inputs).map (PhaseRuntimeState.initial plan))
      (ReservedEpoch.executionHorizon runtime)
        (ReservedEpoch.family runtime leaks (ReservedEpoch.packetCapacity runtime) tape)).Trace
          (some ⟨expiryRemaining, none, expired⟩))
    (kept : TracePrefix dueTrace expiryTrace)
    (count : Nat)
    (supported : expired ∈ ((app).runRounds
      (ReservedEpoch.family runtime leaks (ReservedEpoch.packetCapacity runtime) tape)
      (phaseProposalUnflaggedPolicy setup mode runtime leaks bounds plan values)
        count anchorControl.execution).support) :
    PhaseCount.ResponseRecorded runtime leaks owner
      ⟨dueControl.execution.application.attempt, event⟩ (anchorControl.execution.recall owner) ∧
      (dueControl.execution.application.attempt = anchorControl.execution.application.attempt →
        anchorControl.execution.application.SeedRequest owner
          ⟨dueControl.execution.application.attempt, event⟩) := by
  classical
  let scheduler := ReservedEpoch.family runtime leaks (ReservedEpoch.packetCapacity runtime) tape
  let horizon := ReservedEpoch.executionHorizon runtime
  let ordinary := phaseProposalUnflaggedPolicy setup mode runtime leaks bounds plan values
  let players := ReactiveApplication.anchoredPolicy anchorControl.execution ordinary
  have anchoredSupport : expired ∈
      ((app).runRounds scheduler players count anchorControl.execution).support := by
    rw [ReactiveApplication.runRounds_anchoredPolicy]
    exact supported
  have consistent := ((app).consistentRecall_policyInvariant players).runRounds scheduler count
    anchorControl.execution expired
      (fun who =>
        ReactiveApplication.anchoredPolicy_consistent anchorControl.execution ordinary who)
        anchoredSupport
  have recorded : PhaseCount.ResponseRecorded runtime leaks owner
      ⟨dueControl.execution.application.attempt, event⟩ (anchorControl.execution.recall owner) := by
    by_contra absent
    obtain ⟨before, prior, entry, _priorKept, acting, _member, viewed, offered, requested,
      first, recalled, postTrace, postKept⟩ :=
      ReservedEpoch.expired_request_first_response runtime leaks tape activationGap processingGap
        gaps margin bounds plan ordered maximal inputs dueControl dueTrace owner event entered
          request stamp due
    rcases before with ⟨remaining, actor, execution⟩
    change actor = some owner at acting
    subst actor
    have actualRecall := (app).environmentStep_recall dueControl.execution expired
      (.application (.expire event)) expiry
    obtain ⟨later, recalled⟩ := recalled
    have remembered : expired.recall owner = execution.recall owner ++ entry :: later := by
      rw [actualRecall]
      exact recalled
    have selected : entry.action ∈
        (ordinary owner (execution.recall owner) entry.beforeView).support :=
      phase_recorded_prescribed_response runtime leaks anchorControl.execution expired ordinary
        owner ⟨dueControl.execution.application.attempt, event⟩ absent _ later entry remembered
          (consistent owner) (by
            rw [viewed]
            have raw := (menu).toRawTrace _ horizon scheduler prior
            obtain ⟨_draw, invariant⟩ := phaseNativeInvariant_history runtime leaks plan inputs
              horizon scheduler raw
            exact (PhaseRuntimeState.requests_publicView _ invariant owner _).mpr requested)
    have unsent := phase_unrecorded_request_unsent runtime leaks bounds plan ordered inputs
      horizon scheduler ⟨remaining, some owner, execution⟩ prior owner
        ⟨dueControl.execution.application.attempt, event⟩ first
    have sameAttempt : dueControl.execution.application.attempt = execution.application.attempt :=
      requested.1
    have currentRequest : execution.application.SeedRequest owner
        ⟨execution.application.attempt, event⟩ := by
      simpa only [sameAttempt] using requested
    have currentFirst : ¬ PhaseCount.ResponseRecorded runtime leaks owner
        ⟨execution.application.attempt, event⟩ (execution.recall owner) := by
      simpa only [sameAttempt] using first
    have currentUnsent : ∀ message ∈ (app).outputs (execution.recall owner),
        PhaseCount.event? message.payload ≠ some ⟨execution.application.attempt, event⟩ := by
      simpa only [sameAttempt] using unsent
    have nativePrior : ((menu).protocol
        (setup.initialLaw.map fun draw => PhaseRuntimeState.initial plan (encodeInputs draw))
        horizon scheduler).Trace (some ⟨remaining, some owner, execution⟩) := by
      change ((menu).protocol
        (setup.initialLaw.map ((PhaseRuntimeState.initial plan) ∘ encodeInputs))
          horizon scheduler).Trace (some ⟨remaining, some owner, execution⟩)
      rw [← PMF.map_comp]
      exact prior
    rw [viewed] at selected
    obtain ⟨material, _value, transmitted, _typed⟩ :=
      phaseProposalUnflaggedBinding_supported_usable setup mode runtime leaks bounds plan complete
        coveredValues maximal values fullValues horizon scheduler capacity remaining owner execution
          nativePrior event payload binding currentRequest currentUnsent entry.action selected
    have actionEq : entry.action = (⟨some material⟩ : (app).Action) :=
      congrArg (fun transmission => (⟨transmission⟩ : (app).Action)) transmitted
    rcases entry with ⟨beforeView, action, emitted⟩
    change action = (⟨some material⟩ : (app).Action) at actionEq
    cases actionEq
    let rawPost := (menu).toRawTrace _ horizon scheduler postTrace
    let rawExpiry := (menu).toRawTrace _ horizon scheduler expiryTrace
    have path := ((menu).reaches_raw _ horizon scheduler
      (postKept.trans kept).reachesWithin).tracePrefix
    have dueRequest : dueControl.execution.application.SeedRequest owner
        ⟨execution.application.attempt, event⟩ := by
      simpa only [sameAttempt] using request
    have atDeadline : runtime.deadline event ≤
        dueControl.execution.application.current.native.clock -
          (dueControl.execution.application.current.native.activatedAt event).getD
            dueControl.execution.application.current.native.clock := by
      simpa only [stamp, Option.getD_some] using due
    have coverage : ∀ past view action, action ∈ (players owner past view).support →
        action.transmission = none ∨ PhaseCount.OnePacketResponse runtime leaks owner past view
          action := by
      intro past view action positive
      have allowed := (menu).anchoredPolicy_covered _ horizon scheduler anchorControl anchorTrace
        ordinary owner (phaseProposalUnflaggedPolicy_covered setup mode runtime leaks bounds plan
          values owner) past view action positive
      exact ((PhaseCount.mem_onePacketActions runtime leaks bounds owner _ _ _).mp allowed).2
    exact ReservedEpoch.first_binding_response_cannot_expire runtime leaks tape activationGap
      processingGap gaps margin bounds plan ordered maximal inputs remaining owner execution prior
        event payload binding currentRequest currentFirst material offered rawPost dueControl
          ((menu).toRawTrace _ horizon scheduler dueTrace) dueRequest atDeadline expired
            expiryRemaining expiry rawExpiry path players consistent coverage
  refine ⟨recorded, ?_⟩
  intro same
  have anchorOrdered := (phaseApplication_seedOrder runtime leaks).history
    ((inputs).map (PhaseRuntimeState.initial plan)) horizon scheduler (fun state positive => by
      obtain ⟨draw, _positive, rfl⟩ := PMF.support_map .. ▸ positive
      exact PhaseRuntimeState.initial_ordered plan draw)
    ((menu).toRawTrace _ horizon scheduler anchorTrace)
  have extension := phase_prefix_semantic_extension runtime leaks (menu)
    ((inputs).map (PhaseRuntimeState.initial plan)) horizon scheduler anchorControl dueControl
      anchorTrace dueTrace anchorKept anchorOrdered same.symm
  have unfinished : event ∉
      anchorControl.execution.application.current.native.config.cut.completed := by
    intro completed
    exact request.2.2.1.1 (completed_subset_of_history_prefix _ _ extension.2 completed)
  have currentRecorded : PhaseCount.ResponseRecorded runtime leaks owner
      ⟨anchorControl.execution.application.attempt, event⟩
        (anchorControl.execution.recall owner) := by
    simpa only [same] using recorded
  have request := phase_recorded_unfinished_request runtime leaks (menu) plan ordered maximal
    inputs horizon scheduler anchorControl anchorTrace owner event currentRecorded unfinished
  simpa only [same] using request

end Vegas
