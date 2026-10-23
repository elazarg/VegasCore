/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Pending.ReservedEpochExpiredRequest
import Vegas.Pending.ReservedEpochFreshResponse
import Vegas.Game.PhaseProposalUnflaggedOpening
import Interaction.ReactiveAnchoredMixture

/-! # Origins of actual publication expiry under the unflagged continuation -/

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

/-- A publication that expires under the actual unflagged continuation had
an old callback at the anchor, or its genuine first callback had no usable
locked value and was forced to WAIT. Guard rejection is not a service expiry. -/
theorem phaseProposalUnflagged_opening_expiry_origin
    (coveredValues : bounds.CoversOutputValues)
    (maximal : plan.phases.IsChain fun first last =>
      first.kind ≠ last.kind ∨ first.kind = .sample)
    (ordered : (graph).RevealRelaxedOrdered)
    (values : ∀ who (key : setup.ProposalRecoveryComponent who),
      PMF (setup.CommitRecoveryValueChoice who key.1))
    {length : Nat} (tape : ReservedEpoch.Tape Player length)
    (activationGap processingGap : Nat)
    (gaps : tape.BoundedGaps (ReservedEpoch.completionCycles runtime)
      activationGap processingGap)
    (margin : runtime.AsyncTimely (fun _ => activationGap + 1) (fun _ => processingGap + 1))
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
    (owner : Player) (event : (graph).EventId) (payload : L.Ty)
    (binding : FieldRef (graph).layout (.binding owner payload))
    (checks : List (GuardCheck (graph).layout payload))
    (outputEq : (graph).outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventCode (graph).layout) outputEq) ((graph).nodes event) =
      .resolve owner payload binding checks)
    (node : nodeView graph event = .resolve owner payload binding checks outputEq codeEq)
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
      ⟨dueControl.execution.application.attempt, event⟩ (anchorControl.execution.recall owner) ∨
      ∃ (remaining : Nat) (execution : (app).Execution)
        (prior : ((menu).protocol ((inputs).map (PhaseRuntimeState.initial plan))
          (ReservedEpoch.executionHorizon runtime)
            (ReservedEpoch.family runtime leaks (ReservedEpoch.packetCapacity runtime) tape)).Trace
              (some ⟨remaining, some owner, execution⟩)) (entry : (app).PlayerEntry),
        TracePrefix prior dueTrace ∧ entry ∈ dueControl.execution.recall owner ∧
        entry.beforeView = execution.observe app owner ∧
        execution.application.SeedRequest owner
          ⟨dueControl.execution.application.attempt, event⟩ ∧
        ¬ PhaseCount.ResponseRecorded runtime leaks owner
          ⟨dueControl.execution.application.attempt, event⟩ (execution.recall owner) ∧
        (¬ ∃ value : L.Val payload,
          binding.get? execution.application.current.native.config.store = some (.success value)) ∧
        entry.action.transmission = none := by
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
  by_cases recorded : PhaseCount.ResponseRecorded runtime leaks owner
      ⟨dueControl.execution.application.attempt, event⟩ (anchorControl.execution.recall owner)
  · exact Or.inl recorded
  · have absent := recorded
    obtain ⟨before, prior, entry, priorKept, acting, member, viewed, offered, requested,
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
    by_cases usable : ∃ value : L.Val payload,
        binding.get? execution.application.current.native.config.store = some (.success value)
    · obtain ⟨value, stored⟩ := usable
      have bounded : (⟨payload, value⟩ : Raw L) ∈ bounds.values := by
        have covered := coveredValues event
        rw [outputEq] at covered
        exact covered value
      rw [viewed] at selected
      obtain ⟨candidate, material, accepted, transmitted, call⟩ :=
        phaseProposalUnflaggedOpening_supported_truthful setup mode runtime leaks bounds plan values
          inputs horizon scheduler remaining owner execution prior event payload binding checks
            outputEq codeEq node currentRequest currentUnsent value stored bounded entry.action
              selected
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
      have certificate : ReservedEpoch.ReadyCall execution.application material.call.packet event :=
        .opening owner payload binding checks outputEq codeEq node candidate ⟨payload, value⟩
          call accepted
      exact (ReservedEpoch.first_ready_response_cannot_expire runtime leaks tape activationGap
        processingGap gaps margin bounds plan ordered maximal inputs remaining owner execution prior
          event currentRequest currentFirst material certificate offered rawPost dueControl
            ((menu).toRawTrace _ horizon scheduler dueTrace) dueRequest atDeadline expired
              expiryRemaining expiry rawExpiry path players consistent coverage).elim
    · refine Or.inr ⟨remaining, execution, prior, entry, priorKept, member, viewed, requested,
        first, usable, ?_⟩
      cases transmitted : entry.action.transmission with
      | none => rfl
      | some material =>
          have actionEq : entry.action = (⟨some material⟩ : (app).Action) :=
            congrArg (fun transmission => (⟨transmission⟩ : (app).Action)) transmitted
          have offered' : (⟨some material⟩ : (app).Action) ∈
              PhaseCount.onePacketActions runtime leaks bounds owner (execution.recall owner)
                (execution.observe app owner) := by simpa only [actionEq] using offered
          obtain ⟨candidate, value, _call, stored, _accepted, _fixed⟩ :=
            PhaseCount.onePacket_opening_shape runtime leaks bounds plan ordered inputs horizon
              scheduler remaining owner execution prior event payload binding checks outputEq codeEq
                node currentRequest material offered'
          exact (usable ⟨value, stored⟩).elim

end Vegas
