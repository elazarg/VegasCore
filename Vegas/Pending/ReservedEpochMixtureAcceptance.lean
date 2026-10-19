/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReservedEpochFirstAcceptance
import Interaction.ReactiveSchedulerSeedTrace

/-! # Genuine first packet acceptance under the correlated behavioral service -/

noncomputable section

namespace Vegas.EventGraphRuntime.ReservedEpoch

open EventGraph Interaction GameTheory.Math.Probability

variable {Player : Type} [Fintype Player] [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks

theorem implementation_first_response_receipt {length : Nat}
    (prior : PMF (Tape Player length)) (activationGap processingGap : Nat)
    (gaps : ∀ tape ∈ prior.support,
      tape.BoundedGaps (completionCycles runtime) activationGap processingGap)
    (margin : runtime.AsyncTimely (fun _ => activationGap + 1) (fun _ => processingGap + 1))
    (plan : RuntimePhasePlan graph) (ordered : graph.RevealRelaxedOrdered)
    (maximal : plan.phases.IsChain fun before after =>
      before.kind ≠ after.kind ∨ before.kind = .sample)
    (inputs : PMF graph.Inputs) (remaining : Nat) (owner : Player) (execution : (app).Execution)
    (trace : ((app).protocol (inputs.map (PhaseRuntimeState.initial plan))
      (executionHorizon runtime)
        (implementation runtime leaks (packetCapacity runtime) prior).scheduler).Trace
        (some ⟨remaining, some owner, execution⟩))
    (event : graph.EventId) (entered : Nat)
    (request : execution.application.SeedRequest owner ⟨execution.application.attempt, event⟩)
    (stamp : execution.application.current.native.activatedAt event = some entered)
    (first : ¬ PhaseCount.ResponseRecorded runtime leaks owner
      ⟨execution.application.attempt, event⟩ (execution.recall owner))
    (clean : PhaseCount.OwnCountClean runtime leaks owner execution)
    (material : WitnessedSubmission graph)
    (certificate : ReadyCall execution.application material.call.packet event)
    (permitted : PhaseCount.OnePacketResponse runtime leaks owner (execution.recall owner)
      (execution.observe app owner) ⟨some material⟩)
    (players : Player → (app).Policy)
    (covered : ∀ past view action, action ∈ (players owner past view).support →
      action.transmission = none ∨
        PhaseCount.OnePacketResponse runtime leaks owner past view action)
    (final : (app).Execution)
    (reached : final ∈ ((app).runRounds
      (implementation runtime leaks (packetCapacity runtime) prior).scheduler players remaining
        (execution.respond app owner ⟨some material⟩)).support) :
    ((owner, execution.network.nextSerial owner), true) ∈ final.receipts := by
  let initial := inputs.map (PhaseRuntimeState.initial plan)
  let impl := implementation runtime leaks (packetCapacity runtime) prior
  let fixed : Tape Player length → (app).Scheduler :=
    family runtime leaks (packetCapacity runtime)
  let after := execution.respond app owner ⟨some material⟩
  obtain ⟨tape, posterior⟩ := (impl.posterior final.environmentRecall).support_nonempty
  have joined : (final, tape) ∈ (((app).runRounds impl.scheduler players remaining after).bind
      fun next => (impl.posterior next.environmentRecall).map (Prod.mk next)).support := by
    rw [PMF.support_bind]
    exact Set.mem_iUnion₂.mpr ⟨final, reached,
      (PMF.mem_support_map_iff _ _ _).mpr ⟨tape, posterior, rfl⟩⟩
  rw [← impl.realizeJoint players remaining after] at joined
  obtain ⟨chosen, chosenSupport, actual⟩ :=
    Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ joined)
  change (final, tape) ∈ (((app).schedulerMixture prior fixed).runJoint
    players remaining after chosen).support at actual
  rw [(app).schedulerMixture_runJoint prior fixed players remaining after chosen] at actual
  obtain ⟨result, resultSupport, same⟩ := (PMF.mem_support_map_iff _ _ _).mp actual
  cases same
  have beforeSupport : tape ∈ (impl.posterior execution.environmentRecall).support := by
    simpa only [after, (app).respond_environmentRecall] using chosenSupport
  obtain ⟨original, ⟨fixedTrace⟩⟩ :=
    (app).schedulerMixture_trace_of_posterior_support prior fixed initial
      (executionHorizon runtime) ⟨remaining, some owner, execution⟩ trace tape beforeSupport
  exact first_response_receipt runtime leaks tape activationGap processingGap
    (gaps tape original) margin plan ordered maximal inputs remaining owner execution fixedTrace
      event entered request stamp first clean material certificate permitted players covered
        final resultSupport

end Vegas.EventGraphRuntime.ReservedEpoch
