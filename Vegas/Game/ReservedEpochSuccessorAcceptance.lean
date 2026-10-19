/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.ReservedEpochBindingReadiness
import Vegas.Pending.PhaseSuccessorRecall
import Vegas.Pending.ReservedEpochFirstAcceptance
import Vegas.Pending.PhaseBindingMenuShape

/-! # Protected real successor submissions after an owned binding advances -/

noncomputable section

namespace Vegas.EventGraphRuntime.ReservedEpoch

open SourceProgram EventGraph Interaction GameTheory.Math.Probability

variable {Player : Type} [Fintype Player] [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {Γ : SourceCtx Player L} {O : Finset VarId}
  (program : SourceProgram Player L Γ O)

local notation "graph" =>
  EventGraph.withMode (toEventGraph program) EventGraph.ExecutionMode.concurrentReveals

/-- Actual unchanged own recall across a predecessor's completion makes the
successor's present offer its first offer. The compiled same-owner edge is
derived from the two real binding declarations, rather than assumed. -/
theorem successor_response_receipt (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))
    {length : Nat} (tape : Tape Player length) (activationGap processingGap : Nat)
    (gaps : tape.BoundedGaps (completionCycles runtime) activationGap processingGap)
    (margin : runtime.AsyncTimely (fun _ => activationGap + 1) (fun _ => processingGap + 1))
    (bounds : MessageBounds graph) (plan : RuntimePhasePlan graph)
    (ordered : (graph).RevealRelaxedOrdered)
    (maximal : plan.phases.IsChain fun before after =>
      before.kind ≠ after.kind ∨ before.kind = .sample)
    (inputs : PMF (graph).Inputs) (priorControl : (phaseApplication runtime leaks).Control)
    (prior : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) (executionHorizon runtime)
        (family runtime leaks (packetCapacity runtime) tape)).Trace (some priorControl))
    (remaining : Nat) (owner : Player) (execution : (phaseApplication runtime leaks).Execution)
    (trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) (executionHorizon runtime)
        (family runtime leaks (packetCapacity runtime) tape)).Trace
          (some ⟨remaining, some owner, execution⟩))
    (event predecessor : (graph).EventId) (payload priorPayload : L.Ty)
    (binding : (graph).outputLayout event = .binding owner payload)
    (priorBinding : (graph).outputLayout predecessor = .binding owner priorPayload)
    (earlier : predecessor.val < event.val)
    (unfinished : predecessor ∉
      priorControl.execution.application.current.native.config.cut.completed)
    (sameAttempt : priorControl.execution.application.attempt = execution.application.attempt)
    (sameRecall : priorControl.execution.recall owner = execution.recall owner)
    (request : execution.application.SeedRequest owner ⟨execution.application.attempt, event⟩)
    (material : WitnessedSubmission graph)
    (offered : (⟨some material⟩ : (phaseApplication runtime leaks).Action) ∈
      PhaseCount.onePacketActions runtime leaks bounds owner (execution.recall owner)
        (execution.observe (phaseApplication runtime leaks) owner))
    (players : Player → (phaseApplication runtime leaks).Policy)
    (covered : ∀ past view action, action ∈ (players owner past view).support →
      action.transmission = none ∨
        PhaseCount.OnePacketResponse runtime leaks owner past view action)
    (final : (phaseApplication runtime leaks).Execution)
    (reached : final ∈ ((phaseApplication runtime leaks).runRounds
      (family runtime leaks (packetCapacity runtime) tape) players remaining
        (execution.respond (phaseApplication runtime leaks) owner ⟨some material⟩)).support) :
    ((owner, execution.network.nextSerial owner), true) ∈ final.receipts := by
  have dependency : predecessor ∈ (graph).order.predecessors event := by
    apply (binding_predecessors program event predecessor owner payload binding).mpr
    refine ⟨earlier, Or.inr ?_⟩
    rw [priorBinding]
    exact rfl
  have first := phase_unfinished_predecessor_no_response runtime leaks
    (PhaseCount.onePacketMenu runtime leaks bounds) plan inputs (executionHorizon runtime)
      (family runtime leaks (packetCapacity runtime) tape) priorControl prior owner event
        predecessor dependency unfinished
  rw [sameAttempt, sameRecall] at first
  let initial := inputs.map (PhaseRuntimeState.initial plan)
  let scheduler := family runtime leaks (packetCapacity runtime) tape
  let menu := PhaseCount.onePacketMenu runtime leaks bounds
  have raw := menu.toRawTrace initial (executionHorizon runtime) scheduler trace
  obtain ⟨_draw, valid⟩ := phaseNativeInvariant_history runtime leaks plan inputs
    (executionHorizon runtime) scheduler raw
  obtain ⟨entered, stamp⟩ := Option.isSome_iff_exists.mp
    ((valid.active.activated_iff event).mpr
      ⟨request.2.2.1, by rw [request.2.2.2.1]; rfl⟩)
  obtain ⟨serial, _preparation, _evidence, declared, _bounded, _fresh⟩ :=
    PhaseCount.onePacket_binding_shape runtime leaks bounds plan ordered inputs
      (executionHorizon runtime) scheduler remaining owner execution trace event payload binding
        request material offered
  have certificate : ReadyCall execution.application material.call.packet event :=
    .binding (owner, .prepared serial)
      (congrArg (fun value : WitnessedSubmission graph => value.call.packet) declared)
  have permitted : PhaseCount.OnePacketResponse runtime leaks owner (execution.recall owner)
      (execution.observe (phaseApplication runtime leaks) owner) ⟨some material⟩ := by
    rcases ((PhaseCount.mem_onePacketActions runtime leaks bounds owner _ _ _).mp offered).2
      with silent | transmitted
    · cases silent
    · exact transmitted
  have countClean := (PhaseCount.onePacketMenu_countClean runtime leaks bounds scheduler).history
    initial (executionHorizon runtime) (fun state _ => PhaseCount.countClean_initial runtime leaks
      state) trace
  have clean : PhaseCount.OwnCountClean runtime leaks owner execution :=
    ⟨countClean.1, fun message present _ => countClean.2 message present⟩
  exact first_response_receipt runtime leaks tape activationGap processingGap gaps margin plan
    ordered maximal inputs remaining owner execution raw event entered request stamp first clean
      material certificate permitted players covered final reached

end Vegas.EventGraphRuntime.ReservedEpoch
