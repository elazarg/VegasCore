/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseProposalBindingSettlement
import Vegas.Pending.PhaseOwnCommitments

/-! # Retained emission meanings across actual service operations -/

noncomputable section

namespace Vegas

open EventGraph EventGraphRuntime Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))
  (bounds : MessageBounds graph) (plan : RuntimePhasePlan graph)
  (inputs : PMF graph.Inputs) (horizon : Nat)
  (scheduler : (phaseApplication runtime leaks).Scheduler)

local notation "app" => phaseApplication runtime leaks
local notation "menu" => PhaseCount.onePacketMenu runtime leaks bounds
local notation "initial" => inputs.map (PhaseRuntimeState.initial plan)

/-- Every actual signed counted binding fixes the exact named physical slot,
including an unopenable or wrongly typed preparation. -/
theorem phaseProposal_input_binding_fixed
    (control : (app).Control)
    (trace : ((menu).protocol initial horizon scheduler).Trace (some control))
    (message : Message Player (CommitAttemptPacket graph))
    (member : message ∈ control.execution.network.inputs)
    (event : graph.EventId) (candidate : Handle graph)
    (named : message.payload.packet.call = .commitment event candidate) :
    control.execution.application.current.native.candidates.lookup candidate ≠ .fresh := by
  let raw := (menu).toRawTrace initial horizon scheduler trace
  have clean := (PhaseCount.onePacketMenu_countClean runtime leaks bounds scheduler).history
    initial horizon (fun state _ => PhaseCount.countClean_initial runtime leaks state) trace
  have correct := ((PhaseCount.permits_eq_true_iff _ _).mp (clean.2 message member)).2.1
  change CountCallCorrect _ (PhaseCount.nativeMessage message) at correct
  unfold CountCallCorrect at correct
  change (match message.payload.packet.call with
    | .commitment event candidate => _
    | .opening event candidate raw => _
    | .malformed raw => _) at correct
  rw [named] at correct
  have owner : candidate.1 = message.sender := correct.2.2.1
  have recalled := (app).history_inputRecall initial horizon scheduler raw
  have output : message ∈ (app).outputs (control.execution.recall candidate.1) := by
    rw [← recalled candidate.1]
    exact List.mem_filter.mpr ⟨member, by simp only [← owner, decide_true]⟩
  have fixed := phaseOwnCommitmentsFixed_history runtime leaks initial horizon scheduler raw
  exact fixed candidate.1 message output event candidate.2 named

omit [Fintype Player] in
/-- Rebase one real emitted packet through a physical fixed-candidate step
and a retaining ghost update. The probability of the response is untouched. -/
theorem phaseProposalEmittedBinding_kept
    (original next : (app).Execution) (phase : RuntimePhase graph)
    (frontier after : graph.Config)
    (emissions : PhaseProposalEmittedBindings runtime leaks original phase frontier)
    (message : Message Player (CommitAttemptPacket graph))
    (member : message ∈ original.network.inputs)
    (event : graph.EventId) (inside : event ∈ phase.events) (candidate : Handle graph)
    (named : message.payload.packet.call = .commitment event candidate)
    (current : message.payload.attempt = next.application.attempt)
    (attempt : original.application.attempt = next.application.attempt)
    (fixed : original.application.current.native.candidates.lookup candidate ≠ .fresh)
    (retained : KeepsFixedCandidates original.application.current.native
      next.application.current.native)
    (kept : ∀ field value, frontier.store field = some value → after.store field = some value)
    (owner : Player) (payload : L.Ty)
    (binding : graph.outputLayout event = .binding owner payload) :
    (⟨.inr event, binding⟩ : FieldRef graph.layout (.binding owner payload)).get? after.store =
      some (next.application.current.native.bindingResult candidate payload) := by
  have before := emissions message member (current.trans attempt.symm) event inside candidate
    named owner payload binding
  have lookup := retained candidate fixed
  have meaning : next.application.current.native.bindingResult candidate payload =
      original.application.current.native.bindingResult candidate payload := by
    simp only [State.bindingResult, lookup]
  rw [meaning]
  exact (⟨.inr event, binding⟩ : FieldRef graph.layout (.binding owner payload)).get?_preserved
    frontier.store after.store kept _ before

/-- Every actual service command preserves exactly the retained emission
cylinder in the original namespace. Pending and rejected packets remain in
that same cylinder; their immutable preparation meanings are not redrawn. -/
theorem phaseProposalEmittedBindings_environment
    (control : (app).Control)
    (trace : ((menu).protocol initial horizon scheduler).Trace (some control))
    (next : (app).Execution) (command : (app).Command)
    (supported : next ∈ (control.execution.environmentStep (app) command).support)
    (phase : RuntimePhase graph) (frontier : graph.Config)
    (attempt : control.execution.application.attempt = next.application.attempt) :
    PhaseProposalEmittedBindings runtime leaks control.execution phase frontier ↔
      PhaseProposalEmittedBindings runtime leaks next phase frontier := by
  have inputsEq := (app).environmentStep_inputs control.execution next command supported
  have fixed := (phaseApplication_preservesFixedCandidates runtime leaks).environmentStep
    control.execution next command supported
  constructor
  · intro emissions message member current event inside candidate named owner payload binding
    have old : message ∈ control.execution.network.inputs := by rwa [inputsEq] at member
    exact phaseProposalEmittedBinding_kept runtime leaks control.execution next phase frontier
      frontier emissions message old event inside candidate named current attempt
      (phaseProposal_input_binding_fixed runtime leaks bounds plan inputs horizon scheduler control
        trace message old event candidate named) fixed (fun _ _ stored => stored)
      owner payload binding
  · intro emissions message member current event inside candidate named owner payload binding
    have newer : message ∈ next.network.inputs := by rwa [inputsEq]
    have stored := emissions message newer (current.trans attempt) event inside candidate named
      owner payload binding
    have lookup := fixed candidate
      (phaseProposal_input_binding_fixed runtime leaks bounds plan inputs horizon scheduler control
        trace message member event candidate named)
    simpa only [State.bindingResult, lookup] using stored

end Vegas
