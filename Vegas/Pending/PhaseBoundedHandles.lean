/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseSignedBindings
import Vegas.Pending.PhaseOwnCommitments
import Vegas.Pending.PhaseCountMenu

/-! # Surviving phased handles remain in the finite raw message domain -/

noncomputable section

namespace Vegas.EventGraphRuntime.MessageBounds

open Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (bounds : MessageBounds graph) (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks

/-- Every emitted call of the actual finite raw menu obeys its wire domain,
including obsolete namespaces and privately prepared unusable bindings. -/
theorem phaseNetworkBounds_history (menu : (app).ResponseMenu)
    (included : menu.IncludedIn (PhaseCount.rawMenu runtime leaks bounds))
    (initial : PMF (app).State) (horizon : Nat) (scheduler : (app).Scheduler) {control}
    (trace : (menu.protocol initial horizon scheduler).Trace (some control)) :
    control.execution.network.Satisfies fun message =>
      bounds.AllowsPacket message.payload.packet.call := by
  let safe : Message Player (CommitAttemptPacket graph) → Prop :=
    fun message => bounds.AllowsPacket message.payload.packet.call
  have invariant : menu.ServiceInvariant scheduler (fun execution =>
      execution.network.Satisfies safe) := {
    respond := by
      intro execution who action valid legal
      rcases action with ⟨_ | material⟩
      · exact valid
      · apply valid.submit who
        have bounded := included who _ _ legal
        rw [PhaseCount.rawMenu, ReactiveApplication.ResponseMenu.fromSubmissions_mem] at bounded
        change bounds.AllowsPacket
          ((execution.application.submit who material).emit who
            (execution.network.known who) material).packet.call
        rw [phase_emit_call]
        exact ((bounds.submissions_mem _ _).mp bounded).1.1
    environment := by
      intro execution next command valid _ moved
      cases command with
      | wait =>
          simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map] at moved
          cases (PMF.mem_support_pure_iff _ _).mp moved
          exact valid
      | activate who =>
          obtain ⟨updated, supported, rfl⟩ := PMF.support_map .. ▸ moved
          obtain ⟨selected, _, rfl⟩ := PMF.support_map .. ▸ supported
          exact valid.learn who selected
      | «include» id =>
          simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map] at moved
          cases (PMF.mem_support_pure_iff _ _).mp moved
          change (execution.includePending app id).network.Satisfies safe
          rw [ReactiveApplication.includePending_network]
          exact valid.includePending id
      | application command =>
          obtain ⟨updated, supported, rfl⟩ := PMF.support_map .. ▸ moved
          obtain ⟨state, _, rfl⟩ := PMF.support_map .. ▸ supported
          exact valid }
  exact invariant.history initial horizon
    (fun _ _ => MessageNetwork.Satisfies.empty) trace

/-- Both saved and live accepted handles are encodable after every actual
bounded phased history, even after resets and arbitrary earlier deviations. -/
theorem phaseAcceptedHandles_history (menu : (app).ResponseMenu)
    (included : menu.IncludedIn (PhaseCount.rawMenu runtime leaks bounds))
    (plan : RuntimePhasePlan graph) (inputs : PMF graph.Inputs) (horizon : Nat)
    (scheduler : (app).Scheduler) {control}
    (trace : (menu.protocol (inputs.map (PhaseRuntimeState.initial plan))
      horizon scheduler).Trace (some control)) :
    bounds.AcceptedHandles control.execution.application.entry.native ∧
      bounds.AcceptedHandles control.execution.application.current.native := by
  have network := bounds.phaseNetworkBounds_history runtime leaks menu included _ horizon scheduler
    trace
  have raw := menu.toRawTrace (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler trace
  have signed := phaseSignedBindings_history runtime leaks plan inputs horizon scheduler raw
  have input := (app).history_inputRecall _ horizon scheduler raw
  have bounded (state : State graph)
      (valid : SignedBindingTable (fun who => (app).outputs (control.execution.recall who)) state) :
      bounds.AcceptedHandles state := by
    intro field candidate accepted
    cases field with
    | inl initial =>
        have fixed := valid.1 initial candidate accepted
        change (match candidate.2 with
          | .initial _ => True
          | .prepared serial => serial < bounds.candidateCount)
        rw [fixed]
        trivial
    | inr event =>
        obtain ⟨message, member, _, sent⟩ := valid.2 event candidate accepted
        change message ∈ (app).outputs (control.execution.recall candidate.1) at member
        rw [← input candidate.1] at member
        have packet := network.inputs message (List.mem_filter.mp member).1
        rw [sent] at packet
        exact packet
  exact ⟨bounded _ signed.1, bounded _ signed.2.1⟩

end Vegas.EventGraphRuntime.MessageBounds
