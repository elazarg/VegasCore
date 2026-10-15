/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseNativeTrace

/-! # Complete owner inputs under clear physical address erasure -/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseNativeProjection

open Interaction EventGraph GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))
  (plan : RuntimePhasePlan graph)

local notation "P" => phaseApplication runtime leaks
local notation "N" => runtime.reactiveApplication (nativeLeaks leaks plan)

/-- Response material is unchanged when restoring phase-addressed owner recall. -/
def liftAction (response : (N).Action) : (P).Action := ⟨response.transmission⟩

/-- Restore the public cursor and all known physical packet tags. -/
def liftPlayerView (view : (N).PlayerView) : (P).PlayerView :=
  ⟨view.messages.mapPayload plan.stampPacket,
    (view.application, restorePublic plan view.application.publicView), view.receipts⟩

def liftPlayerEntry (entry : (N).PlayerEntry) : (P).PlayerEntry :=
  ⟨liftPlayerView runtime leaks plan entry.beforeView,
    liftAction runtime leaks plan entry.action,
    entry.emitted.map (Message.mapPayload plan.stampPacket)⟩

/-- Every actual clear owner view is restored exactly, including its candidate
catalogue, complete semantic observation, public cursor and known packets. -/
theorem liftPlayerView_of_clear (bounds : MessageBounds graph) (inputs : PMF graph.Inputs)
    (horizon : Nat) (scheduler : (P).Scheduler) {current}
    (trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some current))
    (clear : current.execution.application.current.excluded = ∅) (who : Player) :
    liftPlayerView runtime leaks plan
        ((execution runtime leaks plan current.execution).observe N who) =
      current.execution.observe P who := by
  have cursor := congrArg (fun view => view.application)
    (liftEnvironmentView_of_clear runtime leaks plan bounds inputs horizon scheduler trace clear)
  change restorePublic plan current.execution.application.current.native.publicView =
    current.execution.application.publicView at cursor
  have messages := congrArg (fun network => network.observe who)
    (network_retag_of_clear runtime leaks plan bounds inputs horizon scheduler trace clear)
  simp only [MessageNetwork.mapPayload_observe] at messages
  change MessageNetwork.PlayerView.mapPayload plan.stampPacket
      ((current.execution.network.observe who).mapPayload CommitAttemptPacket.packet) =
        current.execution.network.observe who at messages
  change (⟨_, (current.execution.application.current.native.playerView who,
      restorePublic plan current.execution.application.current.native.publicView),
      current.execution.receipts⟩ : (P).PlayerView) = _
  rw [cursor]
  exact congrArg (fun known => (⟨known, current.execution.application.playerView who,
    current.execution.receipts⟩ : (P).PlayerView)) messages

private def ClearPlayerRecall (state : (P).ProtocolState) : Prop :=
  match state with
  | none => True
  | some current => current.execution.application.current.excluded = ∅ → ∀ who,
      ((current.execution.recall who).map (playerEntry runtime leaks plan)).map
        (liftPlayerEntry runtime leaks plan) = current.execution.recall who

private theorem clearPlayerRecall_history (bounds : MessageBounds graph)
    (inputs : PMF graph.Inputs) (horizon : Nat) (scheduler : (P).Scheduler) :
    ∀ {state} (_trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace state),
      ClearPlayerRecall runtime leaks plan state
  | _, .start => trivial
  | _, @Trace.extend _ _ source target before joint legal realized => by
      have inherited := clearPlayerRecall_history bounds inputs horizon scheduler before
      have reached : target ∈ ((P).transition
          (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler source joint).support :=
        realized
      cases source with
      | none =>
          obtain ⟨initial, _supported, rfl⟩ := PMF.support_map .. ▸ reached
          intro _clear who
          rfl
      | some current =>
          rcases current with ⟨remaining, actor, current⟩
          cases actor with
          | some who =>
              cases (PMF.mem_support_pure_iff _ _).mp reached
              intro clear observer
              let response := (joint who).getD ⟨none⟩
              have monotone := (phaseApplication_exclusion_monotone runtime leaks).respond current
                who response
              have beforeClear : current.application.current.excluded = ∅ :=
                Finset.subset_empty.mp (clear ▸ monotone)
              have previous := inherited beforeClear observer
              have visible := liftPlayerView_of_clear runtime leaks plan bounds inputs horizon
                scheduler before beforeClear who
              change liftPlayerView runtime leaks plan
                (playerView runtime leaks plan (current.observe P who)) =
                  current.observe P who at visible
              change (((current.respond P who response).recall observer).map
                (playerEntry runtime leaks plan)).map (liftPlayerEntry runtime leaks plan) = _
              by_cases same : observer = who
              · subst observer
                rcases responseEq : response with ⟨transmission⟩
                cases transmission with
                | none =>
                    change (joint who).getD ⟨none⟩ = ⟨none⟩ at responseEq
                    simp only [responseEq, ReactiveApplication.Execution.respond, ↓reduceIte,
                      List.map_append, List.map_cons, List.map_nil, playerEntry, liftPlayerEntry,
                      visible, action, liftAction, Option.map_none]
                    rw [previous]
                | some material =>
                    change (joint who).getD ⟨none⟩ = ⟨some material⟩ at responseEq
                    let envelope := (current.network.submit who
                      ((current.application.submit who material).emit who
                        (current.network.known who) material)).1
                    have authored : envelope ∈ (current.respond P who response).network.inputs := by
                      change envelope ∈
                        (current.respond P who ((joint who).getD ⟨none⟩)).network.inputs
                      rw [responseEq]
                      simp only [ReactiveApplication.Execution.respond,
                        MessageNetwork.submit, List.mem_append, List.mem_singleton]
                      exact Or.inr rfl
                    have restored := PhaseCount.stamp_nativeMessage_of_clear runtime leaks plan
                      bounds inputs horizon scheduler
                      (.extend before joint legal realized) clear envelope authored
                    have emitted : Message.mapPayload plan.stampPacket
                        (Message.mapPayload CommitAttemptPacket.packet envelope) = envelope := by
                      cases envelopeEq : envelope with
                      | mk id payload =>
                          rw [envelopeEq] at restored
                          exact congrArg (Message.mk id) restored
                    simp only [responseEq, ReactiveApplication.Execution.respond, ↓reduceIte,
                      List.map_append, List.map_cons, List.map_nil, playerEntry, liftPlayerEntry,
                      visible, action, liftAction, Option.map_some]
                    erw [emitted]
                    rw [previous]
                    rfl
              · rw [(P).respond_recall_other current who observer same response]
                exact previous
          | none =>
              cases remaining with
              | zero => exact (legal.1 ⟨rfl, rfl⟩).elim
              | succ remaining =>
                  obtain ⟨chosen, _selected, moved⟩ :=
                    Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
                  obtain ⟨next, supported, rfl⟩ := PMF.support_map .. ▸ moved
                  intro clear who
                  have monotone :=
                    (phaseApplication_exclusion_monotone runtime leaks).environmentStep
                      current next chosen supported
                  have previous := inherited (Finset.subset_empty.mp (clear ▸ monotone)) who
                  rw [(P).environmentStep_recall current next chosen supported]
                  exact previous

/-- Full owner recall, rather than only the current semantic observation, is
restored from every genuine clear native projection. -/
theorem playerRecall_lift_of_clear (bounds : MessageBounds graph) (inputs : PMF graph.Inputs)
    (horizon : Nat) (scheduler : (P).Scheduler) {current}
    (trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some current))
    (clear : current.execution.application.current.excluded = ∅) (who : Player) :
    ((execution runtime leaks plan current.execution).recall who).map
        (liftPlayerEntry runtime leaks plan) = current.execution.recall who :=
  clearPlayerRecall_history runtime leaks plan bounds inputs horizon scheduler trace clear who

/-- The same owner policy evaluated on the reconstructed complete physical input. -/
def nativePolicy (policy : (P).Policy) : (N).Policy := fun past view =>
  (policy (past.map (liftPlayerEntry runtime leaks plan))
    (liftPlayerView runtime leaks plan view)).map (action runtime leaks plan)

/-- The complete response distribution is unchanged at every actual clear input;
no source-belief or action-kernel agreement is assumed. -/
theorem nativePolicy_at_clear (bounds : MessageBounds graph) (inputs : PMF graph.Inputs)
    (horizon : Nat) (scheduler : (P).Scheduler) {current}
    (trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some current))
    (clear : current.execution.application.current.excluded = ∅) (who : Player)
    (policy : (P).Policy) :
    nativePolicy runtime leaks plan policy
        ((execution runtime leaks plan current.execution).recall who)
        ((execution runtime leaks plan current.execution).observe N who) =
      (policy (current.execution.recall who) (current.execution.observe P who)).map
        (action runtime leaks plan) := by
  unfold nativePolicy
  rw [playerRecall_lift_of_clear runtime leaks plan bounds inputs horizon scheduler trace clear who,
    liftPlayerView_of_clear runtime leaks plan bounds inputs horizon scheduler trace clear who]

end Vegas.EventGraphRuntime.PhaseNativeProjection
