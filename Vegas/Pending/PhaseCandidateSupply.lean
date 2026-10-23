/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Pending.ReactiveCandidateBudget
import Vegas.Pending.PhaseApplication

/-! # Prepared candidate supply across physical phase rollback

Only an owner's actual binding response can occupy a prepared candidate.
Rollback preserves its catalogue and full response recall, so the same finite
response budget bounds fresh serials across all attempts and phases.
-/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseCandidates

open Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

def responseCandidateSlot (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))
    (response : (phaseApplication runtime leaks).Action) : Option Nat :=
  match response.transmission with
  | some material => material.call.packet.preparedCommitment?
  | _ => none

def submittedCandidateSlots (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))
    (past : List (phaseApplication runtime leaks).PlayerEntry) : List Nat :=
  (past.map ReactiveApplication.PlayerEntry.action).filterMap (responseCandidateSlot runtime leaks)

def CandidateRecall (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))
    (execution : (phaseApplication runtime leaks).Execution) : Prop :=
  ∀ who serial, serial ∉ submittedCandidateSlots runtime leaks (execution.recall who) →
    execution.application.current.native.candidates.lookup (who, .prepared serial) = .fresh

theorem submittedCandidateSlots_respond (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))
    (execution : (phaseApplication runtime leaks).Execution) (who : Player)
    (response : (phaseApplication runtime leaks).Action) :
    submittedCandidateSlots runtime leaks
        ((execution.respond (phaseApplication runtime leaks) who response).recall who) =
      submittedCandidateSlots runtime leaks (execution.recall who) ++
        (responseCandidateSlot runtime leaks response).toList := by
  rw [submittedCandidateSlots, ReactiveApplication.respond_actions]
  simp only [List.filterMap_append, List.filterMap_cons, List.filterMap_nil]
  cases responseCandidateSlot runtime leaks response <;> rfl

theorem candidateRecall_respond (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))
    (execution : (phaseApplication runtime leaks).Execution) (who : Player)
    (response : (phaseApplication runtime leaks).Action)
    (valid : CandidateRecall runtime leaks execution) :
    CandidateRecall runtime leaks
      (execution.respond (phaseApplication runtime leaks) who response) := by
  intro observer serial absent
  have old : serial ∉ submittedCandidateSlots runtime leaks (execution.recall observer) := by
    intro present
    apply absent
    unfold submittedCandidateSlots at present ⊢
    exact List.mem_filterMap.mpr (by
      obtain ⟨action, member, slot⟩ := List.mem_filterMap.mp present
      obtain ⟨entry, retained, rfl⟩ := List.mem_map.mp member
      exact ⟨entry.action, List.mem_map.mpr
        ⟨entry, (phaseApplication runtime leaks).respond_recall_mono
          execution who observer response retained, rfl⟩, slot⟩)
  have fresh := valid observer serial old
  rcases response with ⟨transmission⟩
  cases transmission with
  | none => exact fresh
  | some material =>
      apply Eq.trans (submission_candidate_other execution.application.current.native
        who observer serial
        material.call ?_) fresh
      by_cases same : observer = who
      · subst observer
        right
        rw [submittedCandidateSlots_respond] at absent
        intro selected
        apply absent
        apply List.mem_append_right
        change serial ∈ material.call.packet.preparedCommitment?.toList
        simp [selected]
      · exact Or.inl same

private theorem emit_call (state : PhaseRuntimeState graph) (who : Player)
    (known : List (Message Player (CommitAttemptPacket graph)))
    (material : WitnessedSubmission graph) :
    (state.emit who known material).packet.call = material.call.packet := by
  have nativeCall : (state.current.emit who
      (known.map fun message => ⟨message.id, message.payload.packet⟩) material).call =
      material.call.packet := by
    unfold RecoveryState.emit
    dsimp only
    split <;> rfl
  unfold PhaseRuntimeState.emit
  dsimp only
  split <;> exact nativeCall

private theorem issued_candidate_slot (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))
    (execution : (phaseApplication runtime leaks).Execution)
    (message : Message Player (CommitAttemptPacket graph)) (event : graph.EventId)
    (owner : Player) (serial : Nat)
    (call : message.payload.packet.call = .commitment event (owner, .prepared serial))
    (issued : execution.Issued (phaseApplication runtime leaks) message) :
    serial ∈ submittedCandidateSlots runtime leaks (execution.recall message.sender) := by
  obtain ⟨entry, member, material, sent, _, state, known, packet⟩ := issued
  apply List.mem_filterMap.mpr
  refine ⟨entry.action, List.mem_map.mpr ⟨entry, member, rfl⟩, ?_⟩
  have raw := congrArg (fun packet : CommitAttemptPacket graph => packet.packet.call) packet
  rw [show ((phaseApplication runtime leaks).packet
    state message.sender known material).packet.call = material.call.packet from
      emit_call state message.sender known material] at raw
  simp only [responseCandidateSlot, sent, raw, call, Payload.preparedCommitment?]

private theorem candidateRecall_handle (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))
    (execution : (phaseApplication runtime leaks).Execution) (next : PhaseRuntimeState graph)
    (message : Message Player (CommitAttemptPacket graph))
    (valid : CandidateRecall runtime leaks execution)
    (issued : execution.Issued (phaseApplication runtime leaks) message)
    (accepted : execution.application.handle runtime message = some next)
    (who : Player) (serial : Nat)
    (absent : serial ∉ submittedCandidateSlots runtime leaks (execution.recall who)) :
    next.current.native.candidates.lookup (who, .prepared serial) = .fresh := by
  unfold PhaseRuntimeState.handle at accepted
  split at accepted
  · obtain ⟨native, handled, rfl⟩ := Option.map_eq_some_iff.mp accepted
    dsimp only [PhaseRuntimeState.normalize]
    rw [(PhaseRuntimeState.settle_physical _ _ _ _ _).2.1]
    change native.candidates.lookup (who, .prepared serial) = .fresh
    cases call : message.payload.packet.call with
    | commitment event candidate =>
        rw [call] at handled
        obtain ⟨candidates, _, owner⟩ :=
          handle_commitment_tables runtime _ _ message.id event candidate handled
        have different : (who, Slot.prepared serial) ≠ candidate := by
          intro same
          subst candidate
          change who = message.sender at owner
          subst who
          exact absent (issued_candidate_slot runtime leaks execution message event
            message.sender serial call issued)
        rw [candidates, CommitmentCandidates.lookup_freeze_other _ _ _ different]
        exact valid who serial absent
    | opening event candidate raw =>
        rw [(handle_resolution_tables runtime _ _ _ (by
          intro event candidate impossible
          change message.payload.packet.call = .commitment event candidate at impossible
          rw [call] at impossible
          cases impossible) handled).2]
        exact valid who serial absent
    | malformed raw => simp [call, handle] at handled
  · cases accepted

theorem candidateRecall_environment (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))
    (execution next : (phaseApplication runtime leaks).Execution)
    (command : (phaseApplication runtime leaks).Command)
    (valid : CandidateRecall runtime leaks execution)
    (provenance : execution.Provenance (phaseApplication runtime leaks))
    (reached : next ∈ (execution.environmentStep (phaseApplication runtime leaks)
      command).support) : CandidateRecall runtime leaks next := by
  intro who serial absent
  rw [ReactiveApplication.environmentStep_recall _ execution next command reached] at absent
  cases command with
  | wait =>
      simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map] at reached
      cases (PMF.mem_support_pure_iff _ _).mp reached
      exact valid who serial absent
  | activate actor =>
      obtain ⟨updated, supported, rfl⟩ := PMF.support_map .. ▸ reached
      obtain ⟨selected, _, rfl⟩ := PMF.support_map .. ▸ supported
      exact valid who serial absent
  | «include» id =>
      simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map] at reached
      cases (PMF.mem_support_pure_iff _ _).mp reached
      unfold ReactiveApplication.Execution.includePending MessageNetwork.includePending
      cases found : execution.network.lookup id with
      | none => exact valid who serial absent
      | some message =>
          change (((phaseApplication runtime leaks).handle execution.application message).getD
            execution.application).current.native.candidates.lookup (who, .prepared serial) = _
          cases accepted : (phaseApplication runtime leaks).handle execution.application
              message with
          | none => exact valid who serial absent
          | some state =>
              exact candidateRecall_handle runtime leaks execution state message valid
                (provenance.pending message (List.mem_of_find?_eq_some found))
                accepted who serial absent
  | application command =>
      obtain ⟨updated, supported, rfl⟩ := PMF.support_map .. ▸ reached
      obtain ⟨state, changed, rfl⟩ := PMF.support_map .. ▸ supported
      change state ∈ (execution.application.environment runtime command).support at changed
      unfold PhaseRuntimeState.environment at changed
      split at changed
      · obtain ⟨native, moved, rfl⟩ := PMF.support_map .. ▸ changed
        dsimp only [PhaseRuntimeState.normalize]
        rw [(PhaseRuntimeState.settle_physical _ _ _ _ _).2.1]
        change native.candidates.lookup (who, .prepared serial) = .fresh
        rw [(environmentStep_tables runtime execution.application.current.native native command
          moved).2]
        exact valid who serial absent
      · cases (PMF.mem_support_pure_iff _ _).mp changed
        exact valid who serial absent

theorem candidateRecall_history (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))
    (plan : RuntimePhasePlan graph) (inputs : PMF graph.Inputs) (horizon : Nat)
    (scheduler : (phaseApplication runtime leaks).Scheduler) :
    ∀ {state} (_trace : ((phaseApplication runtime leaks).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace state),
      ReactiveApplication.serviceInvariant (CandidateRecall runtime leaks) state := by
  have invariant : (phaseApplication runtime leaks).ServiceInvariant scheduler
      (fun execution => CandidateRecall runtime leaks execution ∧
        execution.Provenance (phaseApplication runtime leaks)) := {
    respond := fun execution who action valid =>
      ⟨candidateRecall_respond runtime leaks execution who action valid.1,
        (phaseApplication runtime leaks).respond_provenance execution who action valid.2⟩
    environment := fun execution next command valid _ reached =>
      ⟨candidateRecall_environment runtime leaks execution next command valid.1 valid.2 reached,
        (phaseApplication runtime leaks).environment_provenance execution next command
          valid.2 reached⟩ }
  intro state trace
  have valid := invariant.history (inputs.map (PhaseRuntimeState.initial plan)) horizon (by
    intro state supported
    obtain ⟨input, _, rfl⟩ := PMF.support_map .. ▸ supported
    refine ⟨?_, MessageNetwork.Satisfies.empty⟩
    intro who serial _
    change (PhaseRuntimeState.initial plan input).current.native.candidates.lookup
      (who, .prepared serial) = .fresh
    unfold PhaseRuntimeState.initial
    rw [(PhaseRuntimeState.settle_physical _ _ _ _ _).2.1]
    exact State.initial_candidate input who (.prepared serial)) trace
  cases state with
  | none => trivial
  | some control => exact valid.1

/-- The least fresh serial is bounded by the owner's response count, regardless
of the magnitude of the identifiers it previously chose. -/
theorem reactiveFreshSlot_le_recall (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))
    (execution : (phaseApplication runtime leaks).Execution) (who : Player)
    (valid : CandidateRecall runtime leaks execution) :
    ∃ serial, serial ≤ (execution.recall who).length ∧
      reactiveFreshSlot
        (execution.observe (phaseApplication runtime leaks) who).application.1 = some serial := by
  classical
  let used := submittedCandidateSlots runtime leaks (execution.recall who)
  have count : used.toFinset.card ≤ (execution.recall who).length := by
    exact le_trans (List.toFinset_card_le used)
      ((List.length_filterMap_le _ _).trans (List.length_map _).le)
  have more : used.toFinset.card < (Finset.range ((execution.recall who).length + 1)).card := by
    simpa only [Finset.card_range] using Nat.lt_succ_of_le count
  obtain ⟨unused, available, absent⟩ := Finset.exists_mem_notMem_of_card_lt_card more
  have fresh := valid who unused (by simpa only [List.mem_toFinset] using absent)
  have bound : unused ≤ (execution.recall who).length :=
    Nat.lt_succ_iff.mp (Finset.mem_range.mp available)
  unfold reactiveFreshSlot
  split
  · rename_i existsFresh
    exact ⟨_, le_trans (Nat.find_min' existsFresh fresh) bound, rfl⟩
  · rename_i impossible
    exact (impossible ⟨unused, fresh⟩).elim

/-- A horizon of `horizon` scheduler decisions needs at most that many prepared
serials per player. The final active response is included in this bound. -/
theorem reactiveFreshSlot_lt_horizon (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))
    (plan : RuntimePhasePlan graph) (inputs : PMF graph.Inputs) (horizon : Nat)
    (scheduler : (phaseApplication runtime leaks).Scheduler)
    (control : (phaseApplication runtime leaks).Control)
    (trace : ((phaseApplication runtime leaks).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some control))
    (who : Player) (active : control.actor = some who) :
    ∃ serial, serial < horizon ∧ reactiveFreshSlot
      (control.execution.observe (phaseApplication runtime leaks) who).application.1 =
        some serial := by
  obtain ⟨serial, bounded, selected⟩ := reactiveFreshSlot_le_recall runtime leaks
    control.execution who
      (candidateRecall_history runtime leaks plan inputs horizon scheduler trace)
  exact ⟨serial, lt_of_le_of_lt bounded
    ((phaseApplication runtime leaks).active_recall_lt_horizon
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler control trace who active),
        selected⟩

end Vegas.EventGraphRuntime.PhaseCandidates
