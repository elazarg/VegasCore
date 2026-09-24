/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.ReactiveProvenance
import Interaction.ReactiveServiceInvariant
import Interaction.ReactiveResponseBudget
import Vegas.Pending.ReactivePolicy

/-! # Finite candidate supply from actual response counts

Only an owner's submission can occupy its prepared candidate. Inclusion and
replay cannot reserve an additional candidate. Counting slots mentioned by the
owner's own responses bounds the least fresh serial, including after deviations.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

def Payload.preparedCommitment? : Payload graph → Option Nat
  | .commitment _ (_, .prepared serial) => some serial
  | _ => none

def responseCandidateSlot (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (response : (runtime.reactiveApplication leaks).Action) : Option Nat :=
  match response.transmission with
  | some (.submit material) => material.call.packet.preparedCommitment?
  | _ => none

def submittedCandidateSlots (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (past : List (runtime.reactiveApplication leaks).PlayerEntry) : List Nat :=
  (past.map ReactiveApplication.PlayerEntry.action).filterMap (runtime.responseCandidateSlot leaks)

def CandidateRecall (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (execution : (runtime.reactiveApplication leaks).Execution) : Prop :=
  ∀ who serial, serial ∉ runtime.submittedCandidateSlots leaks (execution.recall who) →
    execution.application.candidates.lookup (who, .prepared serial) = .fresh

private theorem submission_candidate_other (state : State graph) (sender observer : Player)
    (serial : Nat) (material : Submission graph)
    (different : observer ≠ sender ∨ material.packet.preparedCommitment? ≠ some serial) :
    (submitStep (material.register state sender) sender material.packet).candidates.lookup
      (observer, .prepared serial) = state.candidates.lookup (observer, .prepared serial) := by
  rcases material with ⟨packet, opening⟩
  cases packet with
  | commitment event candidate =>
      rcases candidate with ⟨owner, slot⟩
      by_cases owned : owner = sender
      · subst owner
        have apart : (observer, Slot.prepared serial) ≠ (sender, slot) := by
          intro same
          cases slot with
          | initial input => cases congrArg Prod.snd same
          | prepared used =>
              have owners := congrArg Prod.fst same
              have slots := Slot.prepared.inj (congrArg Prod.snd same)
              rcases different with different | different
              · exact different owners
              · exact different (congrArg some slots.symm)
        cases slot with
        | initial input =>
            simp only [Submission.register, submitStep, ↓reduceIte]
            exact state.candidates.lookup_freeze_other _ _ apart
        | prepared used =>
            cases opening with
            | none =>
                simp only [Submission.register, submitStep, ↓reduceIte]
                exact state.candidates.lookup_freeze_other _ _ apart
            | some raw =>
                simp only [Submission.register, submitStep, ↓reduceIte]
                rw [CommitmentCandidates.lookup_freeze_other _ _ _ apart,
                  CommitmentCandidates.lookup_prepare_other _ _ _ _ _ apart]
      · cases slot <;> cases opening <;>
          simp [Submission.register, submitStep, owned]
  | opening | withhold | malformed => cases opening <;> rfl

theorem submittedCandidateSlots_respond (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (execution : (runtime.reactiveApplication leaks).Execution) (who : Player)
    (response : (runtime.reactiveApplication leaks).Action) :
    runtime.submittedCandidateSlots leaks
        ((execution.respond (runtime.reactiveApplication leaks) who response).recall who) =
      runtime.submittedCandidateSlots leaks (execution.recall who) ++
        (runtime.responseCandidateSlot leaks response).toList := by
  rw [submittedCandidateSlots, ReactiveApplication.respond_actions]
  simp only [List.filterMap_append, List.filterMap_cons, List.filterMap_nil]
  cases runtime.responseCandidateSlot leaks response <;> rfl

theorem candidateRecall_respond (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (execution : (runtime.reactiveApplication leaks).Execution) (who : Player)
    (response : (runtime.reactiveApplication leaks).Action)
    (valid : runtime.CandidateRecall leaks execution) :
    runtime.CandidateRecall leaks
      (execution.respond (runtime.reactiveApplication leaks) who response) := by
  intro observer serial absent
  have old : serial ∉ runtime.submittedCandidateSlots leaks (execution.recall observer) := by
    intro present
    apply absent
    unfold submittedCandidateSlots at present ⊢
    exact List.mem_filterMap.mpr (by
      obtain ⟨action, member, slot⟩ := List.mem_filterMap.mp present
      obtain ⟨entry, retained, rfl⟩ := List.mem_map.mp member
      exact ⟨entry.action, List.mem_map.mpr
        ⟨entry, (runtime.reactiveApplication leaks).respond_recall_mono
          execution who observer response retained, rfl⟩, slot⟩)
  have fresh := valid observer serial old
  rcases response with ⟨transmission⟩
  cases transmission with
  | none => exact fresh
  | some transmission =>
      cases transmission with
      | replay id => exact fresh
      | submit material =>
          apply Eq.trans (submission_candidate_other execution.application who observer serial
            material.call ?_) fresh
          by_cases same : observer = who
          · subst observer
            right
            rw [runtime.submittedCandidateSlots_respond] at absent
            intro selected
            apply absent
            apply List.mem_append_right
            change serial ∈ material.call.packet.preparedCommitment?.toList
            simp [selected]
          · exact Or.inl same

private theorem issued_candidate_slot (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (execution : (runtime.reactiveApplication leaks).Execution)
    (id : MessageId Player) (event : graph.EventId) (owner : Player) (serial : Nat)
    (evidence : Option (OpeningFact graph))
    (issued : execution.Issued (runtime.reactiveApplication leaks)
      ⟨id, ⟨.commitment event (owner, .prepared serial), evidence⟩⟩) :
    serial ∈ runtime.submittedCandidateSlots leaks (execution.recall id.1) := by
  obtain ⟨entry, member, material, sent, _, state, known, packet⟩ := issued
  apply List.mem_filterMap.mpr
  refine ⟨entry.action, List.mem_map.mpr ⟨entry, member, rfl⟩, ?_⟩
  have raw := congrArg WitnessedPacket.call packet
  change material.call.packet = Payload.commitment event (owner, .prepared serial) at raw
  simp only [responseCandidateSlot, sent, raw, Payload.preparedCommitment?]

private theorem candidateRecall_handle (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (execution : (runtime.reactiveApplication leaks).Execution) (next : State graph)
    (message : Message Player (WitnessedPacket graph))
    (valid : runtime.CandidateRecall leaks execution)
    (issued : execution.Issued (runtime.reactiveApplication leaks) message)
    (accepted : handle runtime execution.application ⟨message.id, message.payload.call⟩ = some next)
    (who : Player) (serial : Nat)
    (absent : serial ∉ runtime.submittedCandidateSlots leaks (execution.recall who)) :
    next.candidates.lookup (who, .prepared serial) = .fresh := by
  rcases message with ⟨id, packet, evidence⟩
  cases packet with
  | commitment event candidate =>
      obtain ⟨candidates, _, owner⟩ :=
        handle_commitment_tables runtime _ _ id event candidate accepted
      have different : (who, Slot.prepared serial) ≠ candidate := by
        intro same
        subst candidate
        change who = id.1 at owner
        subst who
        exact absent
          (issued_candidate_slot runtime leaks execution id event id.1 serial evidence issued)
      rw [candidates, CommitmentCandidates.lookup_freeze_other _ _ _ different]
      exact valid who serial absent
  | opening event candidate raw | withhold event =>
      rw [(handle_resolution_tables runtime _ _ _ (by intros; simp) accepted).2]
      exact valid who serial absent
  | malformed raw => simp [handle] at accepted

theorem candidateRecall_environment (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (execution next : (runtime.reactiveApplication leaks).Execution)
    (command : (runtime.reactiveApplication leaks).Command)
    (valid : runtime.CandidateRecall leaks execution)
    (provenance : execution.Provenance (runtime.reactiveApplication leaks))
    (reached : next ∈ (execution.environmentStep (runtime.reactiveApplication leaks)
      command).support) : runtime.CandidateRecall leaks next := by
  intro who serial absent
  rw [ReactiveApplication.environmentStep_recall _ execution next command reached] at absent
  cases command with
  | wait =>
      simp only [ReactiveApplication.Execution.environmentStep, FinDist.map_pure] at reached
      cases FinDist.mem_support_pure.mp reached
      exact valid who serial absent
  | activate actor =>
      obtain ⟨updated, supported, rfl⟩ := FinDist.support_map .. ▸ reached
      obtain ⟨selected, _, rfl⟩ := FinDist.support_map .. ▸ supported
      exact valid who serial absent
  | «include» id =>
      simp only [ReactiveApplication.Execution.environmentStep, FinDist.map_pure] at reached
      cases FinDist.mem_support_pure.mp reached
      unfold ReactiveApplication.Execution.includePending MessageNetwork.includePending
      cases found : execution.network.lookup id with
      | none => exact valid who serial absent
      | some message =>
          change (State.candidates ((handle runtime execution.application
            ⟨message.id, message.payload.call⟩).getD execution.application)).lookup
              (who, .prepared serial) = _
          cases accepted : handle runtime execution.application
              ⟨message.id, message.payload.call⟩ with
          | none => exact valid who serial absent
          | some state =>
              exact candidateRecall_handle runtime leaks execution state message valid
                (provenance.pending message (List.mem_of_find?_eq_some found)) accepted
                who serial absent
  | application command =>
      obtain ⟨updated, supported, rfl⟩ := FinDist.support_map .. ▸ reached
      obtain ⟨state, changed, rfl⟩ := FinDist.support_map .. ▸ supported
      rw [(environmentStep_tables runtime execution.application state command changed).2]
      exact valid who serial absent

theorem candidateRecall_history (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (inputs : FinDist graph.Inputs) (horizon : Nat)
    (scheduler : (runtime.reactiveApplication leaks).Scheduler) :
    ∀ {state} (_trace : ((runtime.reactiveApplication leaks).protocol
      (inputs.map State.initial) horizon scheduler).Trace state),
      ReactiveApplication.serviceInvariant (runtime.CandidateRecall leaks) state := by
  have invariant : (runtime.reactiveApplication leaks).ServiceInvariant scheduler
      (fun execution => runtime.CandidateRecall leaks execution ∧
        execution.Provenance (runtime.reactiveApplication leaks)) := {
    respond := fun execution who action valid =>
      ⟨runtime.candidateRecall_respond leaks execution who action valid.1,
        (runtime.reactiveApplication leaks).respond_provenance execution who action valid.2⟩
    environment := fun execution next command valid _ reached =>
      ⟨runtime.candidateRecall_environment leaks execution next command valid.1 valid.2 reached,
        (runtime.reactiveApplication leaks).environment_provenance execution next command
          valid.2 reached⟩ }
  intro state trace
  have valid := invariant.history (inputs.map State.initial) horizon (by
    intro state supported
    obtain ⟨input, _, rfl⟩ := FinDist.support_map .. ▸ supported
    exact ⟨fun who serial _ => State.initial_candidate input who (.prepared serial),
      MessageNetwork.Satisfies.empty⟩) trace
  cases state with
  | none => trivial
  | some control => exact valid.1

/-- The least fresh serial is bounded by the owner's response count, regardless
of the magnitude of the identifiers it previously chose. -/
theorem reactiveFreshSlot_le_recall (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (execution : (runtime.reactiveApplication leaks).Execution) (who : Player)
    (valid : runtime.CandidateRecall leaks execution) :
    ∃ serial, serial ≤ (execution.recall who).length ∧
      reactiveFreshSlot
        (execution.observe (runtime.reactiveApplication leaks) who).application = some serial := by
  classical
  let used := runtime.submittedCandidateSlots leaks (execution.recall who)
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
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (inputs : FinDist graph.Inputs) (horizon : Nat)
    (scheduler : (runtime.reactiveApplication leaks).Scheduler)
    (control : (runtime.reactiveApplication leaks).Control)
    (trace : ((runtime.reactiveApplication leaks).protocol (inputs.map State.initial)
      horizon scheduler).Trace (some control)) (who : Player) (active : control.actor = some who) :
    ∃ serial, serial < horizon ∧ reactiveFreshSlot
      (control.execution.observe (runtime.reactiveApplication leaks) who).application =
        some serial := by
  obtain ⟨serial, bounded, selected⟩ := runtime.reactiveFreshSlot_le_recall leaks
    control.execution who (runtime.candidateRecall_history leaks inputs horizon scheduler trace)
  exact ⟨serial, lt_of_le_of_lt bounded
    ((runtime.reactiveApplication leaks).active_recall_lt_horizon (inputs.map State.initial)
      horizon scheduler control trace who active), selected⟩

end Vegas.EventGraphRuntime
