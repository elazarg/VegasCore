/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveCommitmentProtection
import Vegas.Pending.ReactiveBindingRepair
import Vegas.Pending.ReactiveBindingShadowStep
import Interaction.ReactivePolicyInvariant

/-! # Actual candidate agreement outside one changed registration

Two responses to the same owned slot may install different private meanings.
All other owned slots agree, and shared subsequent responses preserve that
agreement. Actual scheduler steps never alter the catalogue after every pending
owned commitment has already fixed its handle. These facts do not follow from
an arbitrary repair frame and do not establish a whole-policy payoff comparison.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

/-- A response's registration depends only on the candidate queried, rather
than on another hidden catalogue entry. -/
theorem Submission.candidateAfter_eq_of_query_eq
    (submission : Submission graph) (who : Player)
    (left right : CandidateSlot graph → CommitmentCandidate (Raw L))
    (query : CandidateSlot graph) (same : left query = right query) :
    submission.candidateAfter who left query = submission.candidateAfter who right query := by
  classical
  unfold Submission.candidateAfter
  cases submission.packet with
  | commitment event candidate =>
      split
      · rw [same]
      · exact same
  | opening | withhold | malformed => exact same

/-- Packet inclusion and scheduler application commands preserve every
candidate when actual retained commitments already have fixed owned handles. -/
theorem reactive_environment_candidates_fixed (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (execution next : (runtime.reactiveApplication leaks).Execution)
    (command : (runtime.reactiveApplication leaks).Command)
    (fixed : runtime.ReactiveCommitmentsFixed leaks execution)
    (reached : next ∈ (execution.environmentStep (runtime.reactiveApplication leaks)
      command).support) : next.application.candidates = execution.application.candidates := by
  cases command with
  | wait =>
      simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map] at reached
      cases (PMF.mem_support_pure_iff _ _).mp reached
      rfl
  | activate who =>
      obtain ⟨updated, supported, rfl⟩ := PMF.support_map .. ▸ reached
      obtain ⟨selected, _, rfl⟩ := PMF.support_map .. ▸ supported
      rfl
  | application command =>
      obtain ⟨updated, supported, rfl⟩ := PMF.support_map .. ▸ reached
      obtain ⟨state, changed, rfl⟩ := PMF.support_map .. ▸ supported
      exact (environmentStep_tables runtime execution.application state command changed).2
  | «include» id =>
      simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map] at reached
      cases (PMF.mem_support_pure_iff _ _).mp reached
      unfold ReactiveApplication.Execution.includePending MessageNetwork.includePending
      cases found : execution.network.lookup id with
      | none => rfl
      | some message =>
          simp only
          cases accepted : (runtime.reactiveApplication leaks).handle execution.application
              message with
          | none => rfl
          | some state =>
              change state.candidates = execution.application.candidates
              have called := reactiveHandle_call accepted
              cases packet : message.payload.call with
              | commitment event candidate =>
                  rw [packet] at called
                  obtain ⟨candidates, _, owned⟩ := handle_commitment_tables runtime
                    execution.application state message.id event candidate called
                  rw [candidates]
                  exact execution.application.candidates.freeze_eq_self_of_not_fresh candidate
                    (fixed.lookup id message found event candidate packet owned)
              | opening | withhold | malformed =>
                  exact (handle_resolution_tables runtime execution.application state
                    ⟨message.id, message.payload.call⟩
                    (by intro event candidate same; rw [packet] at same; cases same) called).2

/-- Actual owned catalogue meanings agree everywhere except the explicitly
changed slot. This is a proof relation on two executions, not additional state. -/
def OwnerCandidatesAgreeExcept (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (owner : Player) (changed : CandidateSlot graph)
    (original repaired : (runtime.reactiveApplication leaks).Execution) : Prop :=
  ∀ slot, slot ≠ changed → original.application.candidates.lookup (owner, slot) =
    repaired.application.candidates.lookup (owner, slot)

namespace OwnerCandidatesAgreeExcept

variable {runtime : EventGraphRuntime graph}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph)}
  {owner : Player} {changed : CandidateSlot graph}
  {original repaired : (runtime.reactiveApplication leaks).Execution}

/-- The genuine same-before registration pair supplies agreement outside the
selected slot, even when its two raw materials have different types or are absent. -/
theorem binding_seed (execution : (runtime.reactiveApplication leaks).Execution)
    (owner : Player) (event : graph.EventId) (slot : CandidateSlot graph)
    (left right : Option (Raw L)) :
    let app := runtime.reactiveApplication leaks
    OwnerCandidatesAgreeExcept runtime leaks owner slot
      (execution.respond app owner ⟨some ⟨⟨.commitment event (owner, slot), left⟩, .none⟩⟩)
      (execution.respond app owner ⟨some ⟨⟨.commitment event (owner, slot), right⟩, .none⟩⟩) := by
  intro app query different
  change (submitStep ((⟨.commitment event (owner, slot), left⟩ : Submission graph).register
    execution.application owner) owner (.commitment event (owner, slot))).candidates.lookup
      (owner, query) =
    (submitStep ((⟨.commitment event (owner, slot), right⟩ : Submission graph).register
      execution.application owner) owner (.commitment event (owner, slot))).candidates.lookup
        (owner, query)
  rw [Submission.candidateAfter_eq, Submission.candidateAfter_eq]
  simp only [Submission.candidateAfter, different, and_false, ↓reduceIte]

end OwnerCandidatesAgreeExcept

/-- The same real response preserves each already equal owned candidate.
The response may name another slot, carry arbitrary raw material, or be foreign. -/
theorem reactive_respond_owner_candidate_eq (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (owner : Player) (original repaired : (runtime.reactiveApplication leaks).Execution)
    (slot : CandidateSlot graph)
    (same : original.application.candidates.lookup (owner, slot) =
      repaired.application.candidates.lookup (owner, slot))
    (actor : Player) (response : (runtime.reactiveApplication leaks).Action) :
    (original.respond (runtime.reactiveApplication leaks)
      actor response).application.candidates.lookup (owner, slot) =
    (repaired.respond (runtime.reactiveApplication leaks)
      actor response).application.candidates.lookup (owner, slot) := by
  by_cases own : actor = owner
  · subst actor
    rcases response with ⟨transmission⟩
    cases transmission with
    | none => exact same
    | some material =>
        change (submitStep (material.call.register original.application owner) owner
          material.call.packet).candidates.lookup (owner, slot) =
          (submitStep (material.call.register repaired.application owner) owner
            material.call.packet).candidates.lookup (owner, slot)
        rw [material.call.candidateAfter_eq, material.call.candidateAfter_eq]
        exact material.call.candidateAfter_eq_of_query_eq owner _ _ slot same
  · have catalog (execution : (runtime.reactiveApplication leaks).Execution) :
        (execution.respond (runtime.reactiveApplication leaks)
          actor response).application.candidates.lookup (owner, slot) =
            execution.application.candidates.lookup (owner, slot) := by
        rcases response with ⟨transmission⟩
        cases transmission with
        | none => rfl
        | some material =>
            have view := (submitStep_playerView_other
              (material.call.register execution.application actor) actor owner (Ne.symm own)
                material.call.packet).trans
                  (material.call.register_other execution.application actor owner (Ne.symm own))
            exact congrFun (congrArg PlayerView.candidates view) slot
    rw [catalog original, catalog repaired]
    exact same

namespace OwnerCandidatesAgreeExcept

variable {runtime : EventGraphRuntime graph}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph)}
  {owner : Player} {changed : CandidateSlot graph}
  {original repaired : (runtime.reactiveApplication leaks).Execution}

/-- A shared actual response preserves every other owned meaning. Foreign
responses need no normalization or restriction. -/
theorem respond (same : OwnerCandidatesAgreeExcept runtime leaks owner changed original repaired)
    (actor : Player) (response : (runtime.reactiveApplication leaks).Action) :
    OwnerCandidatesAgreeExcept runtime leaks owner changed
      (original.respond (runtime.reactiveApplication leaks) actor response)
      (repaired.respond (runtime.reactiveApplication leaks) actor response) := by
  intro slot different
  exact runtime.reactive_respond_owner_candidate_eq leaks owner original repaired slot
    (same slot different) actor response

/-- Any two actual environment outcomes preserve agreement; their candidate
catalogues stay fixed independently of the correlated chance draw. -/
theorem environment
    (same : OwnerCandidatesAgreeExcept runtime leaks owner changed original repaired)
    (leftFixed : runtime.ReactiveCommitmentsFixed leaks original)
    (rightFixed : runtime.ReactiveCommitmentsFixed leaks repaired)
    (left right : (runtime.reactiveApplication leaks).Execution)
    (command : (runtime.reactiveApplication leaks).Command)
    (leftMoved : left ∈ (original.environmentStep (runtime.reactiveApplication leaks)
      command).support)
    (rightMoved : right ∈ (repaired.environmentStep (runtime.reactiveApplication leaks)
      command).support) : OwnerCandidatesAgreeExcept runtime leaks owner changed left right := by
  intro slot different
  rw [runtime.reactive_environment_candidates_fixed leaks original left command leftFixed leftMoved,
    runtime.reactive_environment_candidates_fixed leaks repaired right command rightFixed
      rightMoved]
  exact same slot different

end OwnerCandidatesAgreeExcept

/-- With no further owner commitment, actual foreign and scheduler policies
preserve the entire owned catalogue. The fixedness resource holds on every
initialized raw trace and is maintained by the same policy invariant. -/
theorem reactive_runRounds_candidates_noncommitment (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (owner : Player) (scheduler : (runtime.reactiveApplication leaks).Scheduler)
    (players : Player → (runtime.reactiveApplication leaks).Policy)
    (count : Nat) (execution next : (runtime.reactiveApplication leaks).Execution)
    (fixed : runtime.ReactiveCommitmentsFixed leaks execution)
    (noncommitment : ∀ past view response, response ∈ (players owner past view).support →
      ∀ material, response.transmission = some material →
        ∀ event candidate, material.call.packet ≠ .commitment event candidate)
    (reached : next ∈ ((runtime.reactiveApplication leaks).runRounds scheduler players count
      execution).support) :
    ∀ slot, next.application.candidates.lookup (owner, slot) =
      execution.application.candidates.lookup (owner, slot) := by
  let app := runtime.reactiveApplication leaks
  let predicate (current : app.Execution) :=
    runtime.ReactiveCommitmentsFixed leaks current ∧
      ∀ slot, current.application.candidates.lookup (owner, slot) =
        execution.application.candidates.lookup (owner, slot)
  have invariant : app.PolicyInvariant players predicate := {
    respond := by
      intro current actor response held chosen
      refine ⟨runtime.reactiveCommitmentsFixed_respond leaks current actor response held.1, ?_⟩
      intro slot
      by_cases own : actor = owner
      · subst actor
        rcases response with ⟨transmission⟩
        cases transmission with
        | none => exact held.2 slot
        | some material =>
            have same := reactiveApplication_submit_noncommitment runtime leaks current.application
              owner material (noncommitment _ _ _ chosen material rfl)
            exact (congrArg (fun state : State graph => state.candidates.lookup (owner, slot))
              same).trans (held.2 slot)
      · rcases response with ⟨transmission⟩
        cases transmission with
        | none => exact held.2 slot
        | some material =>
            have view := (submitStep_playerView_other
              (material.call.register current.application actor) actor owner (Ne.symm own)
                material.call.packet).trans
                  (material.call.register_other current.application actor owner (Ne.symm own))
            exact (congrFun (congrArg PlayerView.candidates view) slot).trans (held.2 slot)
    environment := by
      intro current after command held moved
      refine ⟨runtime.reactiveCommitmentsFixed_environment leaks current after command held.1
        moved, ?_⟩
      intro slot
      rw [runtime.reactive_environment_candidates_fixed leaks current after command held.1 moved]
      exact held.2 slot }
  exact (invariant.runRounds scheduler count execution next ⟨fixed, fun _ => rfl⟩ reached).2

namespace OwnerCandidatesAgreeExcept

variable {runtime : EventGraphRuntime graph}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph)}

/-- The actual two preparation origins establish the boundary relation.
Arbitrary foreign raw responses and correlated scheduler observations remain
allowed; neither catalogue equality nor a repaired origin is inferred from a frame. -/
theorem binding_preparation
    (execution : (runtime.reactiveApplication leaks).Execution)
    (owner : Player) (event : graph.EventId) (slot : CandidateSlot graph)
    (leftRaw rightRaw : Option (Raw L))
    (scheduler : (runtime.reactiveApplication leaks).Scheduler)
    (leftPlayers rightPlayers : Player → (runtime.reactiveApplication leaks).Policy)
    (count : Nat) (left right : (runtime.reactiveApplication leaks).Execution)
    (fixed : runtime.ReactiveCommitmentsFixed leaks execution)
    (leftNoncommitment : ∀ past view response,
      response ∈ (leftPlayers owner past view).support →
        ∀ material, response.transmission = some material →
          ∀ named candidate, material.call.packet ≠ .commitment named candidate)
    (rightNoncommitment : ∀ past view response,
      response ∈ (rightPlayers owner past view).support →
        ∀ material, response.transmission = some material →
          ∀ named candidate, material.call.packet ≠ .commitment named candidate)
    (leftReached : left ∈ ((runtime.reactiveApplication leaks).runRounds scheduler leftPlayers count
      (execution.respond (runtime.reactiveApplication leaks) owner
        ⟨some ⟨⟨.commitment event (owner, slot), leftRaw⟩, .none⟩⟩)).support)
    (rightReached : right ∈ ((runtime.reactiveApplication leaks).runRounds scheduler rightPlayers
      count (execution.respond (runtime.reactiveApplication leaks) owner
        ⟨some ⟨⟨.commitment event (owner, slot), rightRaw⟩, .none⟩⟩)).support) :
    OwnerCandidatesAgreeExcept runtime leaks owner slot left right := by
  intro query different
  rw [runtime.reactive_runRounds_candidates_noncommitment leaks owner scheduler leftPlayers count _
    left (runtime.reactiveCommitmentsFixed_respond leaks execution owner _ fixed)
      leftNoncommitment leftReached query,
    runtime.reactive_runRounds_candidates_noncommitment leaks owner scheduler rightPlayers count _
      right (runtime.reactiveCommitmentsFixed_respond leaks execution owner _ fixed)
        rightNoncommitment rightReached query]
  exact binding_seed execution owner event slot leftRaw rightRaw query different

end OwnerCandidatesAgreeExcept

namespace OwnerCandidatesAgreeExcept

variable {runtime : EventGraphRuntime graph}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph)}

/-- Replacing missing material by any actual opening adds no loss of an old
owned certificate. The comparison is derived from the two real registrations. -/
theorem binding_seed_openable_mono
    (execution : (runtime.reactiveApplication leaks).Execution)
    (owner : Player) (event : graph.EventId) (slot : CandidateSlot graph)
    (opening : Option (Raw L)) :
    let app := runtime.reactiveApplication leaks
    let left := execution.respond app owner
      ⟨some ⟨⟨.commitment event (owner, slot), none⟩, .none⟩⟩
    let right := execution.respond app owner
      ⟨some ⟨⟨.commitment event (owner, slot), opening⟩, .none⟩⟩
    ∀ query raw, left.application.candidates.lookup (owner, query) = .openable raw →
      right.application.candidates.lookup (owner, query) = .openable raw := by
  intro app left right query raw available
  change (submitStep ((⟨.commitment event (owner, slot), none⟩ : Submission graph).register
    execution.application owner) owner (.commitment event (owner, slot))).candidates.lookup
      (owner, query) = .openable raw at available
  change (submitStep ((⟨.commitment event (owner, slot), opening⟩ : Submission graph).register
    execution.application owner) owner (.commitment event (owner, slot))).candidates.lookup
      (owner, query) = .openable raw
  rw [Submission.candidateAfter_eq] at available ⊢
  by_cases selected : query = slot
  · subst query
    simp only [Submission.candidateAfter, and_self, ↓reduceIte] at available ⊢
    cases meaning : execution.application.candidates.lookup (owner, slot) with
    | fresh =>
        cases slot <;> simp only [meaning, reduceCtorEq] at available
    | unopenable => simp only [meaning, reduceCtorEq] at available
    | openable value => simpa only [meaning] using available
  · simpa only [Submission.candidateAfter, selected, and_false, ↓reduceIte] using available

/-- Arbitrary actual no-owner-commitment preparation preserves the certificate
comparison supplied by the original missing registration. -/
theorem binding_preparation_openable_mono
    (execution : (runtime.reactiveApplication leaks).Execution)
    (owner : Player) (event : graph.EventId) (slot : CandidateSlot graph)
    (opening : Option (Raw L))
    (scheduler : (runtime.reactiveApplication leaks).Scheduler)
    (leftPlayers rightPlayers : Player → (runtime.reactiveApplication leaks).Policy)
    (count : Nat) (left right : (runtime.reactiveApplication leaks).Execution)
    (fixed : runtime.ReactiveCommitmentsFixed leaks execution)
    (leftNoncommitment : ∀ past view response,
      response ∈ (leftPlayers owner past view).support →
        ∀ material, response.transmission = some material →
          ∀ named handle, material.call.packet ≠ .commitment named handle)
    (rightNoncommitment : ∀ past view response,
      response ∈ (rightPlayers owner past view).support →
        ∀ material, response.transmission = some material →
          ∀ named handle, material.call.packet ≠ .commitment named handle)
    (leftReached : left ∈ ((runtime.reactiveApplication leaks).runRounds scheduler leftPlayers count
      (execution.respond (runtime.reactiveApplication leaks) owner
        ⟨some ⟨⟨.commitment event (owner, slot), none⟩, .none⟩⟩)).support)
    (rightReached : right ∈ ((runtime.reactiveApplication leaks).runRounds scheduler rightPlayers
      count (execution.respond (runtime.reactiveApplication leaks) owner
        ⟨some ⟨⟨.commitment event (owner, slot), opening⟩, .none⟩⟩)).support) :
    ∀ query raw, left.application.candidates.lookup (owner, query) = .openable raw →
      right.application.candidates.lookup (owner, query) = .openable raw := by
  intro query raw available
  rw [runtime.reactive_runRounds_candidates_noncommitment leaks owner scheduler leftPlayers count _
    left (runtime.reactiveCommitmentsFixed_respond leaks execution owner _ fixed)
      leftNoncommitment leftReached query] at available
  rw [runtime.reactive_runRounds_candidates_noncommitment leaks owner scheduler rightPlayers count _
    right (runtime.reactiveCommitmentsFixed_respond leaks execution owner _ fixed)
      rightNoncommitment rightReached query]
  exact binding_seed_openable_mono execution owner event slot opening query raw available

end OwnerCandidatesAgreeExcept

end Vegas.EventGraphRuntime
