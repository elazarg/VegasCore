/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Pending.PhaseNamespace

/-! # Accepted live bindings retain their physical attempt stamp

Saved prefix associations lie strictly before the current phase. Every other
accepted binding has an actual author output in the current namespace. Local
automatic failure writes no association, and rollback erases all live stamps.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}

/-- An accepted association is either in the saved rank prefix or has an
explicit signed output in the indicated attempt namespace. -/
def BindingStamp (outputs : Player → List (Message Player (CommitAttemptPacket graph)))
    (attempt : CommitAttemptId) (state : State graph) : Prop :=
  ∀ event candidate, state.accepted (.inr event) = some candidate →
    event.val < attempt.phase ∨ ∃ message ∈ outputs candidate.1,
      message.sender = candidate.1 ∧
      message.payload.packet.call = .commitment event candidate ∧ message.payload.attempt = attempt

namespace BindingStamp

variable {outputs : Player → List (Message Player (CommitAttemptPacket graph))}

omit [DecidableEq Player] in
theorem copy {before after : State graph} {attempt : CommitAttemptId}
    (valid : BindingStamp outputs attempt before) (accepted : after.accepted = before.accepted) :
    BindingStamp outputs attempt after := by
  simpa only [BindingStamp, accepted] using valid

omit [DecidableEq Player] in
theorem mono {more : Player → List (Message Player (CommitAttemptPacket graph))}
    {state : State graph} {attempt : CommitAttemptId} (valid : BindingStamp outputs attempt state)
    (contains : ∀ who, outputs who ⊆ more who) : BindingStamp more attempt state := by
  intro event candidate accepted
  rcases valid event candidate accepted with previous | ⟨message, member, sender, sent, current⟩
  · exact Or.inl previous
  · exact Or.inr ⟨message, contains candidate.1 member, sender, sent, current⟩

omit [DecidableEq Player] in
theorem of_before {state : State graph} (attempt : CommitAttemptId)
    (before : ∀ event candidate, state.accepted (.inr event) = some candidate →
      event.val < attempt.phase) : BindingStamp outputs attempt state :=
  fun event candidate accepted => Or.inl (before event candidate accepted)

end BindingStamp

namespace PhaseRuntimeState

/-- Automatic phase closure keeps live stamps only when the current namespace
survives. A retry restores exclusively earlier saved associations. -/
theorem settle_bindingStamp
    (outputs : Player → List (Message Player (CommitAttemptPacket graph)))
    (phases : List (RuntimePhase graph)) (generation : Nat) (entry current : RecoveryState graph)
    (retired : List (RetiredCommitAttempt graph))
    (ordered : phases.IsChain (fun before after => before.high = after.low))
    (saved : ∀ phase ∈ phases.head?, ∀ event candidate,
      entry.native.accepted (.inr event) = some candidate → event.val < phase.low)
    (bounded : ∀ phase ∈ phases.head?, ∀ event candidate,
      current.native.accepted (.inr event) = some candidate → event.val < phase.high)
    (active : BindingStamp outputs ⟨phaseLow phases, generation⟩ current.native) :
    BindingStamp outputs (settle phases generation entry current retired).attempt
      (settle phases generation entry current retired).current.native := by
  induction phases generalizing generation entry current retired with
  | nil =>
      exact BindingStamp.of_before _ (fun event _ _ => event.isLt)
  | cons phase remaining ih =>
      have head : phase ∈ (phase :: remaining).head? := by simp
      have savedBefore := saved phase head
      have activeBefore := bounded phase head
      have drained := active.copy (phase.drain_tables current).1
      have rebuiltBefore : ∀ event candidate,
          (phase.drain (restore entry (phase.drain current))).native.accepted (.inr event) =
            some candidate → event.val < phase.low := by
        intro event candidate accepted
        rw [(phase.drain_tables _).1] at accepted
        exact savedBefore event candidate accepted
      have advance : ∀ (state : RecoveryState graph)
          (archive : List (RetiredCommitAttempt graph)),
          (∀ event candidate, state.native.accepted (.inr event) = some candidate →
            event.val < phase.high) →
          BindingStamp outputs (settle remaining generation state state archive).attempt
            (settle remaining generation state state archive).current.native := by
        intro state archive before
        have nextBefore : ∀ next ∈ remaining.head?, ∀ event candidate,
            state.native.accepted (.inr event) = some candidate → event.val < next.low := by
          intro next member event candidate accepted
          have boundary := ordered.rel_head? member
          exact (before event candidate accepted).trans_eq boundary
        apply ih _ _ _ _ ordered.tail nextBefore
        · intro next member event candidate accepted
          exact (nextBefore next member event candidate accepted).trans next.nonempty
        · apply BindingStamp.of_before
          intro event candidate accepted
          cases rest : remaining with
          | nil => exact event.isLt
          | cons next tail =>
              exact nextBefore next (by simp only [rest, List.head?_cons, Option.mem_some_iff])
                event candidate accepted
      simp only [settle]
      split
      · split
        · split
          · exact BindingStamp.of_before _ rebuiltBefore
          · have rebuiltHigh : ∀ event candidate,
                (phase.drain (restore entry (phase.drain current))).native.accepted (.inr event) =
                  some candidate → event.val < phase.high := by
              intro event candidate accepted
              exact (rebuiltBefore event candidate accepted).trans phase.nonempty
            exact advance (phase.drain (restore entry (phase.drain current))) _ rebuiltHigh
        · apply advance
          intro event candidate accepted
          rw [(phase.drain_tables current).1] at accepted
          exact activeBefore event candidate accepted
      · exact drained

/-- Every retired native table retains the authored namespace of its own
acceptance, including records produced when no owner survives the phase. -/
theorem settle_archivedBindingStamp
    (outputs : Player → List (Message Player (CommitAttemptPacket graph)))
    (phases : List (RuntimePhase graph)) (generation : Nat) (entry current : RecoveryState graph)
    (retired : List (RetiredCommitAttempt graph))
    (ordered : phases.IsChain (fun before after => before.high = after.low))
    (saved : ∀ phase ∈ phases.head?, ∀ event candidate,
      entry.native.accepted (.inr event) = some candidate → event.val < phase.low)
    (bounded : ∀ phase ∈ phases.head?, ∀ event candidate,
      current.native.accepted (.inr event) = some candidate → event.val < phase.high)
    (active : BindingStamp outputs ⟨phaseLow phases, generation⟩ current.native)
    (archives : ∀ record ∈ retired, BindingStamp outputs record.attempt record.state) :
    ∀ record ∈ (settle phases generation entry current retired).retired,
      BindingStamp outputs record.attempt record.state := by
  induction phases generalizing generation entry current retired with
  | nil => exact archives
  | cons phase remaining ih =>
      have head : phase ∈ (phase :: remaining).head? := by simp
      have savedBefore := saved phase head
      have activeBefore := bounded phase head
      have drained := active.copy (phase.drain_tables current).1
      have rebuiltBefore : ∀ event candidate,
          (phase.drain (restore entry (phase.drain current))).native.accepted (.inr event) =
            some candidate → event.val < phase.low := by
        intro event candidate accepted
        rw [(phase.drain_tables _).1] at accepted
        exact savedBefore event candidate accepted
      have advance : ∀ (state : RecoveryState graph)
          (archive : List (RetiredCommitAttempt graph)),
          (∀ event candidate, state.native.accepted (.inr event) = some candidate →
            event.val < phase.high) →
          (∀ record ∈ archive, BindingStamp outputs record.attempt record.state) →
          ∀ record ∈ (settle remaining generation state state archive).retired,
            BindingStamp outputs record.attempt record.state := by
        intro state archive before archived
        have nextBefore : ∀ next ∈ remaining.head?, ∀ event candidate,
            state.native.accepted (.inr event) = some candidate → event.val < next.low := by
          intro next member event candidate accepted
          exact (before event candidate accepted).trans_eq (ordered.rel_head? member)
        apply ih _ _ _ _ ordered.tail nextBefore
        · intro next member event candidate accepted
          exact (nextBefore next member event candidate accepted).trans next.nonempty
        · apply BindingStamp.of_before
          intro event candidate accepted
          cases rest : remaining with
          | nil => exact event.isLt
          | cons next tail =>
              exact nextBefore next (by simp only [rest, List.head?_cons, Option.mem_some_iff])
                event candidate accepted
        · exact archived
      have appended : ∀ record ∈ retired ++
          [⟨⟨phase.low, generation⟩, (phase.drain current).native⟩],
          BindingStamp outputs record.attempt record.state := by
        intro record member
        rcases List.mem_append.mp member with old | new
        · exact archives record old
        · cases List.mem_singleton.mp new
          simpa only [phaseLow, List.head?_cons, Option.map_some, Option.getD_some] using drained
      simp only [settle]
      split
      · split
        · split
          · exact appended
          · apply advance _ _ _ appended
            intro event candidate accepted
            exact (rebuiltBefore event candidate accepted).trans phase.nonempty
        · apply advance _ _ _ archives
          intro event candidate accepted
          rw [(phase.drain_tables current).1] at accepted
          exact activeBefore event candidate accepted
      · exact archives

end PhaseRuntimeState

end Vegas.EventGraphRuntime
