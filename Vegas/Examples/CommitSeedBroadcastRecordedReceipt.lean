/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedBroadcastProtectedTail
import Interaction.ReactiveRecallInvariant

/-! # Retained receipts for all raw continuation submissions -/

noncomputable section

namespace Vegas.Examples.CommitSeedBroadcast

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

private def ReceiptAccounted (seeds : Seeds) : app.ProtocolState → Prop
  | none => True
  | some current => ∀ owner entry, entry ∈ current.execution.recall owner →
      ∀ message, entry.emitted = some message →
      entry.beforeView.application.2.attempt ≠ originalAttempt →
      (∃ accepted, (message.id, accepted) ∈ current.execution.receipts) ∨
        (current.actor = none ∧ ∃ (remaining : Nat) (before : app.Execution)
          (submission : app.Submission),
          Nonempty ((app.protocol initial horizon (family seeds)).Trace
            (some ⟨remaining, some owner, before⟩)) ∧
          before.application.attempt ≠ originalAttempt ∧
          current.execution = before.respond app owner ⟨some submission⟩ ∧
          message.id = (owner, before.network.nextSerial owner) ∧
          entry.beforeView.application.1.publicView.clock =
            current.execution.application.current.native.clock)

private theorem accounted_history (seeds : Seeds) :
    ∀ {state} (_trace : (app.protocol initial horizon (family seeds)).Trace state),
      ReceiptAccounted seeds state := by
  intro state trace
  induction trace with
  | start => trivial
  | @extend source target prior joint legal reached ih =>
      change target ∈ (app.transition initial horizon (family seeds) source joint).support
        at reached
      cases source with
      | none =>
          obtain ⟨state, _supported, rfl⟩ := PMF.support_map .. ▸ reached
          intro owner entry member
          exact (List.not_mem_nil member).elim
      | some current =>
          rcases current with ⟨remaining, active, execution⟩
          cases active with
          | some actor =>
              cases (PMF.mem_support_pure_iff _ _).mp reached
              generalize actionEq : (joint actor).getD (⟨none⟩ : app.Action) = action
              intro owner entry member message emitted tracked
              by_cases old : entry ∈ execution.recall owner
              · rcases ih owner entry old message emitted tracked with received | outstanding
                · obtain ⟨accepted, receipt⟩ := received
                  left
                  refine ⟨accepted, ?_⟩
                  rw [app.respond_receipts]
                  exact receipt
                · cases outstanding.1
              · have sameOwner : owner = actor := by
                  by_contra different
                  rw [app.respond_recall_other execution actor owner different action] at member
                  exact old member
                subst owner
                rcases action with ⟨transmission⟩
                cases transmission with
                | none =>
                    simp only [ReactiveApplication.Execution.respond, ↓reduceIte, List.mem_append,
                      List.mem_singleton] at member
                    rcases member with before | rfl
                    · exact (old before).elim
                    · cases emitted
                | some submission =>
                    simp only [ReactiveApplication.Execution.respond, MessageNetwork.submit,
                      ↓reduceIte, List.mem_append, List.mem_singleton] at member
                    rcases member with before | rfl
                    · exact (old before).elim
                    · cases Option.some.inj emitted
                      right
                      refine ⟨rfl, remaining, execution, submission, ⟨prior⟩, tracked, rfl,
                        rfl, ?_⟩
                      have clock := congrArg (fun view : PhasePublicView graph => view.native.clock)
                        (PhaseCount.submit_publicView execution.application actor submission)
                      exact clock.symm
          | none =>
              cases remaining with
              | zero => exact (legal.1 ⟨rfl, rfl⟩).elim
              | succ remaining =>
                  obtain ⟨command, selected, moved⟩ := Set.mem_iUnion₂.mp
                    (PMF.support_bind .. ▸ reached)
                  obtain ⟨next, supported, rfl⟩ := PMF.support_map .. ▸ moved
                  intro owner entry member message emitted tracked
                  rw [app.environmentStep_recall execution next command supported] at member
                  rcases ih owner entry member message emitted tracked with received | outstanding
                  · obtain ⟨accepted, receipt⟩ := received
                    have retained := app.environmentStep_receipts_prefix execution next command
                      supported
                    exact Or.inl ⟨accepted, retained.subset receipt⟩
                  · obtain ⟨_idle, beforeRemaining, before, submission, ⟨beforeTrace⟩,
                      retired, responded, identifier, _clock⟩ := outstanding
                    change execution = before.respond app owner ⟨some submission⟩ at responded
                    subst execution
                    have chosen : command = choose seeds
                        (before.respond app owner ⟨some submission⟩).environmentRecall
                        ((before.respond app owner ⟨some submission⟩).observeEnvironment app) :=
                      (PMF.mem_support_pure_iff _ _).mp selected
                    obtain ⟨accepted, receipt⟩ := tail_submission_receipt seeds beforeRemaining
                      before owner submission beforeTrace retired next (chosen ▸ supported)
                    exact Or.inl ⟨accepted, identifier.symm ▸ receipt⟩

/-- Every raw continuation envelope has a physical receipt as soon as time
passes its emission clock. This remains true after namespace retirement. -/
theorem tail_recorded_submission_receipt (seeds : Seeds) (current : app.Control)
    (trace : (app.protocol initial horizon (family seeds)).Trace (some current))
    (owner : Player) (entry : app.PlayerEntry) (member : entry ∈ current.execution.recall owner)
    (message : Message Player (CommitAttemptPacket graph)) (emitted : entry.emitted = some message)
    (tail : entry.beforeView.application.2.attempt ≠ originalAttempt)
    (later : entry.beforeView.application.1.publicView.clock <
      current.execution.application.current.native.clock) :
    ∃ accepted, (message.id, accepted) ∈ current.execution.receipts := by
  rcases accounted_history seeds trace owner entry member message emitted tail with
    received | outstanding
  · exact received
  · obtain ⟨_idle, _remaining, _before, _submission, _trace, _retired, _responded,
      _identifier, sameClock⟩ := outstanding
    omega

/-- In particular the strict protected bound is satisfied for every raw
continuation packet; the native accept/reject bit is unrestricted. -/
theorem tail_protected_submission_receipt (seeds : Seeds) (current : app.Control)
    (trace : (app.protocol initial horizon (family seeds)).Trace (some current))
    (owner : Player) (entry : app.PlayerEntry) (member : entry ∈ current.execution.recall owner)
    (message : Message Player (CommitAttemptPacket graph)) (emitted : entry.emitted = some message)
    (tail : entry.beforeView.application.2.attempt ≠ originalAttempt)
    (later : entry.beforeView.application.1.publicView.clock + 5 <
      current.execution.application.current.native.clock) :
    ∃ accepted, (message.id, accepted) ∈ current.execution.receipts := by
  exact tail_recorded_submission_receipt seeds current trace owner entry member message emitted
    tail (by omega)

/-- While the original full attempt remains live, its physical clock never
passes six; the raw expiry proof, rather than a player policy, supplies this bound. -/
theorem original_clock_bound (seeds : Seeds) (current : app.Control)
    (trace : (app.protocol initial horizon (family seeds)).Trace (some current))
    (original : current.execution.application.attempt = originalAttempt) :
    current.execution.application.current.native.clock ≤ 6 := by
  have beforeEnd : current.execution.environmentRecall.length < 30 := by
    by_contra late
    exact original_attempt_retired seeds current trace (by omega) original
  rw [original_clock_index seeds current trace original]
  generalize position : current.execution.environmentRecall.length = index at beforeEnd ⊢
  interval_cases index <;> decide

/-- Only clock-zero original packets can meet the strict protected inclusion
antecedent. Late packets are not silently granted a stronger service promise. -/
theorem original_protected_send_clock_zero (seeds : Seeds) (current : app.Control)
    (trace : (app.protocol initial horizon (family seeds)).Trace (some current))
    (original : current.execution.application.attempt = originalAttempt)
    (entry : app.PlayerEntry)
    (late : entry.beforeView.application.1.publicView.clock + 5 <
      current.execution.application.current.native.clock) :
    entry.beforeView.application.1.publicView.clock = 0 := by
  have bounded := original_clock_bound seeds current trace original
  omega

end Vegas.Examples.CommitSeedBroadcast
