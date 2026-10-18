/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedBroadcastInitialResponses
import Interaction.ReactiveRawRoundTrace

/-! # Every original clock-zero packet is retained in the shared early snapshot -/

noncomputable section

namespace Vegas.Examples.CommitSeedBroadcast

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

private theorem originalClock_positive (extra : Nat) : 1 ≤ originalClock (extra + 4) := by
  change 1 ≤ originalTick 0 + (originalTick 1 + (originalTick 2 +
    (originalTick 3 + originalClockFrom 4 extra)))
  norm_num [originalTick]

theorem original_zero_clock_index (seed : Seeds) (current : app.Control)
    (trace : (app.protocol initial horizon (family seed)).Trace (some current))
    (original : current.execution.application.attempt = originalAttempt)
    (zero : current.execution.application.current.native.clock = 0) :
    current.execution.environmentRecall.length ≤ 3 := by
  have clock := original_clock_index seed current trace original
  by_contra later
  have enough : current.execution.environmentRecall.length =
      (current.execution.environmentRecall.length - 4) + 4 := by omega
  rw [enough] at clock
  have positive := originalClock_positive (current.execution.environmentRecall.length - 4)
  omega

private def SnapshotRecorded (execution : app.Execution) : Prop :=
  ∀ owner entry, entry ∈ execution.recall owner → ∀ message, entry.emitted = some message →
    entry.beforeView.application.2.attempt = originalAttempt →
    entry.beforeView.application.1.publicView.clock = 0 →
    execution.environmentRecall.length ≤ 3 ∨
      ∃ snapshot, execution.environmentRecall[3]? = some snapshot ∧
        message ∈ snapshot.beforeView.network.inputs

private theorem snapshot_recorded_history (seeds : Seeds) :
    ∀ {state} (_trace : (app.protocol initial horizon (family seeds)).Trace state),
      state.elim True (fun current => SnapshotRecorded current.execution) := by
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
              intro owner entry member message emitted original zero
              by_cases old : entry ∈ execution.recall owner
              · rw [app.respond_environmentRecall]
                exact ih owner entry old message emitted original zero
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
                    · left
                      rw [app.respond_environmentRecall]
                      exact original_zero_clock_index seeds ⟨remaining, some actor, execution⟩
                        prior original zero
          | none =>
              cases remaining with
              | zero => exact (legal.1 ⟨rfl, rfl⟩).elim
              | succ remaining =>
                  obtain ⟨command, _selected, moved⟩ := Set.mem_iUnion₂.mp
                    (PMF.support_bind .. ▸ reached)
                  obtain ⟨next, supported, rfl⟩ := PMF.support_map .. ▸ moved
                  intro owner entry member message emitted original zero
                  rw [app.environmentStep_recall execution next command supported] at member
                  have entries := app.environmentStep_environmentRecall execution next command
                    supported
                  rcases ih owner entry member message emitted original zero with early | recorded
                  · change execution.environmentRecall.length ≤ 3 at early
                    by_cases stillEarly : next.environmentRecall.length ≤ 3
                    · exact Or.inl stillEarly
                    · right
                      have length : execution.environmentRecall.length = 3 := by
                        rw [entries, List.length_append, List.length_singleton] at stillEarly
                        omega
                      refine ⟨⟨execution.observeEnvironment app, command⟩, ?_, ?_⟩
                      · rw [entries, List.getElem?_append_right (by omega :
                          execution.environmentRecall.length ≤ 3), length, Nat.sub_self]
                        rfl
                      · have inputs := app.history_inputRecall initial horizon (family seeds) prior
                        have own : message ∈ app.outputs (execution.recall owner) :=
                          List.mem_filterMap.mpr ⟨entry, member, emitted⟩
                        rw [← inputs owner] at own
                        exact (List.mem_filter.mp own).1
                  · right
                    obtain ⟨snapshot, selected, input⟩ := recorded
                    have inside : 3 < execution.environmentRecall.length := by
                      by_contra outside
                      have absent : execution.environmentRecall[3]? = none :=
                        List.getElem?_eq_none (by omega)
                      rw [absent] at selected
                      cases selected
                    exact ⟨snapshot, by
                      rw [entries, List.getElem?_append_left inside]
                      exact selected, input⟩

/-- Every actual original clock-zero output belongs to the fourth command's
immutable input snapshot, once that command has been reached. -/
theorem raw_clock_zero_packet_in_snapshot (seeds : Seeds) (current : app.Control)
    (trace : (app.protocol initial horizon (family seeds)).Trace (some current))
    (owner : Player) (entry : app.PlayerEntry) (member : entry ∈ current.execution.recall owner)
    (message : Message Player (CommitAttemptPacket graph)) (emitted : entry.emitted = some message)
    (original : entry.beforeView.application.2.attempt = originalAttempt)
    (zero : entry.beforeView.application.1.publicView.clock = 0)
    (past : 4 ≤ current.execution.environmentRecall.length) :
    ∃ snapshot, current.execution.environmentRecall[3]? = some snapshot ∧
      message ∈ snapshot.beforeView.network.inputs := by
  rcases snapshot_recorded_history seeds trace owner entry member message emitted original zero
    with early | recorded
  · omega
  · exact recorded

end Vegas.Examples.CommitSeedBroadcast
