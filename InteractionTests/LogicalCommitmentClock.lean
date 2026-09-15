/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.SealedCandidateResolution

/-! # The deadline phase of a logical commitment abstraction

Two actual candidate-runtime prefixes have identical state after erasing clock
metadata, but their next ticks have different default outcomes. This rules out
an autonomous deterministic tick on that quotient. It does not rule out a
logical protocol with separate progress and settlement events, a relative
deadline phase, or a strategic simulation using a different action translation.
-/

namespace InteractionTests.LogicalCommitmentClock

open Interaction

private def runtime : SealedResolution Bool (Option Bool) :=
  ⟨⟨[⟨.commit false, []⟩, ⟨.reveal false 0, [0]⟩]⟩, none, 2⟩

private abbrev CandidateState := SealedResolution.ApplicationState Bool (Option Bool)
  (CommitmentCandidates Bool Nat (Option Bool))

/-- Retain the full candidate catalog, events and timeout attribution. Only
absolute clock and first-readiness timestamps are erased. -/
private def withoutClock (state : CandidateState) : CandidateState :=
  { state with visible := { state.visible with readyAt := [], clock := 0 } }

/-- Both prefixes come from the actual initial state by zero or one tick; no
fabricated pending state at an already elapsed deadline is involved. -/
theorem same_clock_free_prefix :
    withoutClock runtime.candidateInitial =
      withoutClock (runtime.tick runtime.candidateInitial) := by
  rfl

/-- The first tick leaves the binding pending. The second defaults its
commitment and publishes the designated value at its reveal, without accepting
any handle. -/
theorem next_ticks_resolve_differently :
    (runtime.tick runtime.candidateInitial).visible.timeouts = [] ∧
      (runtime.tick (runtime.tick runtime.candidateInitial)).visible.timeouts = [0] ∧
      SealedProgram.accepted?
        (runtime.tick (runtime.tick runtime.candidateInitial)).visible.events 0 = none ∧
      (runtime.tick (runtime.tick runtime.candidateInitial)).visible.published? 1 =
        some none := by
  decide

/-- No deterministic update of the clock-free state reproduces a native tick
at both reachable prefixes. This is an operational factoring obstruction only;
it is not an impossibility result about Nash preservation or clock abstraction
under a different logical action interface. -/
theorem no_autonomous_clock_free_tick :
    ¬ ∃ advance : CandidateState → CandidateState,
      advance (withoutClock runtime.candidateInitial) =
          withoutClock (runtime.tick runtime.candidateInitial) ∧
        advance (withoutClock (runtime.tick runtime.candidateInitial)) =
          withoutClock (runtime.tick (runtime.tick runtime.candidateInitial)) := by
  rintro ⟨advance, hfirst, hsecond⟩
  rw [← same_clock_free_prefix] at hsecond
  have heq := congrArg (fun state : CandidateState => state.visible.timeouts)
    (hfirst.symm.trans hsecond)
  change ([] : List Nat) = [0] at heq
  cases heq

end InteractionTests.LogicalCommitmentClock

/-- info: 'InteractionTests.LogicalCommitmentClock.no_autonomous_clock_free_tick'
depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms InteractionTests.LogicalCommitmentClock.no_autonomous_clock_free_tick
