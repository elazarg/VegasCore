/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedBroadcastForeignGoodAdmission
import Vegas.Examples.CommitSeedBroadcastOriginalRecordedOmission

/-! # Admission determined by retained eligible good-owner responses -/

noncomputable section

namespace Vegas.Examples.CommitSeedBroadcast

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

/-- Once a good owner's two eligible opportunities have passed, its original
receipt is determined by its retained transmissions, independently of all
later responses and every private preparation. -/
theorem good_original_receipt_iff_two_records (seed : Seeds) (remaining : Nat)
    (final : app.Execution)
    (trace : (countedMenu.protocol initial horizon (family seed)).Trace
      (some ⟨remaining, none, final⟩))
    (owner : Player) (good : seed.2 owner = true)
    (resolved : (originalCoordinate owner).Resolved final.application)
    (first second : app.PlayerEntry)
    (firstMember : first ∈ final.recall owner) (secondMember : second ∈ final.recall owner)
    (firstRequest : PhaseRuntimeState.requests first.beforeView.application.2 owner
      (originalCoordinate owner))
    (secondRequest : PhaseRuntimeState.requests second.beforeView.application.2 owner
      (originalCoordinate owner))
    (firstClock : first.beforeView.application.2.native.clock = 0)
    (secondClock : second.beforeView.application.2.native.clock = 2) :
    PhaseService.BindingAccepted runtime leaks (originalCoordinate owner) owner final ↔
      first.action.transmission ≠ none ∨ second.action.transmission ≠ none := by
  classical
  constructor
  · intro accepted
    by_cases sentFirst : first.action.transmission ≠ none
    · exact Or.inl sentFirst
    by_cases sentSecond : second.action.transmission ≠ none
    · exact Or.inr sentSecond
    exact (original_good_binding_waits_unaccepted seed ⟨remaining, none, final⟩ trace owner good
      first second firstMember secondMember firstRequest secondRequest
        (not_not.mp sentFirst) (not_not.mp sentSecond) firstClock secondClock accepted).elim
  · intro emitted
    have characterization := original_binding_accepted_iff_clocks seed
      ⟨remaining, none, final⟩ trace owner resolved
    rcases emitted with firstSent | secondSent
    · obtain ⟨material, transmitted⟩ := Option.ne_none_iff_exists'.mp firstSent
      exact characterization.mpr (Or.inl (original_recorded_transmission_clock seed remaining
        final trace owner first firstMember firstRequest material transmitted 0 firstClock))
    · obtain ⟨material, transmitted⟩ := Option.ne_none_iff_exists'.mp secondSent
      have late : lateClock (seed.2 owner) = 2 := by rw [good]; rfl
      apply characterization.mpr
      right
      rw [late]
      exact original_recorded_transmission_clock seed remaining final trace owner second
        secondMember secondRequest material transmitted 2 secondClock

/-- An earlier good-slot omission remains a miss under both preparation
comparators; an earlier emission remains an admission under both. -/
theorem good_two_records_run_admission_iff (seed : Seeds) (remaining : Nat)
    (anchor : app.Execution)
    (trace : (countedMenu.protocol initial horizon (family seed)).Trace
      (some ⟨remaining, none, anchor⟩))
    (owner : Player) (good : seed.2 owner = true)
    (first second : app.PlayerEntry) (word : anchor.recall owner = [first, second])
    (firstRequest : PhaseRuntimeState.requests first.beforeView.application.2 owner
      (originalCoordinate owner))
    (secondRequest : PhaseRuntimeState.requests second.beforeView.application.2 owner
      (originalCoordinate owner))
    (firstClock : first.beforeView.application.2.native.clock = 0)
    (secondClock : second.beforeView.application.2.native.clock = 2)
    (players : Player → app.Policy)
    (covered : ∀ who past view action, action ∈ (players who past view).support →
      action ∈ countedMenu.actions who past view)
    (final : app.Execution)
    (reached : final ∈ (app.runRounds (family seed) players remaining anchor).support)
    (resolved : (originalCoordinate owner).Resolved final.application) :
    PhaseService.BindingAccepted runtime leaks (originalCoordinate owner) owner final ↔
      first.action.transmission ≠ none ∨ second.action.transmission ≠ none := by
  obtain ⟨finalTrace⟩ := countedMenu.trace_runRounds initial horizon (family seed) players covered
    0 remaining anchor final (by simpa only [Nat.zero_add] using trace) reached
  have retained := rounds_recall_retained (family seed) players remaining anchor final reached owner
  have firstMember : first ∈ final.recall owner := retained.subset (by rw [word]; simp)
  have secondMember : second ∈ final.recall owner := retained.subset (by rw [word]; simp)
  exact good_original_receipt_iff_two_records seed 0 final finalTrace owner good resolved
    first second firstMember secondMember firstRequest secondRequest firstClock secondClock

end Vegas.Examples.CommitSeedBroadcast
