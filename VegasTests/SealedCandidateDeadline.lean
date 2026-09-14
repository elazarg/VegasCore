/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Compile.SealedCandidateDeadline
import Vegas.Compile.SealedTermination
import Interaction.SealedResolutionReservations
import VegasTests.SealedSourceExtraction

/-! # Honest deadlines with an arbitrary candidate-host opponent

A checked two-player source commits and reveals once per player. Player zero
may use any native policy, including competing or unopenable candidates and
withholding. Player one's compiled policy meets both of its deadlines under
delayed periodic inclusion, even if player zero's sites resolve by default.
The reserved service class and supported completed execution are inhabited.
-/

noncomputable section

namespace VegasTests.SealedCandidateDeadline

open Vegas Vegas.EventGraph Interaction Interaction.MessageApplication
open GameTheory.Math.Probability
open SealedSourceExtraction (source graph node supported)

private abbrev Principal := SealedSourceExtraction.Player
private abbrev runtime := supported.resolvingRuntime none 14
private abbrev app := runtime.candidateApplication

private def initial : app.PolicyExecution :=
  PolicyExecution.initial app (State.initial app runtime.candidateInitial)

private def players (profile : CommitPolicyProfile graph) (replacement : app.PlayerPolicy) :
    Principal → app.PlayerPolicy := fun who =>
  if who = 0 then replacement else
    runtime.candidatePlayerPolicy (supported.resolvingPolicy none 14 who (profile who))

private def wire (base : app.WirePolicy) : app.WirePolicy :=
  app.reserveInclusion (SealedResolution.periodicFinalReservation 4 2) base

/-- The honest second player meets both deadlines, under every native first
player policy and arbitrary adaptive unreserved delivery or inclusion choices. -/
theorem honest_player_meets_deadlines
    (profile : CommitPolicyProfile graph) (replacement : app.PlayerPolicy)
    (base : app.WirePolicy) (periods : Nat) (next : app.PolicyExecution)
    (hnext : next ∈ (runtime.candidateRoundDriver.runRounds [0, 1] 4
      (players profile replacement) (wire base) (2 * periods) initial).support) :
    2 ∉ next.native.application.visible.timeouts ∧
      3 ∉ next.native.application.visible.timeouts := by
  have hclear (index : Fin 4)
      (howned :
        (∃ guard, (graph.nodeRow (node index)).sem = .commit 1 guard) ∨
        ∃ (producer : Fin graph.nodeCount) (guard : EventGuard simpleExpr),
          (graph.nodeRow (node index)).sem = .reveal (graph.nodeTarget producer) ∧
          (graph.nodeRow producer).sem = .commit 1 guard) :
      (node index).val ∉ next.native.application.visible.timeouts := by
    exact supported.candidate_runRounds_no_timeout none 14 [0, 1] 4
      (players profile replacement) (wire base) (SealedResolution.periodicFinalReservation 4 2)
      (app.reserveInclusion_service _ base) 2 (by decide)
      (fun block => SealedResolution.periodicFinalReservation_capacity [0, 1] 4 2 block
        (by decide) (by decide))
      1 (profile 1) (by simp [players]) (node index) howned 1 rfl
      (by fin_cases index <;> decide) (2 * periods) ⟨periods, rfl⟩ next hnext
  exact ⟨hclear 2 (Or.inl ⟨_, rfl⟩), hclear 3 (Or.inr ⟨node 2, _, rfl, rfl⟩)⟩

/-- Arbitrary deviator and wire policies still have a completed supported
execution with no honest timeout. Only the deviator may require defaults. -/
theorem exists_protected_completion
    (profile : CommitPolicyProfile graph) (replacement : app.PlayerPolicy)
    (base : app.WirePolicy) :
    ∃ next ∈ (runtime.candidateRoundDriver.runRounds [0, 1] 4
        (players profile replacement) (wire base) 60 initial).support,
      runtime.complete next.native.application.visible = true ∧
        2 ∉ next.native.application.visible.timeouts ∧
        3 ∉ next.native.application.visible.timeouts := by
  obtain ⟨next, hnext⟩ := (runtime.candidateRoundDriver.runRounds [0, 1] 4
    (players profile replacement) (wire base) 60 initial).support_nonempty
  refine ⟨next, hnext, ?_, honest_player_meets_deadlines profile replacement base 30 next hnext⟩
  exact supported.candidateRuntime_runRounds_complete none 14 [0, 1] 4
    (players profile replacement) (wire base) 60 (by decide) next hnext

end VegasTests.SealedCandidateDeadline

/-- info: 'VegasTests.SealedCandidateDeadline.honest_player_meets_deadlines'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VegasTests.SealedCandidateDeadline.honest_player_meets_deadlines

/-- info: 'VegasTests.SealedCandidateDeadline.exists_protected_completion'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VegasTests.SealedCandidateDeadline.exists_protected_completion
