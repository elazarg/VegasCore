/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Compile.SealedPolicyDeadline
import Vegas.Compile.SealedTermination
import Interaction.SealedResolutionReservations
import VegasTests.SealedPolicy

/-! # Checked-source deadline guarantees under delayed periodic service

The multistage checked source is run with its actual compiled behavioral
policies. The environment reserves the second round of each two-round period;
all first-round wire decisions remain adaptive. The result holds for every
source kernel, not just a fixed transcript, and includes source choices of null.
-/

noncomputable section

namespace VegasTests.SealedPolicyDeadline

open Vegas Vegas.EventGraph Vegas.ToEventGraph Interaction Interaction.MessageApplication
open GameTheory.Math.Probability PendingStages

private abbrev runtime := supported.resolvingRuntime none 14
private abbrev app := runtime.messageApplication

private def initial : app.PolicyExecution :=
  PolicyExecution.initial app (State.initial app runtime.initial)

private def players (profile : SourceBehavioralProfile core) : PendingStages.Player →
    app.PlayerPolicy := fun who =>
  SealedPolicy.compilation.compileResolvingPolicy none 14 who (profile who)

private def wire (base : app.WirePolicy) : app.WirePolicy :=
  app.reserveInclusion (SealedResolution.periodicFinalReservation 2 2) base

/-- Every source site meets its deadline for arbitrary source policies and
arbitrary adaptive wire choices in unreserved service phases. -/
theorem every_site_meets_deadline (profile : SourceBehavioralProfile core)
    (base : app.WirePolicy) (periods : Nat) (next : app.PolicyExecution)
    (hnext : next ∈ (runtime.runRounds [0] 2 (players profile) (wire base)
      (2 * periods) initial).support) (index : Fin 4) :
    (node index).val ∉ next.native.application.visible.timeouts := by
  let policy := compileSourcePolicy core source.core.fresh SealedPolicy.initialBuild rfl 0
    (profile 0)
  have howned :
      (∃ guard, (graph.nodeRow (node index)).sem = .commit 0 guard) ∨
      ∃ (producer : Fin graph.nodeCount) (guard : EventGuard simpleExpr),
        (graph.nodeRow (node index)).sem = .reveal (graph.nodeTarget producer) ∧
        (graph.nodeRow producer).sem = .commit 0 guard := by
    fin_cases index
    · exact Or.inl ⟨_, rfl⟩
    · exact Or.inr ⟨node 0, _, rfl, rfl⟩
    · exact Or.inl ⟨_, rfl⟩
    · exact Or.inr ⟨node 2, _, rfl, rfl⟩
  exact supported.runRounds_no_timeout none 14 [0] 2 (players profile) (wire base)
    (SealedResolution.periodicFinalReservation 2 2)
    (app.reserveInclusion_service _ base) 2 (by decide)
    (fun block => SealedResolution.periodicFinalReservation_capacity [0] 2 2 block
      (by decide) (by decide))
    0 policy rfl (node index) howned 0 rfl (by fin_cases index <;> decide)
    (2 * periods) ⟨periods, rfl⟩ next hnext

/-- A normal completed execution actually exists for every original source
profile and every unreserved wire policy; the deadline premises are inhabited. -/
theorem exists_complete_without_timeouts (profile : SourceBehavioralProfile core)
    (base : app.WirePolicy) :
    ∃ next ∈ (runtime.runRounds [0] 2 (players profile) (wire base) 60 initial).support,
      runtime.complete next.native.application.visible = true ∧
        next.native.application.visible.timeouts = [] := by
  obtain ⟨next, hnext⟩ :=
    (runtime.runRounds [0] 2 (players profile) (wire base) 60 initial).support_nonempty
  refine ⟨next, hnext, ?_, ?_⟩
  · exact SealedPolicy.compilation.resolvingRuntime_runRounds_complete none 14 [0] 2
      (players profile) (wire base) next hnext
  · let graphProfile := fun who => compileSourcePolicy core source.core.fresh
      SealedPolicy.initialBuild rfl who (profile who)
    exact supported.runRounds_timeouts_eq_nil none 14 [0] 2 graphProfile (wire base)
      (SealedResolution.periodicFinalReservation 2 2) (app.reserveInclusion_service _ base)
      2 (by decide) (fun block => SealedResolution.periodicFinalReservation_capacity [0] 2 2
        block (by decide) (by decide))
      (by intro who; fin_cases who; simp) (by decide) 60 ⟨30, rfl⟩ next hnext

end VegasTests.SealedPolicyDeadline
