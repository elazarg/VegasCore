/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedBroadcastRegularAdmission

/-! # Future good-owner admission without assumptions on earlier foreign omissions -/

noncomputable section

namespace Vegas.Examples.CommitSeedBroadcast

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

/-- An owner whose anchor word contains only its initial response uses the
unchanged assessed strategy at its later first-late callback. Other owners'
retained responses may include arbitrary earlier timing errors. -/
theorem singleton_anchored_first_late_transmits
    (assessment : rawModel.BehavioralAssessment)
    (equilibrium : assessment.IsSequentialEquilibrium
      (rawMenu.decisionInformationAntichain initial horizon scheduler)
      canonicalCertificate rawPayoff)
    (seed : Seeds) (supportedSeed : seed ∈ nativeSeedLaw.support)
    (anchor : app.Execution) (owner : Player) (short : (anchor.recall owner).length = 1)
    (players : Player → app.Policy)
    (selected : players owner = countedMenu.decodeProfile initial horizon scheduler
      (countedAssessmentProfile assessment) owner)
    (final : app.Execution) (retained : anchor.recall owner <+: final.recall owner)
    (consistent : (app.anchoredPolicy anchor players owner).Consistent (final.recall owner)) :
    FirstLateOwnerTransmits seed final owner := by
  classical
  intro remaining execution trace request clock empty first word firstRequest silent zero entry
    recorded viewed
  obtain ⟨after, decomposition⟩ := recorded
  have faithful := consistent
  rw [decomposition, ← List.singleton_append, ← List.append_assoc] at faithful
  have chosen := ((app.anchoredPolicy anchor players owner).consistent_snoc_iff
    (execution.recall owner) entry).mp (ReactiveApplication.Policy.Consistent.of_append faithful)
  have supported : entry.action ∈ (app.anchoredPolicy anchor players owner
      (execution.recall owner) (execution.observe app owner)).support := by
    simpa only [viewed] using chosen.2
  obtain ⟨rest, retainedWord⟩ := retained
  rw [decomposition, word] at retainedWord
  have oldPast : anchor.recall owner = execution.recall owner := by
    cases old : anchor.recall owner with
    | nil => simp only [old, List.length_nil] at short; omega
    | cons head tail =>
        have tailEmpty : tail = [] := List.length_eq_zero_iff.mp (by
          simp only [old, List.length_cons] at short; omega)
        subst tail
        rw [old] at retainedWord
        have headEq : head = first := (List.cons.inj retainedWord).1
        rw [word, headEq]
  rw [app.anchoredPolicy_of_extends anchor players owner _ _
    (oldPast ▸ List.prefix_refl _), selected] at supported
  obtain ⟨mixed⟩ := counted_fixed_decision_mixed seed supportedSeed remaining execution owner trace
  let source : countedProtocol.History := ⟨_, mixed⟩
  rw [counted_assessment_response_law assessment equilibrium source remaining execution owner rfl]
    at supported
  intro waited
  have same : entry.action = ⟨none⟩ := by
    have eta : entry.action = ⟨entry.action.transmission⟩ := by cases entry.action; rfl
    exact eta.trans (congrArg ReactiveApplication.Action.mk waited)
  rw [same] at supported
  exact raw_first_late_response_ne_wait assessment equilibrium source remaining execution owner
    rfl request clock empty first word firstRequest silent zero supported

/-- Every still-unpolled good owner obtains original admission under its
unchanged assessed continuation. Earlier foreign omissions are unrestricted. -/
theorem foreign_singleton_good_original_admission
    (assessment : rawModel.BehavioralAssessment)
    (equilibrium : assessment.IsSequentialEquilibrium
      (rawMenu.decisionInformationAntichain initial horizon scheduler)
      canonicalCertificate rawPayoff)
    (seed : Seeds) (supportedSeed : seed ∈ nativeSeedLaw.support)
    (remaining : Nat) (anchor : app.Execution)
    (trace : (countedMenu.protocol initial horizon (family seed)).Trace
      (some ⟨remaining, none, anchor⟩))
    (owner : Player) (short : (anchor.recall owner).length = 1) (good : seed.2 owner = true)
    (players : Player → app.Policy)
    (covered : ∀ who past view action, action ∈ (players who past view).support →
      action ∈ countedMenu.actions who past view)
    (selected : players owner = countedMenu.decodeProfile initial horizon scheduler
      (countedAssessmentProfile assessment) owner)
    (final : app.Execution)
    (reached : final ∈ (app.runRounds (family seed) players remaining anchor).support)
    (resolved : ∀ who, (originalCoordinate who).Resolved final.application) :
    PhaseService.BindingAccepted runtime leaks (originalCoordinate owner) owner final := by
  classical
  let replay := app.anchoredPolicy anchor players
  have sameFuture : app.runRounds (family seed) replay remaining anchor =
      app.runRounds (family seed) players remaining anchor :=
    app.runRounds_anchoredPolicy (family seed) anchor players remaining
  have replayReached : final ∈ (app.runRounds (family seed) replay remaining anchor).support := by
    rw [sameFuture]
    exact reached
  have consistent := (app.consistentRecall_policyInvariant replay).runRounds (family seed)
    remaining anchor final (app.anchoredPolicy_consistent anchor players) replayReached
  have retained := rounds_recall_retained (family seed) replay remaining anchor final
    replayReached owner
  have transmits := singleton_anchored_first_late_transmits assessment equilibrium seed
    supportedSeed anchor owner short players selected final retained (consistent owner)
  have replayCovered : ∀ who past view response, response ∈ (replay who past view).support →
      response ∈ countedMenu.actions who past view := by
    intro who
    exact countedMenu.anchoredPolicy_covered initial horizon (family seed)
      ⟨remaining, none, anchor⟩ trace players who (covered who)
  obtain ⟨enough, anchorReached⟩ := app.mem_roundsFrom_anchoredPolicy_of_trace initial horizon
    (family seed) players (countedMenu.toRawTrace initial horizon (family seed) trace)
  have initializedAnchor : anchor ∈ (app.runRounds (family seed) replay
      (horizon - remaining) initialExecution).support := by
    simpa only [ReactiveApplication.roundsFrom, initial, PMF.pure_bind, initialExecution]
      using anchorReached
  have initializedFinal : final ∈
      (app.runRounds (family seed) replay horizon initialExecution).support := by
    have split : horizon = (horizon - remaining) + remaining := by omega
    rw [split, app.runRounds_add, PMF.support_bind]
    exact Set.mem_iUnion₂.mpr ⟨anchor, initializedAnchor, replayReached⟩
  exact good_original_admission seed owner good replay replayCovered final transmits
    initializedFinal resolved

end Vegas.Examples.CommitSeedBroadcast
