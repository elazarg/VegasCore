/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedBroadcastAllGoodAdmission
import Vegas.Examples.CommitSeedBroadcastFirstLateTiming
import Vegas.Examples.CommitSeedBroadcastAssessedResponse
import Vegas.Examples.CommitSeedBroadcastSeedTrace
import Vegas.Examples.CommitSeedBroadcastSeedAtoms
import Interaction.ReactiveAnchoredMixture
import Interaction.ReactiveConsistentHistory

/-! # Regular original prefixes under the unchanged assessed foreign strategies -/

noncomputable section

namespace Vegas.Examples.CommitSeedBroadcast

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

def RegularResponsePrefix (anchor : app.Execution) : Prop :=
  ∀ who, (anchor.recall who).length = 1 ∨
    (anchor.recall who).length = 2 ∧
      ((anchor.recall who).getLast?).map ReactiveApplication.PlayerEntry.action ≠ some ⟨none⟩

private theorem silent_action (action : app.Action) :
    action.transmission = none ↔ action = ⟨none⟩ := by
  cases action
  exact ⟨congrArg _, congrArg ReactiveApplication.Action.transmission⟩

/-- The old word is replayed literally. A new foreign clock-two record uses
its actual assessed response at the same full input, even off the equilibrium path. -/
theorem regular_anchored_record_transmits
    (assessment : rawModel.BehavioralAssessment)
    (equilibrium : assessment.IsSequentialEquilibrium
      (rawMenu.decisionInformationAntichain initial horizon scheduler)
      canonicalCertificate rawPayoff)
    (seed : Seeds) (supportedSeed : seed ∈ nativeSeedLaw.support)
    (anchor : app.Execution) (focal : Player) (long : (anchor.recall focal).length = 2)
    (regular : RegularResponsePrefix anchor)
    (players : Player → app.Policy)
    (foreign : ∀ who, who ≠ focal → players who =
      countedMenu.decodeProfile initial horizon scheduler (countedAssessmentProfile assessment) who)
    (final : app.Execution) (retained : ∀ who, anchor.recall who <+: final.recall who)
    (consistent : ∀ who, (app.anchoredPolicy anchor players who).Consistent (final.recall who)) :
    FirstLateRecordedTransmits seed final := by
  classical
  intro owner remaining execution trace request clock empty first word firstRequest silent zero
    entry recorded viewed
  obtain ⟨after, decomposition⟩ := recorded
  have faithful := consistent owner
  rw [decomposition, ← List.singleton_append, ← List.append_assoc] at faithful
  have chosen := ((app.anchoredPolicy anchor players owner).consistent_snoc_iff
    (execution.recall owner) entry).mp (ReactiveApplication.Policy.Consistent.of_append faithful)
  have supported : entry.action ∈ (app.anchoredPolicy anchor players owner
      (execution.recall owner) (execution.observe app owner)).support := by
    simpa only [viewed] using chosen.2
  obtain ⟨rest, retainedWord⟩ := retained owner
  rw [decomposition, word] at retainedWord
  rcases regular owner with short | ⟨two, nonsilent⟩
  · have ownerNe : owner ≠ focal := by intro same; subst owner; omega
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
      (oldPast ▸ List.prefix_refl _), foreign owner ownerNe] at supported
    obtain ⟨mixed⟩ := counted_fixed_decision_mixed seed supportedSeed remaining execution owner
      trace
    let source : countedProtocol.History := ⟨_, mixed⟩
    rw [counted_assessment_response_law assessment equilibrium source remaining execution owner rfl]
      at supported
    intro waited
    have same : entry.action = ⟨none⟩ := (silent_action _).mp waited
    rw [same] at supported
    exact raw_first_late_response_ne_wait assessment equilibrium source remaining execution owner
      rfl request clock empty first word firstRequest silent zero supported
  · cases old : anchor.recall owner with
    | nil => simp only [old, List.length_nil] at two; omega
    | cons head tail =>
        cases tail with
        | nil => simp only [old, List.length_cons, List.length_nil] at two; omega
        | cons second tail =>
            have tailEmpty : tail = [] := List.length_eq_zero_iff.mp (by
              simp only [old, List.length_cons] at two; omega)
            subst tail
            rw [old] at retainedWord
            have entryEq : second = entry := (List.cons.inj (List.cons.inj retainedWord).2).1
            intro waited
            apply nonsilent
            rw [old]
            change some second.action = some ⟨none⟩
            rw [entryEq, (silent_action _).mp waited]

end Vegas.Examples.CommitSeedBroadcast
