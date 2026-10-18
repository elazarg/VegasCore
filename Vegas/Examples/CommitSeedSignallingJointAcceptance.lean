/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedSignallingCorrectSeedProbability
import Vegas.Examples.CommitSeedSignallingAcceptanceBoundary

/-! # Original Alice delivery retained in the final native acceptance joint -/

noncomputable section

namespace Vegas.Examples.CommitSeedSignalling

open SourceProgram EventGraphRuntime Interaction GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability
open OnePacketCommitRevealHypotheses (Player alice bob)

section Counted

variable (profile : ∀ who, countedModel.BehavioralPolicy who)

local notation "players" => countedMenu.decodeProfile initial horizon scheduler profile

/-- Alice's original receipt cannot first appear after Bob's polls start.
The empty early snapshot comes from the actual two initial WAIT responses. -/
theorem alice_acceptance_at_bob_prefix
    (aliceWait : players alice [] (aliceFirst.observe app alice) = PMF.pure ⟨none⟩)
    (bobWait : players bob [] ((bobFirst ⟨none⟩).observe app bob) = PMF.pure ⟨none⟩)
    (seed : Seeds) (before after : app.Execution)
    (prior : before ∈ (app.runRounds (family seed) players 12 initialExecution).support)
    (future : after ∈ (app.runRounds (family seed) players 52 before).support) :
    PhaseService.BindingAccepted runtime leaks (originalCoordinate alice) alice after ↔
      PhaseService.BindingAccepted runtime leaks (originalCoordinate alice) alice before := by
  constructor
  · intro accepted
    by_contra missing
    obtain ⟨trace⟩ := raw_counted_profile_trace profile seed 12 (by decide) before prior
    have rawTrace := rawMenu.toRawTrace initial horizon (family seed) trace
    change (app.protocol initial horizon (family seed)).Trace
      (some ⟨52, none, before⟩) at rawTrace
    have length := app.runRounds_environmentRecall_length (family seed) players 12
      initialExecution before prior
    have late : 12 ≤ before.environmentRecall.length := by
      change before.environmentRecall.length = initialExecution.environmentRecall.length + 12
        at length
      omega
    exact alice_binding_unaccepted_after_late seed players 52 52 before after
      rawTrace le_rfl future late
      (quiet_snapshot_empty profile aliceWait bobWait seed 12 (by decide) before prior alice)
      missing accepted
  · exact original_binding_accepted_runRounds (family seed) players 52 before after future alice

private theorem alice_acceptance_original_joint
    (aliceWait : players alice [] (aliceFirst.observe app alice) = PMF.pure ⟨none⟩)
    (bobWait : players bob [] ((bobFirst ⟨none⟩).observe app bob) = PMF.pure ⟨none⟩)
    (outcome : Bool × ((app.Execution × BobSeedRest) × app.Execution))
    (supported : outcome ∈ (bobPrefixFinalJoint players 52).support) :
    PhaseService.BindingAccepted runtime leaks (originalCoordinate alice) alice outcome.2.2 ↔
      PhaseService.BindingAccepted runtime leaks (originalCoordinate alice) alice
        outcome.2.1.1 := by
  rw [bobPrefixFinalJoint, PMF.support_bind] at supported
  obtain ⟨seed, _positive, selected⟩ := Set.mem_iUnion₂.mp supported
  obtain ⟨pair, reached, rfl⟩ := PMF.support_map .. ▸ selected
  rw [bindPairLaw, PMF.support_bind] at reached
  obtain ⟨before, prior, continued⟩ := Set.mem_iUnion₂.mp reached
  obtain ⟨after, future, equal⟩ := PMF.support_map .. ▸ continued
  cases equal
  exact alice_acceptance_at_bob_prefix profile aliceWait bobWait seed before after prior future

/-- The actual integrated scheduler's joint retains Alice's receipt at the
earlier prefix. The hidden seed is not redrawn at that prefix. -/
theorem alice_acceptance_physical_joint
    (aliceWait : players alice [] (aliceFirst.observe app alice) = PMF.pure ⟨none⟩)
    (bobWait : players bob [] ((bobFirst ⟨none⟩).observe app bob) = PMF.pure ⟨none⟩)
    (pair : app.Execution × app.Execution)
    (supported : pair ∈ (bindPairLaw (app.runRounds scheduler players 12 initialExecution)
      (app.runRounds scheduler players 52)).support) :
    PhaseService.BindingAccepted runtime leaks (originalCoordinate alice) alice pair.2 ↔
      PhaseService.BindingAccepted runtime leaks (originalCoordinate alice) alice pair.1 := by
  rw [← bobPrefixFinalJoint_physical players 52, PMF.support_map] at supported
  obtain ⟨outcome, reached, equal⟩ := supported
  cases equal
  exact alice_acceptance_original_joint profile aliceWait bobWait outcome reached

/-- The joint final acceptance probability is at most half Alice's own
acceptance probability, allowing arbitrary correlations with her earlier play. -/
theorem initialized_joint_acceptance_half
    (aliceWait : players alice [] (aliceFirst.observe app alice) = PMF.pure ⟨none⟩)
    (bobWait : players bob [] ((bobFirst ⟨none⟩).observe app bob) = PMF.pure ⟨none⟩) :
    let law := app.runRounds scheduler players horizon initialExecution
    (law.toOuterMeasure {final |
      PhaseService.BindingAccepted runtime leaks (originalCoordinate alice) alice final ∧
      PhaseService.BindingAccepted runtime leaks (originalCoordinate bob) bob final}).toReal ≤
      (1 / 2) * (law.toOuterMeasure {final |
        PhaseService.BindingAccepted runtime leaks (originalCoordinate alice) alice
          final}).toReal := by
  classical
  let joint := bindPairLaw (app.runRounds scheduler players 12 initialExecution)
    (app.runRounds scheduler players 52)
  let accepted : Set app.Execution := {final |
    PhaseService.BindingAccepted runtime leaks (originalCoordinate alice) alice final}
  have finalLaw : joint.map Prod.snd =
      app.runRounds scheduler players horizon initialExecution := by
    rw [bindPairLaw_map_snd, ← app.runRounds_add]
  have firstLaw : joint.map Prod.fst = app.runRounds scheduler players 12 initialExecution :=
    bindPairLaw_map_fst _ _
  have transfer (event : Set app.Execution) :
      joint.toOuterMeasure {pair | pair.2 ∈ accepted ∧ pair.2 ∈ event} =
        joint.toOuterMeasure {pair | pair.1 ∈ accepted ∧ pair.2 ∈ event} := by
    apply PMF.toOuterMeasure_apply_eq_of_inter_support_eq
    ext pair
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨⟨own, foreign⟩, supported⟩
      exact ⟨⟨(alice_acceptance_physical_joint profile aliceWait bobWait pair supported).mp own,
        foreign⟩, supported⟩
    · rintro ⟨⟨own, foreign⟩, supported⟩
      exact ⟨⟨(alice_acceptance_physical_joint profile aliceWait bobWait pair supported).mpr own,
        foreign⟩, supported⟩
  have ownMass : (app.runRounds scheduler players horizon initialExecution).toOuterMeasure
      accepted = (app.runRounds scheduler players 12 initialExecution).toOuterMeasure
        accepted := by
    rw [← finalLaw, ← firstLaw, PMF.toOuterMeasure_map_apply, PMF.toOuterMeasure_map_apply]
    change joint.toOuterMeasure {pair | pair.2 ∈ accepted} =
      joint.toOuterMeasure {pair | pair.1 ∈ accepted}
    simpa only [Set.mem_univ, and_true] using transfer Set.univ
  have bound := bob_initialized_weighted_half profile aliceWait bobWait accepted
  change _ ≤ (1 / 2) * ((app.runRounds scheduler players horizon initialExecution).toOuterMeasure
    accepted).toReal
  rw [ownMass, ← finalLaw, PMF.toOuterMeasure_map_apply]
  rw [show (Prod.snd ⁻¹' {final |
      PhaseService.BindingAccepted runtime leaks (originalCoordinate alice) alice final ∧
      PhaseService.BindingAccepted runtime leaks (originalCoordinate bob) bob final}) =
      {pair : app.Execution × app.Execution | pair.2 ∈ accepted ∧
        PhaseService.BindingAccepted runtime leaks (originalCoordinate bob) bob pair.2} from rfl]
  have transferred : joint.toOuterMeasure {pair | pair.2 ∈ accepted ∧
      PhaseService.BindingAccepted runtime leaks (originalCoordinate bob) bob pair.2} =
      joint.toOuterMeasure {pair | pair.1 ∈ accepted ∧
        PhaseService.BindingAccepted runtime leaks (originalCoordinate bob) bob pair.2} := by
    simpa only [Set.mem_ofPred_eq] using transfer {final |
      PhaseService.BindingAccepted runtime leaks (originalCoordinate bob) bob final}
  rw [transferred]
  exact bound

end Counted

end Vegas.Examples.CommitSeedSignalling
