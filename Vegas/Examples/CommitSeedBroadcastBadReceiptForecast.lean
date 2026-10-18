/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedBroadcastBadHelperAdmission

/-! # Original bad-owner nonadmission without an initial public helper packet -/

noncomputable section

namespace Vegas.Examples.CommitSeedBroadcast

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

/-- Without initial public packets, the actual first-late response spends the
bad owner's one counted packet in its ineligible slot. Later play cannot admit it. -/
theorem foreign_singleton_bad_no_helper_unaccepted
    (assessment : rawModel.BehavioralAssessment)
    (equilibrium : assessment.IsSequentialEquilibrium
      (rawMenu.decisionInformationAntichain initial horizon scheduler)
      canonicalCertificate rawPayoff)
    (seed : Seeds) (supportedSeed : seed ∈ nativeSeedLaw.support)
    (remaining : Nat) (anchor : app.Execution)
    (trace : (countedMenu.protocol initial horizon (family seed)).Trace
      (some ⟨remaining, none, anchor⟩))
    (owner : Player) (bad : seed.2 owner = false)
    (started : 5 ≤ anchor.environmentRecall.length)
    (ahead : anchor.environmentRecall.length ≤ 11 + (seed.1.symm owner).val)
    (first : app.PlayerEntry) (word : anchor.recall owner = [first])
    (firstRequest : PhaseRuntimeState.requests first.beforeView.application.2 owner
      (originalCoordinate owner))
    (zero : first.beforeView.application.2.native.clock = 0)
    (noHelper : initialPublicPackets anchor = ∅)
    (players : Player → app.Policy)
    (covered : ∀ who past view action, action ∈ (players who past view).support →
      action ∈ countedMenu.actions who past view)
    (selected : players owner = countedMenu.decodeProfile initial horizon scheduler
      (countedAssessmentProfile assessment) owner)
    (final : app.Execution)
    (reached : final ∈ (app.runRounds (family seed) players remaining anchor).support) :
    ¬ PhaseService.BindingAccepted runtime leaks (originalCoordinate owner) owner final := by
  classical
  obtain ⟨finalTrace⟩ := countedMenu.trace_runRounds initial horizon (family seed) players covered
    0 remaining anchor final (by simpa only [Nat.zero_add] using trace) reached
  have silent : first.action.transmission = none := by
    cases sent : first.action.transmission with
    | none => rfl
    | some material =>
        have helper := initial_record_transmission_packets_nonempty seed remaining anchor trace
          owner first (by rw [word]; exact List.mem_singleton_self _) firstRequest zero material
            sent (by omega)
        exact (helper noHelper).elim
  have outputs := silent_own_outputs_of_history (family seed) _
    (countedMenu.toRawTrace initial horizon (family seed) trace) owner (by
      intro entry member
      rw [word, List.mem_singleton] at member
      subst entry
      exact silent)
  have missing := outputs_empty_original_unaccepted seed remaining anchor trace owner outputs
  have request := original_request_of_unaccepted_before_expiry seed _
    (countedMenu.toRawTrace initial horizon (family seed) trace) owner missing (by
      change anchor.environmentRecall.length < 28
      have rank := (seed.1.symm owner).isLt
      omega)
  let count := 11 + (seed.1.symm owner).val - anchor.environmentRecall.length
  have target : anchor.environmentRecall.length + count = 11 + (seed.1.symm owner).val := by
    dsimp only [count]
    omega
  have budget := (countedMenu.roundSupported_uniform initial horizon (family seed) trace).1
  change anchor.environmentRecall.length + remaining = horizon at budget
  have rank := (seed.1.symm owner).isLt
  have enough : count + 1 ≤ remaining := by dsimp only [horizon] at budget; omega
  have split : remaining = (count + 1) + (remaining - (count + 1)) := by omega
  have actual := reached
  rw [split, app.runRounds_add] at actual
  obtain ⟨middle, stage, following⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ actual)
  obtain ⟨before, observed, action, _before, _observed, _command, ⟨observedTrace⟩,
    observedRequest, observedClock, observedWord, chosen, middleEq⟩ :=
      bad_owner_firstLate_callback seed remaining anchor owner bad trace request
        (by rw [outputs]; exact fun _ member => (List.not_mem_nil member).elim) started ahead
        players covered middle stage
  have countdown : remaining - count - 1 = remaining - (count + 1) := by omega
  change (countedMenu.protocol initial horizon (family seed)).Trace
    (some ⟨remaining - count - 1, some owner, observed⟩) at observedTrace
  rw [countdown] at observedTrace
  have wordTwo : observed.recall owner = [first] := observedWord.trans word
  have packets : initialPublicPackets observed = ∅ := by
    have preserved := runRounds_initialPublicPackets (family seed) players (count + 1) anchor
      middle (by omega) stage
    rw [middleEq] at preserved
    exact preserved.trans noHelper
  have empty := (bad_firstLate_receipts_empty_iff_initial_packets seed _
    (countedMenu.toRawTrace initial horizon (family seed) observedTrace) owner rfl
      observedRequest.1.symm observedClock bad).mpr packets
  obtain ⟨mixed⟩ := counted_fixed_decision_mixed seed supportedSeed _ observed owner observedTrace
  let source : countedProtocol.History := ⟨_, mixed⟩
  have responseLaw := counted_assessment_response_law assessment equilibrium source _ observed
    owner rfl
  have rawChosen : action ∈ (rawMenu.decodeProfile initial horizon scheduler assessment.strategy
      owner (observed.recall owner) (observed.observe app owner)).support := by
    rw [← responseLaw, ← selected]
    exact chosen
  have neverWait := raw_first_late_response_ne_wait assessment equilibrium source _ observed owner
    rfl observedRequest observedClock empty first wordTwo firstRequest silent zero
  have nonsilent : action.transmission ≠ none := by
    intro nothing
    have actionEq : action = (⟨none⟩ : app.Action) := by
      have eta : action = ⟨action.transmission⟩ := by cases action; rfl
      exact eta.trans (congrArg ReactiveApplication.Action.mk nothing)
    rw [actionEq] at rawChosen
    exact neverWait rawChosen
  obtain ⟨material, sent⟩ := Option.ne_none_iff_exists'.mp nonsilent
  obtain ⟨emitted, recalled⟩ := app.respond_recall_entry observed owner action
  let entry : app.PlayerEntry := ⟨observed.observe app owner, action, emitted⟩
  rw [middleEq] at following
  have member : entry ∈ final.recall owner :=
    (rounds_recall_retained (family seed) players _ _ final following owner).subset (by
      rw [recalled]
      exact List.mem_append_right _ (List.mem_singleton_self _))
  have valid := raw_native_valid (family seed) _
    (countedMenu.toRawTrace initial horizon (family seed) observedTrace)
  have entryRequest : PhaseRuntimeState.requests entry.beforeView.application.2 owner
      (originalCoordinate owner) :=
    (observed.application.requests_publicView valid owner (originalCoordinate owner)).mpr
      observedRequest
  exact bad_clock_two_record_unaccepted seed 0 final finalTrace owner bad entry member entryRequest
    material sent observedClock

/-- The actual original receipt forecast depends on the fixed initial public
word, rather than later hidden preparations or a refreshed service prior. -/
theorem foreign_singleton_bad_original_admission_iff_packets
    (assessment : rawModel.BehavioralAssessment)
    (equilibrium : assessment.IsSequentialEquilibrium
      (rawMenu.decisionInformationAntichain initial horizon scheduler)
      canonicalCertificate rawPayoff)
    (seed : Seeds) (supportedSeed : seed ∈ nativeSeedLaw.support)
    (remaining : Nat) (anchor : app.Execution)
    (trace : (countedMenu.protocol initial horizon (family seed)).Trace
      (some ⟨remaining, none, anchor⟩))
    (owner : Player) (bad : seed.2 owner = false)
    (started : 5 ≤ anchor.environmentRecall.length)
    (ahead : anchor.environmentRecall.length ≤ 11 + (seed.1.symm owner).val)
    (first : app.PlayerEntry) (word : anchor.recall owner = [first])
    (firstRequest : PhaseRuntimeState.requests first.beforeView.application.2 owner
      (originalCoordinate owner))
    (zero : first.beforeView.application.2.native.clock = 0)
    (players : Player → app.Policy)
    (covered : ∀ who past view action, action ∈ (players who past view).support →
      action ∈ countedMenu.actions who past view)
    (selected : players owner = countedMenu.decodeProfile initial horizon scheduler
      (countedAssessmentProfile assessment) owner)
    (final : app.Execution)
    (reached : final ∈ (app.runRounds (family seed) players remaining anchor).support)
    (resolved : (originalCoordinate owner).Resolved final.application) :
    PhaseService.BindingAccepted runtime leaks (originalCoordinate owner) owner final ↔
      initialPublicPackets anchor ≠ ∅ := by
  constructor
  · intro accepted empty
    exact foreign_singleton_bad_no_helper_unaccepted assessment equilibrium seed supportedSeed
      remaining anchor trace owner bad started ahead first word firstRequest zero empty players
        covered selected final reached accepted
  · intro helper
    exact foreign_singleton_bad_helper_original_admission assessment equilibrium seed supportedSeed
      remaining anchor trace owner bad started ahead first word firstRequest zero helper players
        covered selected final reached resolved

end Vegas.Examples.CommitSeedBroadcast
