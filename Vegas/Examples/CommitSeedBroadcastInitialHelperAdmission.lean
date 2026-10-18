/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedBroadcastBadReceiptForecast
import Vegas.Examples.CommitSeedBroadcastForeignGoodAdmission
import Vegas.Examples.CommitSeedBroadcastFirstLateRecord
import Vegas.Examples.CommitSeedBroadcastOriginalCompletion

/-! # Original admission after an actual initial helper transmission -/

noncomputable section

namespace Vegas.Examples.CommitSeedBroadcast

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

/-- The actual fifth-command frame retains each owner's literal initial record,
including its arbitrary hidden preparation and evidence. -/
theorem frame_five_initial_record (seed : Seeds) (remaining : Nat) (frame : app.Execution)
    (trace : (countedMenu.protocol initial horizon (family seed)).Trace
      (some ⟨remaining, none, frame⟩))
    (position : frame.environmentRecall.length = 5) (owner : Player) :
    ∃ first : app.PlayerEntry, frame.recall owner = [first] ∧
      PhaseRuntimeState.requests first.beforeView.application.2 owner
        (originalCoordinate owner) ∧ first.beforeView.application.2.native.clock = 0 := by
  classical
  have actual := (countedMenu.roundSupported_uniform initial horizon (family seed) trace).2
  change frame ∈ (app.roundsFrom initial (family seed) countedMenu.uniformResponses
    frame.environmentRecall.length).support at actual
  rw [position] at actual
  have started : frame ∈ (app.runRounds (family seed) countedMenu.uniformResponses 5
      initialExecution).support := by
    simpa only [ReactiveApplication.roundsFrom, initial, PMF.pure_bind, initialExecution]
      using actual
  rw [first_five_rounds] at started
  obtain ⟨firstAction, _first, afterFirst⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ started)
  obtain ⟨secondAction, _second, afterSecond⟩ :=
    Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ afterFirst)
  obtain ⟨thirdAction, _third, same⟩ := (PMF.mem_support_map_iff _ _ _).mp afterSecond
  have frameWord : frame.recall owner =
      (afterInitialResponses firstAction secondAction thirdAction).recall owner :=
    (congrArg (fun current : app.Execution => current.recall owner) same.symm).trans
      (show (initialClockTwo firstAction secondAction thirdAction).recall owner =
        (afterInitialResponses firstAction secondAction thirdAction).recall owner from rfl)
  have length : (frame.recall owner).length = 1 := by
    rw [frameWord]
    exact initial_record_length firstAction secondAction thirdAction owner
  obtain ⟨first, word⟩ : ∃ first, frame.recall owner = [first] := by
    cases recalled : frame.recall owner with
    | nil => simp only [recalled, List.length_nil] at length; omega
    | cons first rest =>
        have restEmpty : rest = [] := List.length_eq_zero_iff.mp (by
          simp only [recalled, List.length_cons] at length
          omega)
        exact ⟨first, by rw [restEmpty]⟩
  have member : first ∈ (afterInitialResponses firstAction secondAction thirdAction).recall
      owner := by
    rw [← frameWord, word]
    exact List.mem_singleton_self _
  have publicView := initial_record_public firstAction secondAction thirdAction owner first member
  refine ⟨first, word, ?_, ?_⟩
  · rw [publicView]
    exact initial_bindings_ready owner
  · rw [publicView]
    exact initialState_clock

private theorem frame_finish_original_resolved (seed : Seeds) (remaining : Nat)
    (frame : app.Execution)
    (trace : (countedMenu.protocol initial horizon (family seed)).Trace
      (some ⟨remaining, none, frame⟩))
    (players : Player → app.Policy)
    (covered : ∀ who past view action, action ∈ (players who past view).support →
      action ∈ countedMenu.actions who past view)
    (final : app.Execution)
    (reached : final ∈ (app.runRounds (family seed) players remaining frame).support) :
    ∀ owner, (originalCoordinate owner).Resolved final.application := by
  obtain ⟨finalTrace⟩ := countedMenu.trace_runRounds initial horizon (family seed) players covered
    0 remaining frame final (by simpa only [Nat.zero_add] using trace) reached
  have raw := countedMenu.toRawTrace initial horizon (family seed) finalTrace
  have accounted := app.raw_trace_horizon initial horizon (family seed) raw
  change final.environmentRecall.length + 0 = horizon at accounted
  intro owner
  exact original_bindings_resolved seed ⟨0, none, final⟩ raw (by
    change 30 ≤ final.environmentRecall.length
    dsimp only [horizon] at accounted
    omega) owner

/-- When every future owner uses its assessed counted policy, a nonempty actual
initial packet word forces admission of all originals, for every original seed. -/
theorem frame_helper_assessed_original_admissions
    (assessment : rawModel.BehavioralAssessment)
    (equilibrium : assessment.IsSequentialEquilibrium
      (rawMenu.decisionInformationAntichain initial horizon scheduler)
      canonicalCertificate rawPayoff)
    (seed : Seeds) (supportedSeed : seed ∈ nativeSeedLaw.support)
    (remaining : Nat) (frame : app.Execution)
    (trace : (countedMenu.protocol initial horizon (family seed)).Trace
      (some ⟨remaining, none, frame⟩))
    (position : frame.environmentRecall.length = 5)
    (helper : initialPublicPackets frame ≠ ∅)
    (players : Player → app.Policy)
    (covered : ∀ who past view action, action ∈ (players who past view).support →
      action ∈ countedMenu.actions who past view)
    (selected : ∀ owner, players owner = countedMenu.decodeProfile initial horizon scheduler
      (countedAssessmentProfile assessment) owner)
    (final : app.Execution)
    (reached : final ∈ (app.runRounds (family seed) players remaining frame).support) :
    ∀ owner, PhaseService.BindingAccepted runtime leaks (originalCoordinate owner) owner final := by
  have resolved := frame_finish_original_resolved seed remaining frame trace players covered final
    reached
  intro owner
  obtain ⟨first, word, firstRequest, zero⟩ :=
    frame_five_initial_record seed remaining frame trace position owner
  cases bit : seed.2 owner with
  | true =>
      exact foreign_singleton_good_original_admission assessment equilibrium seed supportedSeed
        remaining frame trace owner (by rw [word]; rfl) bit players covered (selected owner)
        final reached resolved
  | false =>
      exact foreign_singleton_bad_helper_original_admission assessment equilibrium seed
        supportedSeed remaining frame trace owner bit (by omega) (by omega) first word
        firstRequest zero helper players covered (selected owner) final reached (resolved owner)

/-- A focal owner's retained initial transmission guarantees its own admission
under arbitrary covered future play; all other assessed owners then admit too. -/
theorem frame_focal_early_original_admissions
    (assessment : rawModel.BehavioralAssessment)
    (equilibrium : assessment.IsSequentialEquilibrium
      (rawMenu.decisionInformationAntichain initial horizon scheduler)
      canonicalCertificate rawPayoff)
    (seed : Seeds) (supportedSeed : seed ∈ nativeSeedLaw.support)
    (remaining : Nat) (frame : app.Execution)
    (trace : (countedMenu.protocol initial horizon (family seed)).Trace
      (some ⟨remaining, none, frame⟩))
    (position : frame.environmentRecall.length = 5)
    (focal : Player)
    (early : ∃ entry ∈ frame.recall focal, entry.action.transmission ≠ none)
    (players : Player → app.Policy)
    (covered : ∀ who past view action, action ∈ (players who past view).support →
      action ∈ countedMenu.actions who past view)
    (selected : ∀ owner, owner ≠ focal →
      players owner = countedMenu.decodeProfile initial horizon scheduler
        (countedAssessmentProfile assessment) owner)
    (final : app.Execution)
    (reached : final ∈ (app.runRounds (family seed) players remaining frame).support) :
    ∀ owner, PhaseService.BindingAccepted runtime leaks (originalCoordinate owner) owner final := by
  classical
  obtain ⟨focalFirst, focalWord, focalRequest, focalZero⟩ :=
    frame_five_initial_record seed remaining frame trace position focal
  obtain ⟨entry, member, nonsilent⟩ := early
  rw [focalWord, List.mem_singleton] at member
  subst entry
  obtain ⟨material, sent⟩ := Option.ne_none_iff_exists'.mp nonsilent
  have helper := initial_record_transmission_packets_nonempty seed remaining frame trace focal
    focalFirst (by rw [focalWord]; exact List.mem_singleton_self _) focalRequest focalZero
    material sent (by omega)
  have resolved := frame_finish_original_resolved seed remaining frame trace players covered final
    reached
  intro owner
  by_cases same : owner = focal
  · subst owner
    obtain ⟨finalTrace⟩ := countedMenu.trace_runRounds initial horizon (family seed) players covered
      0 remaining frame final (by simpa only [Nat.zero_add] using trace) reached
    have retained := rounds_recall_retained (family seed) players remaining frame final reached
      focal
    have recorded : focalFirst ∈ final.recall focal := retained.subset (by
      rw [focalWord]; exact List.mem_singleton_self _)
    apply (original_binding_accepted_iff_clocks seed _ finalTrace focal (resolved focal)).mpr
    exact Or.inl (original_recorded_transmission_clock seed 0 final finalTrace focal focalFirst
      recorded focalRequest material sent 0 focalZero)
  · obtain ⟨first, word, firstRequest, zero⟩ :=
      frame_five_initial_record seed remaining frame trace position owner
    cases bit : seed.2 owner with
    | true =>
        exact foreign_singleton_good_original_admission assessment equilibrium seed supportedSeed
          remaining frame trace owner (by rw [word]; rfl) bit players covered (selected owner same)
          final reached resolved
    | false =>
        exact foreign_singleton_bad_helper_original_admission assessment equilibrium seed
          supportedSeed remaining frame trace owner bit (by omega) (by omega) first word
          firstRequest zero helper players covered (selected owner same) final reached
          (resolved owner)

end Vegas.Examples.CommitSeedBroadcast
