/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedBroadcastRegularAdmission
import Vegas.Examples.CommitSeedBroadcastRegularBelief

/-! # Regular first-late prefixes admit every original binding -/

noncomputable section

namespace Vegas.Examples.CommitSeedBroadcast

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

private theorem regular_after_response (seed : Seeds) (remaining : Nat)
    (execution : app.Execution) (focal : Player)
    (trace : (countedMenu.protocol initial horizon (family seed)).Trace
      (some ⟨remaining, some focal, execution⟩))
    (original : execution.application.attempt = originalAttempt)
    (clock : execution.application.current.native.clock = 2) (empty : execution.receipts = [])
    (regular : regularFirstLateControl seed (some ⟨remaining, some focal, execution⟩))
    (action : app.Action) (emits : action.transmission ≠ none) :
    RegularResponsePrefix (execution.respond app focal action) ∧
      ((execution.respond app focal action).recall focal).length = 2 := by
  classical
  obtain ⟨first, word, _view, _request, _zero⟩ := original_first_late_initial_record seed remaining
    execution focal (countedInRaw.trace initial horizon (family seed) trace) original clock empty
  have two : ((execution.respond app focal action).recall focal).length = 2 := by
    rw [app.respond_recall_length, word]
    simp only [List.length_cons, List.length_nil, ite_true]
  refine ⟨?_, two⟩
  intro who
  by_cases same : who = focal
  · subst who
    right
    refine ⟨two, ?_⟩
    obtain ⟨emitted, recalled⟩ := app.respond_recall_entry execution focal action
    rw [recalled, List.getLast?_append_of_ne_nil _ (by simp), List.getLast?_singleton]
    change some action ≠ some ⟨none⟩
    intro equal
    have equalAction := Option.some.inj equal
    exact emits (congrArg ReactiveApplication.Action.transmission equalAction)
  · rw [app.respond_recall_other execution focal who same action]
    rcases original_first_late_recall_length seed remaining execution focal
        (countedInRaw.trace initial horizon (family seed) trace) original clock empty who with
      short | two
    · exact Or.inl short
    · right
      refine ⟨two, ?_⟩
      rcases regular.2 who with short | nonsilent
      · change (execution.recall who).length = 1 at short
        omega
      · exact nonsilent

/-- Any current permitted transmission at an all-good regular clock-two
prefix obtains every original owner's receipt under the unchanged assessed
foreign strategies and an arbitrary covered focal continuation. No assumption
on the transmitted or hidden preparations is made. -/
theorem regular_assessed_original_admission
    (assessment : rawModel.BehavioralAssessment)
    (equilibrium : assessment.IsSequentialEquilibrium
      (rawMenu.decisionInformationAntichain initial horizon scheduler)
      canonicalCertificate rawPayoff)
    (seed : Seeds) (supportedSeed : seed ∈ nativeSeedLaw.support)
    (remaining : Nat) (execution : app.Execution) (focal : Player)
    (trace : (countedMenu.protocol initial horizon (family seed)).Trace
      (some ⟨remaining, some focal, execution⟩))
    (request : execution.application.SeedRequest focal (originalCoordinate focal))
    (clock : execution.application.current.native.clock = 2) (empty : execution.receipts = [])
    (regular : regularFirstLateControl seed (some ⟨remaining, some focal, execution⟩))
    (action : app.Action)
    (offered : action ∈ countedMenu.actions focal (execution.recall focal)
      (execution.observe app focal))
    (emits : action.transmission ≠ none)
    (tail : app.Policy)
    (tailCovered : ∀ past view response, response ∈ (tail past view).support →
      response ∈ countedMenu.actions focal past view)
    (final : app.Execution)
    (reached : final ∈ (app.runRounds (family seed)
      (Function.update
        (countedMenu.decodeProfile initial horizon scheduler (countedAssessmentProfile assessment))
          focal tail) remaining (execution.respond app focal action)).support)
    (resolved : ∀ who, (originalCoordinate who).Resolved final.application) :
    ∀ who, PhaseService.BindingAccepted runtime leaks (originalCoordinate who) who final := by
  classical
  let anchor := execution.respond app focal action
  let players := Function.update
    (countedMenu.decodeProfile initial horizon scheduler (countedAssessmentProfile assessment))
      focal tail
  have covered : ∀ who past view response, response ∈ (players who past view).support →
      response ∈ countedMenu.actions who past view := by
    intro who past view response selected
    by_cases same : who = focal
    · subst who
      exact tailCovered past view response (by simpa only [players, Function.update_self] using
        selected)
    · have baseline : response ∈
          (countedMenu.decodeProfile initial horizon scheduler (countedAssessmentProfile assessment)
            who past view).support := by
        simpa only [players, Function.update_of_ne same] using selected
      change response ∈ (app.decodePolicy (countedMenu.embedPolicy initial horizon scheduler who
        (countedAssessmentProfile assessment who)) past view).support at baseline
      exact countedMenu.decode_embedPolicy_covered initial horizon scheduler who
        (countedAssessmentProfile assessment who) past view response baseline
  obtain ⟨anchorTrace⟩ := countedMenu.trace_respond initial horizon (family seed) remaining
    execution focal action trace offered
  have foreign : ∀ who, who ≠ focal → players who =
      countedMenu.decodeProfile initial horizon scheduler (countedAssessmentProfile assessment)
        who := by
    intro who different
    exact Function.update_of_ne different _ _
  obtain ⟨regularAnchor, long⟩ := regular_after_response seed remaining execution focal trace
    request.1.symm clock empty regular action emits
  let replay := app.anchoredPolicy anchor players
  have sameFuture : app.runRounds (family seed) replay remaining anchor =
      app.runRounds (family seed) players remaining anchor :=
    app.runRounds_anchoredPolicy (family seed) anchor players remaining
  have replayReached : final ∈ (app.runRounds (family seed) replay remaining anchor).support := by
    rw [sameFuture]
    exact reached
  have consistent := (app.consistentRecall_policyInvariant replay).runRounds (family seed)
    remaining anchor final (app.anchoredPolicy_consistent anchor players) replayReached
  have retained : ∀ who, anchor.recall who <+: final.recall who :=
    rounds_recall_retained (family seed) replay remaining anchor final replayReached
  have transmits := regular_anchored_record_transmits assessment equilibrium seed supportedSeed
    anchor focal long regularAnchor players foreign final retained consistent
  have replayCovered : ∀ who past view response, response ∈ (replay who past view).support →
      response ∈ countedMenu.actions who past view := by
    intro who
    exact countedMenu.anchoredPolicy_covered initial horizon (family seed)
      ⟨remaining, none, anchor⟩ anchorTrace players who (covered who)
  obtain ⟨enough, anchorReached⟩ := app.mem_roundsFrom_anchoredPolicy_of_trace initial horizon
    (family seed) players (countedMenu.toRawTrace initial horizon (family seed) anchorTrace)
  have initializedAnchor : anchor ∈ (app.runRounds (family seed) replay
      (horizon - remaining) initialExecution).support := by
    simpa only [ReactiveApplication.roundsFrom, initial, PMF.pure_bind, initialExecution]
      using anchorReached
  have initializedFinal : final ∈
      (app.runRounds (family seed) replay horizon initialExecution).support := by
    have split : horizon = (horizon - remaining) + remaining := by omega
    rw [split, app.runRounds_add, PMF.support_bind]
    exact Set.mem_iUnion₂.mpr ⟨anchor, initializedAnchor, replayReached⟩
  exact allGood_original_admission seed regular.1 replay replayCovered final transmits
    initializedFinal resolved

end Vegas.Examples.CommitSeedBroadcast
