/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedBroadcastProperRetryExclusion
import Vegas.Examples.CommitSeedBroadcastProperPublicationExclusion
import Vegas.Examples.CommitSeedBroadcastPrivateCalendar
import Vegas.Examples.CommitSeedBroadcastInitializedTrace
import Vegas.Examples.CommitSeedBroadcastRealization
import Interaction.ReactiveInvariantPrefix

/-! # Proper original binding acceptance protects the entire actual execution -/

noncomputable section

namespace Vegas.Examples.CommitSeedBroadcast

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable (clock : Nat)

private theorem scheduled_proper_passive_step_survives (seed : Seeds)
    (remaining : Nat) (execution : app.Execution)
    (prior : (countedMenu.protocol initial horizon (family seed)).Trace
      (some ⟨remaining, none, execution⟩))
    (afterRemaining : Nat) (after : app.Execution)
    (joint : Player → Option app.Action)
    (legal : (countedMenu.protocol initial horizon (family seed)).Legal
      (some ⟨remaining, none, execution⟩) joint)
    (moved : some (⟨afterRemaining, none, after⟩ : app.Control) ∈
      (app.transition initial horizon (family seed)
        (some ⟨remaining, none, execution⟩) joint).support)
    (final : app.Control)
    (trace : (countedMenu.protocol initial horizon (family seed)).Trace (some final))
    (kept : TracePrefix (prior.extend joint legal moved) trace)
    (owner : Player)
    (consistent : (scheduledProperPolicy clock owner).Consistent (final.execution.recall owner))
    (accepted : PhaseService.BindingAccepted runtime leaks (originalCoordinate owner) owner
      final.execution)
    (active : owner ∉ execution.application.current.excluded) :
    owner ∉ after.application.current.excluded := by
  classical
  let nextTrace := prior.extend joint legal moved
  let raw := countedMenu.toRawTrace initial horizon (family seed) prior
  have nextPrefix : TracePrefix prior nextTrace := by
    change TracePrefix prior (prior.extend joint legal moved)
    exact @TracePrefix.extend Player (countedMenu.protocol initial horizon (family seed))
      _ prior _ _ prior .refl joint legal moved
  have retained := app.reaches_recall_prefix initial horizon (family seed)
    (countedMenu.reaches_raw initial horizon (family seed) kept.reachesWithin)
      ⟨afterRemaining, none, after⟩ final rfl rfl owner
  obtain ⟨later, recallEq⟩ := retained
  have afterConsistent : (scheduledProperPolicy clock owner).Consistent (after.recall owner) := by
    apply ReactiveApplication.Policy.Consistent.of_append (after := later)
    rwa [recallEq]
  have compiledRaw := raw
  rw [initial_eq_compiled] at compiledRaw
  have suffix := phasePlanSuffix_history runtime leaks plan (setup.initialLaw.map encodeInputs)
    horizon (family seed) compiledRaw
  cases phases : execution.application.phases with
  | nil =>
      have positioned := (raw_phase_geometry (family seed) ⟨remaining, none, execution⟩
        raw).1.positioned
      rw [phases] at positioned
      change execution.application.current.native.config.cut.IsPrefix graph.order.eventCount
        at positioned
      have finished := (finished_owner_invariant owner).tracePrefix countedMenu initial horizon
        (family seed) ⟨remaining, none, execution⟩ ⟨afterRemaining, none, after⟩ prior nextTrace
          nextPrefix
          ⟨by rw [phases]; exact List.nil_suffix,
            fun event _ => (positioned.2 event).mpr event.isLt, active⟩
      exact finished.2.2
  | cons phase rest =>
      have member : phase ∈ plan.phases :=
        suffix.subset (by rw [phases]; exact List.mem_cons_self)
      rw [plan_phases] at member
      rcases List.mem_cons.mp member with commitment | publication
      · subst phase
        have installed : execution.application.phases.head? = some commitmentPhase := by
          rw [phases]
          rfl
        by_cases original : execution.application.attempt = originalAttempt
        · intro excluded
          have rawKept := (countedMenu.reaches_raw initial horizon (family seed)
            kept.reachesWithin).tracePrefix
          change TracePrefix (raw.extend joint
            (countedMenu.legal_raw initial horizon (family seed) legal) moved)
              (countedMenu.toRawTrace initial horizon (family seed) trace) at rawKept
          have transportPrefix (law : PMF app.State) (equal : initial = law) :
              TracePrefix
                ((equal ▸ raw).extend joint
                  (countedMenu.legal_raw initial horizon (family seed) legal) moved)
                (equal ▸ (countedMenu.toRawTrace initial horizon (family seed) trace)) := by
            subst law
            exact rawKept
          have compiledKept := transportPrefix _ initial_eq_compiled
          obtain ⟨event, _inside, request, missing⟩ :=
            PhaseService.not_bindingAccepted_after_commitment_exclusion runtime leaks plan
              (setup.initialLaw.map encodeInputs) horizon (family seed)
              ⟨remaining, none, execution⟩ ⟨afterRemaining, none, after⟩ final
                (initial_eq_compiled ▸ raw) joint
                (countedMenu.legal_raw initial horizon (family seed) legal) moved
                (initial_eq_compiled ▸
                  countedMenu.toRawTrace initial horizon (family seed) trace) compiledKept
                commitmentPhase (Option.mem_def.mpr installed) rfl owner active excluded
          have coordinate := original_request_coordinate seed ⟨remaining, none, execution⟩ raw
            ⟨execution.application.attempt, event⟩ owner original request
          rw [coordinate] at missing
          exact missing accepted
        · intro excluded
          exact scheduled_proper_retry_exclusion_impossible clock seed remaining execution
            prior afterRemaining
            after nextTrace nextPrefix joint moved owner afterConsistent
              original installed active excluded
      · have same : phase = publicationPhase := List.mem_singleton.mp publication
        subst phase
        have installed : execution.application.phases.head? = some publicationPhase := by
          rw [phases]
          rfl
        intro excluded
        exact scheduled_proper_publication_exclusion_impossible clock seed remaining execution prior
          afterRemaining after nextTrace nextPrefix joint moved owner
            afterConsistent installed active excluded

/-- Once the original binding actually lands, a fixed proper late owner survives
every later retry and publication along the same counted history. Its original
receipt need not already exist at an earlier prefix under consideration. -/
theorem scheduled_proper_original_binding_survives (seed : Seeds) (final : app.Control)
    (trace : (countedMenu.protocol initial horizon (family seed)).Trace (some final))
    (owner : Player)
    (consistent : (scheduledProperPolicy clock owner).Consistent (final.execution.recall owner))
    (accepted : PhaseService.BindingAccepted runtime leaks (originalCoordinate owner) owner
      final.execution) : owner ∉ final.execution.application.current.excluded := by
  have everyPrefix {state : app.ProtocolState}
      (past : (countedMenu.protocol initial horizon (family seed)).Trace state) :
      TracePrefix past trace → ReactiveApplication.stateInvariant
        (fun state : app.State => owner ∉ state.current.excluded) state := by
    refine Trace.rec (motive := fun state past => TracePrefix past trace →
      ReactiveApplication.stateInvariant
        (fun state : app.State => owner ∉ state.current.excluded) state) ?_ ?_ past
    · intro _; trivial
    · intro source target prior joint legal moved ih kept
      have preceding := (TracePrefix.extend .refl joint legal moved).trans kept
      have active := ih preceding
      change target ∈ (app.transition initial horizon (family seed) source joint).support at moved
      cases source with
      | none =>
          obtain ⟨physical, supported, rfl⟩ := PMF.support_map .. ▸ moved
          rw [initial, PMF.mem_support_pure_iff] at supported
          subst physical
          change owner ∉ initialState.current.excluded
          rw [initialState_eq]
          exact Finset.notMem_empty owner
      | some before =>
          obtain ⟨after, sameTarget, _recall⟩ := app.transition_recall_prefix initial horizon
            (family seed) before target joint moved
          subst target
          change owner ∉ after.execution.application.current.excluded
          rcases before with ⟨remaining, actor, execution⟩
          cases actor with
          | some who =>
              cases Option.some.inj ((PMF.mem_support_pure_iff _ _).mp moved)
              rcases action : (joint who).getD ⟨none⟩ with ⟨transmission⟩
              cases transmission <;> exact active
          | none =>
              cases remaining with
              | zero =>
                  cases Option.some.inj ((PMF.mem_support_pure_iff _ _).mp moved)
                  exact active
              | succ remaining =>
                  have actualMove := moved
                  obtain ⟨command, _selected, stepped⟩ :=
                    Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ moved)
                  obtain ⟨next, environment, equal⟩ := PMF.support_map .. ▸ stepped
                  cases Option.some.inj equal
                  cases command with
                  | wait =>
                      simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map]
                        at environment
                      cases (PMF.mem_support_pure_iff _ _).mp environment
                      exact active
                  | activate who =>
                      obtain ⟨observed, observedSupport, exactNext⟩ :=
                        PMF.support_map .. ▸ environment
                      obtain ⟨view, _chosen, exactObserved⟩ :=
                        PMF.support_map .. ▸ observedSupport
                      cases exactObserved
                      cases exactNext
                      exact active
                  | «include» identifier =>
                      exact scheduled_proper_passive_step_survives clock seed (remaining + 1)
                        execution
                        prior remaining next joint legal actualMove final trace kept owner
                          consistent accepted active
                  | application operation =>
                      exact scheduled_proper_passive_step_survives clock seed (remaining + 1)
                        execution
                        prior remaining next joint legal actualMove final trace kept owner
                          consistent accepted active
  exact everyPrefix trace .refl

/-- The installed scheduler's initialized law uses one original seed mixture.
Successful original binding delivery protects a proper owner on every supported
physical outcome against arbitrary counted opposing policies. -/
theorem initialized_scheduled_proper_original_binding_survives
    (profile : ∀ who, countedModel.BehavioralPolicy who) (owner : Player)
    (selected : countedMenu.decodeProfile initial horizon scheduler profile owner =
      scheduledProperPolicy clock owner)
    (final : app.Execution)
    (reached : final ∈ (app.runRounds scheduler
      (countedMenu.decodeProfile initial horizon scheduler profile) horizon
        initialExecution).support)
    (accepted : PhaseService.BindingAccepted runtime leaks (originalCoordinate owner) owner
      final) : owner ∉ final.application.current.excluded := by
  let players := countedMenu.decodeProfile initial horizon scheduler profile
  have realized := original_realize players horizon initialState
  change nativeSeedLaw.bind
      (fun seed => app.runRounds (family seed) players horizon initialExecution) =
    app.runRounds scheduler players horizon initialExecution at realized
  change final ∈ (app.runRounds scheduler players horizon initialExecution).support at reached
  rw [← realized, PMF.support_bind] at reached
  obtain ⟨seed, _supported, familyReached⟩ := Set.mem_iUnion₂.mp reached
  obtain ⟨trace⟩ := counted_profile_trace profile seed horizon le_rfl final familyReached
  have trace : (countedMenu.protocol initial horizon (family seed)).Trace
      (some ⟨0, none, final⟩) := by
    simpa only [Nat.sub_self] using trace
  have consistency := (app.consistentRecall_policyInvariant players).runRounds (family seed)
    horizon initialExecution final (fun _ => .nil) familyReached
  have ownConsistent := consistency owner
  change (countedMenu.decodeProfile initial horizon scheduler profile owner).Consistent
    (final.recall owner) at ownConsistent
  rw [selected] at ownConsistent
  exact scheduled_proper_original_binding_survives clock seed ⟨0, none, final⟩ trace owner
    ownConsistent accepted

end Vegas.Examples.CommitSeedBroadcast
