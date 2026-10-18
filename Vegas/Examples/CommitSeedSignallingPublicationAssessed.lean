/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedSignallingPublicationProper
import Vegas.Examples.CommitSeedSignallingPublicationContinuation

/-! # Incumbent survival from authentic successful publication entries -/

noncomputable section

namespace Vegas.Examples.CommitSeedSignalling

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Protocol.InformationModel
  GameTheory.Math.Probability GameTheory.Enforcement
open OnePacketCommitRevealHypotheses (Player alice bob setup program)

/-- A retained incumbent publication response protects its owner along the
literal original trace. Sequential rationality supplies its nonsilent response
at the full raw information fiber; the real next include supplies survival. -/
theorem anchored_assessed_recorded_publication_survives
    (assessment : rawModel.BehavioralAssessment)
    (equilibrium : assessment.IsSequentialEquilibrium
      (rawMenu.decisionInformationAntichain initial horizon scheduler)
      canonicalCertificate rawPayoff)
    (source : app.Control) (sourceTrace : countedProtocol.Trace (some source))
    (tail : source.execution.application.phases <:+ [publicationPhase])
    (owner : Player) (value : Bool)
    (stored : source.execution.application.current.native.config.store (.inr (bindingEvent owner)) =
      some (cast (congrArg EventField.Value (bindingEvent_layout owner).symm)
        (PublicationResult.success value)))
    (unserved : ∀ entry ∈ source.execution.recall owner,
      ∀ coordinate : CommitAttemptEvent graph, coordinate.event = revealEvent owner →
        ¬ PhaseRuntimeState.requests entry.beforeView.application.2 owner coordinate)
    (final : app.Control) (trace : countedProtocol.Trace (some final))
    (sourceKept : TracePrefix sourceTrace trace)
    (consistent : (app.anchoredPolicy source.execution
      (rawMenu.decodeProfile initial horizon scheduler assessment.strategy) owner).Consistent
        (final.execution.recall owner))
    (coordinate : CommitAttemptEvent graph) (publication : coordinate.event = revealEvent owner)
    (entry : app.PlayerEntry) (recorded : entry ∈ final.execution.recall owner)
    (requested : PhaseRuntimeState.requests entry.beforeView.application.2 owner coordinate) :
    owner ∉ final.execution.application.current.excluded := by
  obtain ⟨remaining, execution, prior, postTrace, postKept, allowed, request,
    currentStored, retired, chosen⟩ :=
    anchored_recorded_publication_data scheduler source sourceTrace tail owner value stored
      unserved (rawMenu.decodeProfile initial horizon scheduler assessment.strategy)
        final trace sourceKept consistent coordinate publication entry recorded requested
  have nonsilent := counted_successful_publication_response_nonsilent assessment equilibrium
    remaining execution owner prior retired request value currentStored entry.action chosen
  have timely := counted_tail_request_timely remaining execution owner prior
    ⟨execution.application.attempt, revealEvent owner⟩ retired request
  cases entry with
  | mk entryView action emitted =>
      cases action with
      | mk transmission =>
          cases transmission with
          | none => exact (nonsilent rfl).elim
          | some material =>
              have scheduled := tail_submission_scheduler remaining execution owner material
                (countedMenu.toRawTrace initial horizon scheduler prior) retired
              exact publication_after_submission_survives scheduler remaining execution owner
                prior request value currentStored material allowed timely scheduled postTrace
                  final trace postKept

/-- The shared first-exclusion induction applies to the actual assessed raw
responses, including off-path counted information histories. No proper future
policy or assumed current-response survival is imposed. -/
theorem anchored_assessed_publication_trace_survives
    (assessment : rawModel.BehavioralAssessment)
    (equilibrium : assessment.IsSequentialEquilibrium
      (rawMenu.decisionInformationAntichain initial horizon scheduler)
      canonicalCertificate rawPayoff)
    (source : app.Control) (sourceTrace : countedProtocol.Trace (some source))
    (tail : source.execution.application.phases <:+ [publicationPhase])
    (owner : Player) (value : Bool)
    (stored : source.execution.application.current.native.config.store (.inr (bindingEvent owner)) =
      some (cast (congrArg EventField.Value (bindingEvent_layout owner).symm)
        (PublicationResult.success value)))
    (unserved : ∀ entry ∈ source.execution.recall owner,
      ∀ coordinate : CommitAttemptEvent graph, coordinate.event = revealEvent owner →
        ¬ PhaseRuntimeState.requests entry.beforeView.application.2 owner coordinate)
    (active : owner ∉ source.execution.application.current.excluded)
    (final : app.Control) (trace : countedProtocol.Trace (some final))
    (kept : TracePrefix sourceTrace trace)
    (consistent : (app.anchoredPolicy source.execution
      (rawMenu.decodeProfile initial horizon scheduler assessment.strategy) owner).Consistent
        (final.execution.recall owner)) :
    owner ∉ final.execution.application.current.excluded := by
  apply publication_trace_survives scheduler source sourceTrace tail owner value stored active
    final trace kept
  · intro remaining execution prior coordinate request positive
    obtain ⟨seed, ⟨fixed⟩⟩ := menu_trace_fixed_seed countedMenu
      (PhaseCount.silence_onePacket runtime leaks bounds) _ prior
    exact positive_age_own_request seed remaining execution fixed coordinate owner request positive
  · intro coordinate publication entry recorded requested
    exact anchored_assessed_recorded_publication_survives assessment equilibrium source sourceTrace
      tail owner value stored unserved final trace kept consistent coordinate publication entry
        recorded requested

/-- The unchanged assessed physical continuation from a genuine fresh
publication entry preserves its successful owner. The actual raw strategy is
restricted only through its derived clean-site extension, and the original
mixed scheduler and the complete old own word are retained. -/
theorem assessed_publication_run_survives
    (assessment : rawModel.BehavioralAssessment)
    (equilibrium : assessment.IsSequentialEquilibrium
      (rawMenu.decisionInformationAntichain initial horizon scheduler)
      canonicalCertificate rawPayoff)
    (remaining : Nat) (execution : app.Execution)
    (sourceTrace : countedProtocol.Trace (some ⟨remaining, none, execution⟩))
    (tail : execution.application.phases <:+ [publicationPhase])
    (owner : Player) (value : Bool)
    (stored : execution.application.current.native.config.store (.inr (bindingEvent owner)) =
      some (cast (congrArg EventField.Value (bindingEvent_layout owner).symm)
        (PublicationResult.success value)))
    (unserved : ∀ entry ∈ execution.recall owner,
      ∀ coordinate : CommitAttemptEvent graph, coordinate.event = revealEvent owner →
        ¬ PhaseRuntimeState.requests entry.beforeView.application.2 owner coordinate)
    (active : owner ∉ execution.application.current.excluded)
    (final : app.Execution)
    (reached : final ∈ (app.runRounds scheduler
      (rawMenu.decodeProfile initial horizon scheduler assessment.strategy)
        remaining execution).support) :
    owner ∉ final.application.current.excluded := by
  let source : app.Control := ⟨remaining, none, execution⟩
  let players := rawMenu.decodeProfile initial horizon scheduler assessment.strategy
  let anchored := app.anchoredPolicy execution players
  have anchoredReached : final ∈
      (app.runRounds scheduler anchored remaining execution).support := by
    simpa only [anchored, app.runRounds_anchoredPolicy] using reached
  have consistency := (app.consistentRecall_policyInvariant anchored).runRounds scheduler
    remaining execution final (fun who => app.anchoredPolicy_consistent execution players who)
      anchoredReached
  let history : countedProtocol.History := ⟨some source, sourceTrace⟩
  let fuel := app.rank horizon history.state
  have historyLaw := (countedInRaw.actionRestriction initial horizon scheduler).runFrom_law
    (countedAssessmentProfile assessment) assessment.strategy
      (raw_equilibrium_extends_counted assessment equilibrium) fuel history
  have stateLaw := congrArg (fun law => law.map ExecutionProtocol.History.state) historyLaw
  rw [PMF.map_comp] at stateLaw
  change (countedModel.runBehavioralFrom (countedAssessmentProfile assessment) fuel history).map
      ExecutionProtocol.History.state =
    (rawModel.runBehavioralFrom assessment.strategy fuel
      (countedInRaw.history initial horizon scheduler history)).map
        ExecutionProtocol.History.state at stateLaw
  rw [rawMenu.run_eq_finish initial horizon scheduler assessment.strategy fuel _ le_rfl]
    at stateLaw
  change (countedModel.runBehavioralFrom (countedAssessmentProfile assessment) fuel history).map
      ExecutionProtocol.History.state =
    app.finish initial horizon scheduler players (some source) at stateLaw
  have physical : some (⟨0, none, final⟩ : app.Control) ∈
      (app.finish initial horizon scheduler players (some source)).support := by
    simp only [ReactiveApplication.finish, source, ReactiveApplication.resume, PMF.pure_bind]
    exact (PMF.mem_support_map_iff _ _ _).mpr ⟨final, reached, rfl⟩
  rw [← stateLaw, PMF.support_map] at physical
  obtain ⟨ending, supported, stateEq⟩ := physical
  have path := countedModel.runBehavioralFrom_reachesWithin
    (countedAssessmentProfile assessment) fuel history ending supported
  rcases ending with ⟨endingState, endingTrace⟩
  change endingState = some (⟨0, none, final⟩ : app.Control) at stateEq
  subst endingState
  have kept : TracePrefix sourceTrace endingTrace := path.tracePrefix
  exact anchored_assessed_publication_trace_survives assessment equilibrium source sourceTrace
    tail owner value stored unserved active ⟨0, none, final⟩ endingTrace kept (consistency owner)

end Vegas.Examples.CommitSeedSignalling
