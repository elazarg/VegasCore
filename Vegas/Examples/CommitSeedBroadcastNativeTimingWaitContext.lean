/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedBroadcastNativeTimingWaitLaw
import Vegas.Examples.CommitSeedBroadcastCountedContinuation
import Vegas.Examples.CommitSeedBroadcastCountedInformation
import Vegas.Examples.CommitSeedBroadcastFirstLateSeedBelief
import Interaction.ReactiveLocalContinuation

/-! # Actual first-late WAIT values on complete native information fibers -/

noncomputable section

namespace Vegas.Examples.CommitSeedBroadcast

open SourceProgram EventGraphRuntime Interaction GameTheory GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Protocol.InformationModel
  GameTheory.Math.Probability

/-- At a concrete first-late control, all supported original posterior seeds
have the same bad-service mark, determined by the complete physical history. -/
theorem counted_first_late_original_bad_value
    (remaining : Nat) (execution : app.Execution) (owner : Player)
    (trace : countedProtocol.Trace (some ⟨remaining, some owner, execution⟩))
    (request : execution.application.SeedRequest owner (originalCoordinate owner))
    (clock : execution.application.current.native.clock = 2) :
    expect (implementation.posterior execution.environmentRecall)
      (fun seed => if seed.2 owner = false then (1 : ℝ) else 0) =
        firstLateBadValue (some ⟨remaining, some owner, execution⟩) := by
  rw [← expect_constant (implementation.posterior execution.environmentRecall)
    (firstLateBadValue (some ⟨remaining, some owner, execution⟩))]
  apply expect_congr_on_support
  intro seed supported
  obtain ⟨_original, ⟨fixed⟩⟩ := menu_original_posterior_trace countedMenu
    ⟨remaining, some owner, execution⟩ trace seed supported
  have bad := original_first_late_bad_iff seed ⟨remaining, some owner, execution⟩
    (countedMenu.toRawTrace initial horizon (family seed) fixed) owner rfl request.1.symm clock
  change (if seed.2 owner = false then (1 : ℝ) else 0) =
    if 12 ≤ execution.environmentRecall.length then 1 else 0
  simp only [bad]

/-- A forced current WAIT followed by any count-permitted future has the exact
physical-history upper bound. The original posterior is averaged jointly. -/
theorem counted_first_late_wait_finish_value_upper
    (remaining : Nat) (execution : app.Execution) (owner : Player)
    (trace : countedProtocol.Trace (some ⟨remaining, some owner, execution⟩))
    (request : execution.application.SeedRequest owner (originalCoordinate owner))
    (clock : execution.application.current.native.clock = 2)
    (first : app.PlayerEntry) (recorded : first ∈ execution.recall owner)
    (firstRequest : PhaseRuntimeState.requests first.beforeView.application.2 owner
      (originalCoordinate owner))
    (silent : first.action.transmission = none)
    (zero : first.beforeView.application.2.native.clock = 0)
    (players : Player → app.Policy)
    (covered : ∀ who past view action, action ∈ (players who past view).support →
      action ∈ countedMenu.actions who past view) :
    expect (app.finish initial horizon scheduler players
      (some ⟨remaining, none, execution.respond app owner ⟨none⟩⟩))
      (fun state => netPayoff state owner) ≤
        (5 / 2 : ℝ) * firstLateBadValue (some ⟨remaining, some owner, execution⟩) - 3 / 2 := by
  let last : app.PlayerEntry := ⟨execution.observe app owner, ⟨none⟩, none⟩
  have valid := raw_native_valid scheduler ⟨remaining, some owner, execution⟩
    (countedMenu.toRawTrace initial horizon scheduler trace)
  have publicRequest := (execution.application.requests_publicView valid owner
    (originalCoordinate owner)).mpr request
  obtain ⟨afterTrace⟩ := countedMenu.trace_respond initial horizon scheduler remaining execution
    owner ⟨none⟩ trace (PhaseCount.silence_onePacket runtime leaks bounds owner _ _)
  have lastMember : last ∈ (execution.respond app owner ⟨none⟩).recall owner := by
    simp only [ReactiveApplication.Execution.respond, ite_true, List.mem_append,
      List.mem_singleton]
    exact Or.inr rfl
  have bound := counted_waits_finish_value_upper remaining (execution.respond app owner ⟨none⟩)
    afterTrace owner first last (app.respond_recall_mono execution owner owner ⟨none⟩ recorded)
      lastMember firstRequest publicRequest silent rfl zero clock players covered
  rw [app.respond_environmentRecall] at bound
  rw [counted_first_late_original_bad_value remaining execution owner trace request clock] at bound
  exact bound

open Classical in
/-- The full original raw information fiber has the same WAIT upper bound
under the unchanged assessed continuation. Foreign hidden past actions are
unrestricted; complete physical input equality supplies counted representatives. -/
theorem raw_first_late_wait_context_value_upper
    (assessment : rawModel.BehavioralAssessment)
    (equilibrium : assessment.IsSequentialEquilibrium
      (rawMenu.decisionInformationAntichain initial horizon scheduler)
      canonicalCertificate rawPayoff)
    (source : countedProtocol.History) (remaining : Nat) (execution : app.Execution)
    (owner : Player) (current : source.state = some ⟨remaining, some owner, execution⟩)
    (request : execution.application.SeedRequest owner (originalCoordinate owner))
    (clock : execution.application.current.native.clock = 2)
    (first : app.PlayerEntry) (recorded : first ∈ execution.recall owner)
    (firstRequest : PhaseRuntimeState.requests first.beforeView.application.2 owner
      (originalCoordinate owner))
    (silent : first.action.transmission = none)
    (zero : first.beforeView.application.2.native.clock = 0)
    (site : rawModel.InformationSite owner)
    (atSite : site.1 = countedModel.infoOf owner source.trace)
    (choice : rawModel.Choice owner site.1) (selected : choice.1 = some ⟨none⟩) :
    (assessment.continuationContext canonicalCertificate site (rawPayoff owner)).value
      ((assessment.strategy owner).commit site.1 choice) ≤
        (5 / 2 : ℝ) * expect (assessment.belief owner site)
          (fun history => firstLateBadValue history.1.state) - 3 / 2 := by
  have sourceTrace : countedProtocol.Trace (some ⟨remaining, some owner, execution⟩) :=
    current ▸ source.trace
  have fiber (target : rawModel.InformationHistory owner site.1) :
      expect (rawModel.runBehavioralTerminalFrom canonicalCertificate
        (Profile.update (sig := rawModel.behavioralSignature) assessment.strategy owner
          ((assessment.strategy owner).commit site.1 choice)) target.1) (rawPayoff owner) ≤
        (5 / 2 : ℝ) * firstLateBadValue target.1.state - 3 / 2 := by
    let retained : rawModel.InformationHistory owner (countedModel.infoOf owner source.trace) :=
      ⟨target.1, target.2.trans atSite⟩
    obtain ⟨count, next, state, ⟨countedTrace⟩, recalled, observed⟩ :=
      counted_information_raw_fiber_control source remaining execution owner current retained
    change target.1.state = some (⟨count, some owner, next⟩ : app.Control) at state
    have rawTrace : rawProtocol.Trace (some ⟨count, some owner, next⟩) := state ▸ target.1.trace
    have sourceValid := raw_native_valid scheduler ⟨remaining, some owner, execution⟩
      (countedMenu.toRawTrace initial horizon scheduler sourceTrace)
    have publicSource := (execution.application.requests_publicView sourceValid owner
      (originalCoordinate owner)).mpr request
    have publicNext : PhaseRuntimeState.requests next.application.publicView owner
        (originalCoordinate owner) := by
      change PhaseRuntimeState.requests (next.observe app owner).application.2 owner _
      rw [observed]
      exact publicSource
    have nextValid := raw_native_valid scheduler ⟨count, some owner, next⟩
      (rawMenu.toRawTrace initial horizon scheduler rawTrace)
    have requestNext := (next.application.requests_publicView nextValid owner
      (originalCoordinate owner)).mp publicNext
    have clockNext : next.application.current.native.clock = 2 := by
      change (next.observe app owner).application.2.native.clock = 2
      rw [observed]
      exact clock
    let players := countedMenu.decodeProfile initial horizon scheduler
      (countedAssessmentProfile assessment)
    have bound := counted_first_late_wait_finish_value_upper count next owner countedTrace
      requestNext clockNext first (recalled.symm ▸ recorded) firstRequest silent zero players
        (fun who past view action supported => countedMenu.decode_embedPolicy_covered
          initial horizon scheduler who (countedAssessmentProfile assessment who)
            past view action supported)
    obtain ⟨responded⟩ := countedMenu.trace_respond initial horizon scheduler count next owner
      ⟨none⟩ countedTrace (PhaseCount.silence_onePacket runtime leaks bounds owner _ _)
    let after : countedProtocol.History :=
      ⟨some ⟨count, none, next.respond app owner ⟨none⟩⟩, responded⟩
    have physical := counted_assessment_finish_eq assessment equilibrium after
    change app.finish initial horizon scheduler players after.state = _ at physical
    change expect (app.finish initial horizon scheduler players after.state)
      (fun state => netPayoff state owner) ≤ _ at bound
    rw [physical] at bound
    have raw := rawMenu.toRawTrace initial horizon scheduler rawTrace
    have enough : app.rank horizon target.1.state ≤ 2 * horizon + 1 := by
      rw [state]
      exact (Nat.le_add_left _ _).trans (app.trace_bound initial horizon scheduler raw)
    have projection := rawMenu.run_local_law_finish_of_information initial horizon scheduler
      assessment.strategy target.1 owner count next state site.1 target.2 (PMF.pure choice)
        (2 * horizon) enough
    change (rawModel.runBehavioralFrom
      (Profile.update (sig := rawModel.behavioralSignature) assessment.strategy owner
        ((assessment.strategy owner).commit site.1 choice)) (2 * horizon + 1)
          target.1).map History.state = _ at projection
    rw [PMF.pure_map, selected, Option.getD_some, PMF.pure_bind] at projection
    have terminalProjection : (rawModel.runBehavioralTerminalFrom canonicalCertificate
        (Profile.update (sig := rawModel.behavioralSignature) assessment.strategy owner
          ((assessment.strategy owner).commit site.1 choice)) target.1).map History.state =
        app.finish initial horizon scheduler
          (rawMenu.decodeProfile initial horizon scheduler assessment.strategy)
            after.state := by
      rw [rawModel.runBehavioralTerminalFrom_eq_runBehavioralFrom_of_bounded
        canonicalCertificate (rawMenu.bounded initial horizon scheduler)]
      exact projection
    have expected := congrArg (fun law : PMF app.ProtocolState =>
      expect law (fun state => netPayoff state owner)) terminalProjection
    rw [expect_map] at expected
    change expect _ (rawPayoff owner) = _ at expected
    exact expected.le.trans (by simpa only [state] using bound)
  have integrable := assessment.continuationContext_integrable_of_bounded_terminal
    canonicalCertificate site (rawPayoff owner) (9 / 2)
      (fun final _ => rawPayoff_abs_le owner final)
        ((assessment.strategy owner).commit site.1 choice)
  change (assessment.continuationContextWith
    (rawModel.runBehavioralTerminalFrom canonicalCertificate) site (rawPayoff owner)).value
      ((assessment.strategy owner).commit site.1 choice) ≤ _
  rw [assessment.continuationContextWith_value_tower
    (rawModel.runBehavioralTerminalFrom canonicalCertificate) site (rawPayoff owner)
      ((assessment.strategy owner).commit site.1 choice) integrable]
  have comparison := expect_mono (μ := assessment.belief owner site)
    (fun target _ => fiber target) (payoffIntegrable_of_finite _ _)
      (payoffIntegrable_of_finite _ _)
  rw [expect_sub (payoffIntegrable_of_finite _ _) (payoffIntegrable_of_finite _ _),
    expect_const_mul, expect_constant] at comparison
  exact comparison

end Vegas.Examples.CommitSeedBroadcast
