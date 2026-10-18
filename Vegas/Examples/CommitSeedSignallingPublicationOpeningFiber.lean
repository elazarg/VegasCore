/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedSignallingOpeningTransfer
import Vegas.Examples.CommitSeedSignallingPublicationWaitFiber
import Vegas.Examples.CommitSeedSignallingBudget

/-! # Strict opening incentives on the complete native information fiber -/

noncomputable section

namespace Vegas.Examples.CommitSeedSignalling

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Protocol.InformationModel
  GameTheory.Math.Probability GameTheory.Enforcement
open OnePacketCommitRevealHypotheses (Player alice bob setup program)

private theorem opening_value_on_same_information
    (assessment : rawModel.BehavioralAssessment)
    (equilibrium : assessment.IsSequentialEquilibrium
      (rawMenu.decisionInformationAntichain initial horizon scheduler)
      canonicalCertificate rawPayoff)
    (source : countedProtocol.History) (remaining : Nat) (execution : app.Execution)
    (owner : Player) (current : source.state = some ⟨remaining, some owner, execution⟩)
    (retired : execution.application.attempt ≠ originalAttempt)
    (candidate : Handle graph) (value : Bool)
    (allowed : PhaseCount.phaseOpeningResponse runtime leaks (revealEvent owner) candidate
      ⟨.bool, value⟩ ∈ countedMenu.actions owner (execution.recall owner)
        (execution.observe app owner))
    (request : execution.application.SeedRequest owner
      ⟨execution.application.attempt, revealEvent owner⟩)
    (timely : execution.application.current.native.WithinDeadline runtime (revealEvent owner))
    (stored : execution.application.current.native.config.store (.inr (bindingEvent owner)) =
      some (cast (congrArg EventField.Value (bindingEvent_layout owner).symm)
        (PublicationResult.success value)))
    (target : rawModel.InformationHistory owner (countedModel.infoOf owner source.trace)) :
    ∃ count next, target.1.state = some (⟨count + 1, some owner, next⟩ : app.Control) ∧
      0 ≤ expect (app.finish initial horizon scheduler
        (rawMenu.decodeProfile initial horizon scheduler assessment.strategy)
        (some ⟨count + 1, none, next.respond app owner
          (PhaseCount.phaseOpeningResponse runtime leaks (revealEvent owner) candidate
            ⟨.bool, value⟩)⟩)) (fun state => netPayoff state owner) := by
  classical
  obtain ⟨count, next, state, recalled, observed⟩ :=
    raw_information_control_of_counted_view source remaining execution owner current target
  have sourceTrace : countedProtocol.Trace (some ⟨remaining, some owner, execution⟩) :=
    current ▸ source.trace
  have targetTrace : rawProtocol.Trace (some ⟨count, some owner, next⟩) := state ▸ target.1.trace
  have targetRaw := rawMenu.toRawTrace initial horizon scheduler targetTrace
  have sourceValid := raw_native_valid scheduler ⟨remaining, some owner, execution⟩
    (countedMenu.toRawTrace initial horizon scheduler sourceTrace)
  have targetValid := raw_native_valid scheduler ⟨count, some owner, next⟩ targetRaw
  have attempt : next.application.attempt = execution.application.attempt :=
    congrArg (fun view : app.PlayerView => view.application.2.attempt) observed
  have publicRequest := (execution.application.requests_publicView sourceValid owner
    ⟨execution.application.attempt, revealEvent owner⟩).mpr request
  have publicHere : PhaseRuntimeState.requests next.application.publicView owner
      ⟨next.application.attempt, revealEvent owner⟩ := by
    change PhaseRuntimeState.requests (next.observe app owner).application.2 owner _
    rw [attempt, observed]
    exact publicRequest
  have requested := (next.application.requests_publicView targetValid owner
    ⟨next.application.attempt, revealEvent owner⟩).mp publicHere
  obtain ⟨seed, ⟨fixed⟩⟩ := fixed_seed_decision ⟨count, some owner, next⟩ targetRaw
  have enough := family_requested_remaining seed ⟨count, some owner, next⟩ fixed _ owner requested
  change 9 < count at enough
  have sourceClean := (PhaseCount.onePacketMenu_countClean runtime leaks bounds scheduler).history
    initial horizon (fun state _ => PhaseCount.countClean_initial runtime leaks state) source.trace
  rw [current] at sourceClean
  have sourceOwn : OwnPermitted owner execution :=
    ⟨sourceClean.1, fun message member _ => sourceClean.2 message member⟩
  have targetRecall := PhaseCount.countRecall_history runtime leaks targetRaw
  have clean : OwnPermitted owner next :=
    (ownPermitted_iff_past owner next targetRecall).mpr (by
      rw [recalled]
      exact (ownPermitted_iff_past owner execution sourceOwn.1).mp sourceOwn)
  cases count with
  | zero => omega
  | succ count =>
      refine ⟨count, next, state, ?_⟩
      exact raw_tail_opening_value_on_same_input assessment equilibrium
        ⟨remaining, some owner, execution⟩ sourceTrace count next owner targetTrace clean rfl
          recalled observed retired candidate value allowed request timely stored

open Classical in
/-- The truthful opening's actual committed terminal value is nonnegative at
every compatible raw history, including histories with charged foreign traffic. -/
theorem raw_publication_opening_fiber_committed_value_nonnegative
    (assessment : rawModel.BehavioralAssessment)
    (equilibrium : assessment.IsSequentialEquilibrium
      (rawMenu.decisionInformationAntichain initial horizon scheduler)
      canonicalCertificate rawPayoff)
    (source : countedProtocol.History) (remaining : Nat) (execution : app.Execution)
    (owner : Player) (current : source.state = some ⟨remaining, some owner, execution⟩)
    (retired : execution.application.attempt ≠ originalAttempt)
    (candidate : Handle graph) (value : Bool)
    (allowed : PhaseCount.phaseOpeningResponse runtime leaks (revealEvent owner) candidate
      ⟨.bool, value⟩ ∈ countedMenu.actions owner (execution.recall owner)
        (execution.observe app owner))
    (request : execution.application.SeedRequest owner
      ⟨execution.application.attempt, revealEvent owner⟩)
    (timely : execution.application.current.native.WithinDeadline runtime (revealEvent owner))
    (stored : execution.application.current.native.config.store (.inr (bindingEvent owner)) =
      some (cast (congrArg EventField.Value (bindingEvent_layout owner).symm)
        (PublicationResult.success value)))
    (site : rawModel.InformationSite owner)
    (atSite : site.1 = countedModel.infoOf owner source.trace)
    (choice : rawModel.Choice owner site.1)
    (selected : choice.1 = some
      (PhaseCount.phaseOpeningResponse runtime leaks (revealEvent owner) candidate ⟨.bool, value⟩))
    (target : rawModel.InformationHistory owner site.1) :
    0 ≤ expect (rawModel.runBehavioralTerminalFrom canonicalCertificate
      (Profile.update (sig := rawModel.behavioralSignature) assessment.strategy owner
        ((assessment.strategy owner).commit site.1 choice)) target.1) (rawPayoff owner) := by
  classical
  let retained : rawModel.InformationHistory owner (countedModel.infoOf owner source.trace) :=
    ⟨target.1, target.2.trans atSite⟩
  obtain ⟨count, next, state, valueBound⟩ := opening_value_on_same_information assessment
    equilibrium source remaining execution owner current retired candidate value allowed request
      timely stored retained
  have bound := app.trace_bound initial horizon scheduler
    (rawMenu.toRawTrace initial horizon scheduler target.1.trace)
  have projection := rawMenu.run_local_law_finish_of_information initial horizon scheduler
    assessment.strategy target.1 owner (count + 1) next state site.1 target.2 (PMF.pure choice)
      (2 * horizon) ((Nat.le_add_left _ _).trans bound)
  change (rawModel.runBehavioralFrom
    (Profile.update (sig := rawModel.behavioralSignature) assessment.strategy owner
      ((assessment.strategy owner).commit site.1 choice)) (2 * horizon + 1) target.1).map
        History.state = _ at projection
  rw [PMF.pure_map, selected, Option.getD_some, PMF.pure_bind] at projection
  have terminalProjection : (rawModel.runBehavioralTerminalFrom canonicalCertificate
      (Profile.update (sig := rawModel.behavioralSignature) assessment.strategy owner
        ((assessment.strategy owner).commit site.1 choice)) target.1).map History.state =
      app.finish initial horizon scheduler
        (rawMenu.decodeProfile initial horizon scheduler assessment.strategy)
        (some ⟨count + 1, none, next.respond app owner
          (PhaseCount.phaseOpeningResponse runtime leaks (revealEvent owner) candidate
            ⟨.bool, value⟩)⟩) := by
    rw [rawModel.runBehavioralTerminalFrom_eq_runBehavioralFrom_of_bounded canonicalCertificate
      (rawMenu.bounded initial horizon scheduler)]
    exact projection
  have expected := congrArg (fun law : PMF app.ProtocolState =>
    expect law (fun state => netPayoff state owner)) terminalProjection
  rw [expect_map] at expected
  exact expected.symm ▸ valueBound

open Classical in
/-- Strict current-opening dominance excludes WAIT under the original
assessment's full native belief. No proper future strategy is prescribed. -/
theorem raw_publication_wait_not_supported
    (assessment : rawModel.BehavioralAssessment)
    (equilibrium : assessment.IsSequentialEquilibrium
      (rawMenu.decisionInformationAntichain initial horizon scheduler)
      canonicalCertificate rawPayoff)
    (source : countedProtocol.History) (remaining : Nat) (execution : app.Execution)
    (owner : Player) (current : source.state = some ⟨remaining, some owner, execution⟩)
    (retired : execution.application.attempt ≠ originalAttempt)
    (candidate : Handle graph) (value : Bool)
    (allowed : PhaseCount.phaseOpeningResponse runtime leaks (revealEvent owner) candidate
      ⟨.bool, value⟩ ∈ countedMenu.actions owner (execution.recall owner)
        (execution.observe app owner))
    (request : execution.application.SeedRequest owner
      ⟨execution.application.attempt, revealEvent owner⟩)
    (timely : execution.application.current.native.WithinDeadline runtime (revealEvent owner))
    (stored : execution.application.current.native.config.store (.inr (bindingEvent owner)) =
      some (cast (congrArg EventField.Value (bindingEvent_layout owner).symm)
        (PublicationResult.success value)))
    (site : rawModel.InformationSite owner)
    (atSite : site.1 = countedModel.infoOf owner source.trace)
    (choice : rawModel.Choice owner site.1) (selected : choice.1 = some ⟨none⟩) :
    choice ∉ (assessment.strategy owner site.1).support := by
  classical
  let opening := PhaseCount.phaseOpeningResponse runtime leaks (revealEvent owner) candidate
    ⟨.bool, value⟩
  have sourceInfo : site.1 = some (execution.recall owner, execution.observe app owner) := by
    rw [atSite]
    change (countedMenu.signals initial horizon scheduler).infoOf owner source.trace = _
    rw [countedMenu.info, current]
    simp only [ReactiveApplication.observe, ite_true]
  have rawAllowed : opening ∈ rawMenu.actions owner (execution.recall owner)
      (execution.observe app owner) :=
    ((PhaseCount.mem_onePacketActions runtime leaks bounds owner _ _ _).mp allowed).1
  have available : some opening ∈ rawModel.menu owner site.1 := by
    rw [sourceInfo]
    exact ⟨opening, rawAllowed, rfl⟩
  let alternative : rawModel.Choice owner site.1 := ⟨some opening, available⟩
  have factor := rawModel.runnerFactorsAt_terminal canonicalCertificate
    (rawMenu.decisionRecall initial horizon scheduler).actsOnceWhereItMatters
    (rawMenu.informationSite_allNonterminal initial horizon scheduler owner site)
  have integrable (policy : rawModel.BehavioralPolicy owner) :=
    assessment.continuationContext_integrable_of_bounded_terminal canonicalCertificate site
      (rawPayoff owner) 6 (fun final _ => rawPayoff_abs_le owner final) policy
  apply assessment.not_supported_choice_of_uniform_gap
    (rawModel.runBehavioralTerminalFrom canonicalCertificate) site factor (rawPayoff owner)
    (equilibrium.1 owner site) (integrable (assessment.strategy owner)) choice
    ((assessment.strategy owner).commit site.1 alternative)
    (integrable ((assessment.strategy owner).commit site.1 alternative)) (-1) 0 (by norm_num)
  · intro target
    exact le_of_eq (raw_publication_wait_fiber_committed_value assessment equilibrium source
      remaining execution owner current retired request site atSite choice selected target)
  · intro target
    exact raw_publication_opening_fiber_committed_value_nonnegative assessment equilibrium source
      remaining execution owner current retired candidate value allowed request timely stored
        site atSite alternative rfl target

end Vegas.Examples.CommitSeedSignalling
