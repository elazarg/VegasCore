/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedSignallingPublicationWait

/-! # Exact WAIT value on the complete native information fiber -/

noncomputable section

namespace Vegas.Examples.CommitSeedSignalling

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Protocol.InformationModel
  GameTheory.Math.Probability GameTheory.Enforcement
open OnePacketCommitRevealHypotheses (Player alice bob setup program)

theorem raw_information_control_of_counted_view (source : countedProtocol.History)
    (remaining : Nat) (execution : app.Execution) (owner : Player)
    (current : source.state = some ⟨remaining, some owner, execution⟩)
    (target : rawModel.InformationHistory owner (countedModel.infoOf owner source.trace)) :
    ∃ count next, target.1.state = some (⟨count, some owner, next⟩ : app.Control) ∧
      next.recall owner = execution.recall owner ∧
      next.observe app owner = execution.observe app owner := by
  have sourceInfo : countedModel.infoOf owner source.trace =
      some (execution.recall owner, execution.observe app owner) := by
    change (countedMenu.signals initial horizon scheduler).infoOf owner source.trace = _
    rw [countedMenu.info, current]
    simp only [ReactiveApplication.observe, ite_true]
  have observed := (rawMenu.info initial horizon scheduler owner target.1.trace).symm.trans
    (target.2.trans sourceInfo)
  cases state : target.1.state with
  | none => simp only [ReactiveApplication.observe, state] at observed; cases observed
  | some control =>
      rcases control with ⟨count, acting, next⟩
      by_cases active : acting = some owner
      · subst acting
        simp only [ReactiveApplication.observe, state, ite_true] at observed
        have pair := Option.some.inj observed
        exact ⟨count, next, rfl, congrArg Prod.fst pair, congrArg Prod.snd pair⟩
      · simp only [ReactiveApplication.observe, state, active, ite_false] at observed
        cases observed

private theorem wait_value_on_same_information
    (assessment : rawModel.BehavioralAssessment)
    (equilibrium : assessment.IsSequentialEquilibrium
      (rawMenu.decisionInformationAntichain initial horizon scheduler)
      canonicalCertificate rawPayoff)
    (source : countedProtocol.History) (remaining : Nat) (execution : app.Execution)
    (owner : Player) (current : source.state = some ⟨remaining, some owner, execution⟩)
    (retired : execution.application.attempt ≠ originalAttempt)
    (request : execution.application.SeedRequest owner
      ⟨execution.application.attempt, revealEvent owner⟩)
    (target : rawModel.InformationHistory owner (countedModel.infoOf owner source.trace)) :
    ∃ count next, target.1.state = some (⟨count, some owner, next⟩ : app.Control) ∧
      expect (app.finish initial horizon scheduler
        (rawMenu.decodeProfile initial horizon scheduler assessment.strategy)
        (some ⟨count, none, next.respond app owner ⟨none⟩⟩))
        (fun state => netPayoff state owner) = -1 := by
  classical
  obtain ⟨count, next, state, recalled, view⟩ :=
    raw_information_control_of_counted_view source remaining execution owner current target
  have sourceTrace : countedProtocol.Trace (some ⟨remaining, some owner, execution⟩) :=
    current ▸ source.trace
  have targetTrace : rawProtocol.Trace (some ⟨count, some owner, next⟩) :=
    state ▸ target.1.trace
  have sourceRaw := countedMenu.toRawTrace initial horizon scheduler sourceTrace
  have targetRaw := rawMenu.toRawTrace initial horizon scheduler targetTrace
  have sourceValid := raw_native_valid scheduler ⟨remaining, some owner, execution⟩ sourceRaw
  have targetValid := raw_native_valid scheduler ⟨count, some owner, next⟩ targetRaw
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
  have attempt : next.application.attempt = execution.application.attempt :=
    congrArg (fun observed : app.PlayerView => observed.application.2.attempt) view
  have sourcePublic := (execution.application.requests_publicView sourceValid owner
    ⟨execution.application.attempt, revealEvent owner⟩).mpr request
  have targetPublic : PhaseRuntimeState.requests next.application.publicView owner
      ⟨next.application.attempt, revealEvent owner⟩ := by
    change PhaseRuntimeState.requests (next.observe app owner).application.2 owner
      ⟨next.application.attempt, revealEvent owner⟩
    rw [attempt, view]
    exact sourcePublic
  have requested := (next.application.requests_publicView targetValid owner
    ⟨next.application.attempt, revealEvent owner⟩).mp targetPublic
  have oldUnsubmitted := counted_tail_callback_unsubmitted remaining execution owner sourceTrace
    ⟨execution.application.attempt, revealEvent owner⟩ retired request
  have unsubmitted (message : Message Player (CommitAttemptPacket graph))
      (member : message ∈ next.network.inputs) (sender : message.sender = owner) :
      PhaseCount.event? message.payload ≠
        some ⟨next.application.attempt, revealEvent owner⟩ := by
    have output : message ∈ app.outputs (next.recall owner) := by
      rw [← targetRecall.1 owner]
      exact List.mem_filter.mpr ⟨member, decide_eq_true_eq.mpr sender⟩
    rw [recalled, ← sourceClean.1.1 owner] at output
    have original := (List.mem_filter.mp output).1
    rw [attempt]
    exact oldUnsubmitted message original sender
  refine ⟨count, next, state, ?_⟩
  exact raw_publication_wait_assessed_value assessment equilibrium count next owner targetTrace
    clean (by rw [attempt]; exact retired) requested unsubmitted

open Classical in
/-- The current WAIT's payoff is minus one at every raw history of the full
native information fiber. A counted representative supplies only the common
own input; the foreign past and the assessment's belief remain unrestricted. -/
theorem raw_publication_wait_fiber_committed_value
    (assessment : rawModel.BehavioralAssessment)
    (equilibrium : assessment.IsSequentialEquilibrium
      (rawMenu.decisionInformationAntichain initial horizon scheduler)
      canonicalCertificate rawPayoff)
    (source : countedProtocol.History) (remaining : Nat) (execution : app.Execution)
    (owner : Player) (current : source.state = some ⟨remaining, some owner, execution⟩)
    (retired : execution.application.attempt ≠ originalAttempt)
    (request : execution.application.SeedRequest owner
      ⟨execution.application.attempt, revealEvent owner⟩)
    (site : rawModel.InformationSite owner)
    (atSite : site.1 = countedModel.infoOf owner source.trace)
    (choice : rawModel.Choice owner site.1) (selected : choice.1 = some ⟨none⟩)
    (target : rawModel.InformationHistory owner site.1) :
    expect (rawModel.runBehavioralTerminalFrom canonicalCertificate
      (Profile.update (sig := rawModel.behavioralSignature) assessment.strategy owner
        ((assessment.strategy owner).commit site.1 choice)) target.1) (rawPayoff owner) = -1 := by
  classical
  let retained : rawModel.InformationHistory owner (countedModel.infoOf owner source.trace) :=
    ⟨target.1, target.2.trans atSite⟩
  obtain ⟨count, next, state, value⟩ := wait_value_on_same_information assessment equilibrium source
    remaining execution owner current retired request retained
  have bound := app.trace_bound initial horizon scheduler
    (rawMenu.toRawTrace initial horizon scheduler target.1.trace)
  have projection := rawMenu.run_local_law_finish_of_information initial horizon scheduler
    assessment.strategy target.1 owner count next state site.1 target.2 (PMF.pure choice)
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
        (some ⟨count, none, next.respond app owner ⟨none⟩⟩) := by
    rw [rawModel.runBehavioralTerminalFrom_eq_runBehavioralFrom_of_bounded canonicalCertificate
      (rawMenu.bounded initial horizon scheduler)]
    exact projection
  have expected := congrArg (fun law : PMF app.ProtocolState =>
    expect law (fun state => netPayoff state owner)) terminalProjection
  rw [expect_map] at expected
  exact expected.trans value

open Classical in
/-- The assessment's actual belief can be integrated directly: the fixed WAIT
choice has exactly minus-one conditional value, even at a zero-probability site. -/
theorem raw_publication_wait_context_value
    (assessment : rawModel.BehavioralAssessment)
    (equilibrium : assessment.IsSequentialEquilibrium
      (rawMenu.decisionInformationAntichain initial horizon scheduler)
      canonicalCertificate rawPayoff)
    (source : countedProtocol.History) (remaining : Nat) (execution : app.Execution)
    (owner : Player) (current : source.state = some ⟨remaining, some owner, execution⟩)
    (retired : execution.application.attempt ≠ originalAttempt)
    (request : execution.application.SeedRequest owner
      ⟨execution.application.attempt, revealEvent owner⟩)
    (site : rawModel.InformationSite owner)
    (atSite : site.1 = countedModel.infoOf owner source.trace)
    (choice : rawModel.Choice owner site.1) (selected : choice.1 = some ⟨none⟩) :
    (assessment.continuationContext canonicalCertificate site (rawPayoff owner)).value
      ((assessment.strategy owner).commit site.1 choice) = -1 := by
  classical
  have integrable := assessment.continuationContext_integrable_of_bounded_terminal
    canonicalCertificate site (rawPayoff owner) 6 (fun final _ => rawPayoff_abs_le owner final)
      ((assessment.strategy owner).commit site.1 choice)
  change (assessment.continuationContextWith
    (rawModel.runBehavioralTerminalFrom canonicalCertificate) site (rawPayoff owner)).value
      ((assessment.strategy owner).commit site.1 choice) = -1
  rw [assessment.continuationContextWith_value_tower
    (rawModel.runBehavioralTerminalFrom canonicalCertificate) site (rawPayoff owner)
      ((assessment.strategy owner).commit site.1 choice) integrable,
    ← expect_constant (assessment.belief owner site) (-1 : ℝ)]
  apply expect_congr_on_support
  intro target _
  exact raw_publication_wait_fiber_committed_value assessment equilibrium source remaining
    execution owner current retired request site atSite choice selected target

end Vegas.Examples.CommitSeedSignalling
