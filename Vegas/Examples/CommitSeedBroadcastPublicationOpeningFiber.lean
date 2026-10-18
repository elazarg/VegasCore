/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedBroadcastPublicationOpeningValue
import Vegas.Examples.CommitSeedBroadcastPublicationInformation
import Vegas.Examples.CommitSeedBroadcastPublicationWaitFiber

/-! # Strict truthful-opening incentives on the complete raw information fiber -/

noncomputable section

namespace Vegas.Examples.CommitSeedBroadcast

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Protocol.InformationModel
  GameTheory.Math.Probability

open Classical in
/-- The same current truthful opening has nonnegative actual terminal value
at every compatible raw history, with the original assessed foreign tail. -/
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
  let retained : rawModel.InformationHistory owner (countedModel.infoOf owner source.trace) :=
    ⟨target.1, target.2.trans atSite⟩
  obtain ⟨count, next, state, ⟨trace⟩, recalled, observed⟩ :=
    counted_information_raw_fiber_control source remaining execution owner current retained
  change target.1.state = some (⟨count, some owner, next⟩ : app.Control) at state
  have sourceTrace : countedProtocol.Trace (some ⟨remaining, some owner, execution⟩) :=
    current ▸ source.trace
  have sourceValid := raw_native_valid scheduler ⟨remaining, some owner, execution⟩
    (countedMenu.toRawTrace initial horizon scheduler sourceTrace)
  have nextValid := raw_native_valid scheduler ⟨count, some owner, next⟩
    (countedMenu.toRawTrace initial horizon scheduler trace)
  have attempt : next.application.attempt = execution.application.attempt :=
    congrArg (fun view : app.PlayerView => view.application.2.attempt) observed
  have publicSource := (execution.application.requests_publicView sourceValid owner
    ⟨execution.application.attempt, revealEvent owner⟩).mpr request
  have publicNext : PhaseRuntimeState.requests next.application.publicView owner
      ⟨next.application.attempt, revealEvent owner⟩ := by
    change PhaseRuntimeState.requests (next.observe app owner).application.2 owner _
    rw [attempt, observed]
    exact publicSource
  have requestNext := (next.application.requests_publicView nextValid owner
    ⟨next.application.attempt, revealEvent owner⟩).mp publicNext
  have retiredNext : next.application.attempt ≠ originalAttempt := by rwa [attempt]
  have allowedNext : PhaseCount.phaseOpeningResponse runtime leaks (revealEvent owner) candidate
      ⟨.bool, value⟩ ∈ countedMenu.actions owner (next.recall owner)
        (next.observe app owner) := by simpa only [recalled, observed] using allowed
  have views : next.application.current.native.playerView owner =
      execution.application.current.native.playerView owner :=
    congrArg (fun view : app.PlayerView => view.application.1) observed
  have storedNext := (binding_store_eq_of_owner_view next.application.current.native
    execution.application.current.native owner views).trans stored
  have timelyNext := counted_tail_request_timely count next owner trace
    ⟨next.application.attempt, revealEvent owner⟩ retiredNext requestNext
  obtain ⟨seed, ⟨fixed⟩⟩ := menu_trace_fixed_seed countedMenu
    (PhaseCount.silence_onePacket runtime leaks bounds) ⟨count, some owner, next⟩ trace
  have enough := family_requested_remaining seed ⟨count, some owner, next⟩
    (countedMenu.toRawTrace initial horizon (family seed) fixed)
      ⟨next.application.attempt, revealEvent owner⟩ owner requestNext
  change 20 < count at enough
  cases count with
  | zero => omega
  | succ count =>
    rw [raw_committed_current_value_eq_finish assessment.strategy target.1 owner (count + 1)
      next state site.1 target.2 choice _ selected]
    exact counted_tail_opening_assessed_value_nonnegative assessment equilibrium count next owner
      trace retiredNext candidate value allowedNext requestNext timelyNext storedNext

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
      (rawPayoff owner) (9 / 2) (fun final _ => rawPayoff_abs_le owner final) policy
  apply assessment.not_supported_choice_of_uniform_gap
    (rawModel.runBehavioralTerminalFrom canonicalCertificate) site factor (rawPayoff owner)
    (equilibrium.1 owner site) (integrable (assessment.strategy owner)) choice
    ((assessment.strategy owner).commit site.1 alternative)
    (integrable ((assessment.strategy owner).commit site.1 alternative)) (-(3 / 2)) 0 (by norm_num)
  · intro target
    exact le_of_eq (raw_publication_wait_fiber_committed_value assessment equilibrium source
      remaining execution owner current retired request site atSite choice selected target)
  · intro target
    exact raw_publication_opening_fiber_committed_value_nonnegative assessment equilibrium source
      remaining execution owner current retired candidate value allowed request stored
        site atSite alternative rfl target

end Vegas.Examples.CommitSeedBroadcast
