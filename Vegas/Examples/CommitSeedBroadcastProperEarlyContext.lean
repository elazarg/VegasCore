/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedBroadcastProperEarlyValue
import Vegas.Examples.CommitSeedBroadcastProperTimingContext

/-! # Nonnegative proper initial continuation on the full raw information fiber -/

noncomputable section

namespace Vegas.Examples.CommitSeedBroadcast

open SourceProgram EventGraphRuntime Interaction GameTheory GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Protocol.InformationModel
  GameTheory.Math.Probability

open Classical in
/-- A proper initial packet has nonnegative continuation value on the
whole raw information fiber, with the actual assessment and unchanged
opponents. This includes initial inputs of zero equilibrium reach. -/
theorem raw_proper_early_context_value_nonnegative
    (assessment : rawModel.BehavioralAssessment)
    (equilibrium : assessment.IsSequentialEquilibrium
      (rawMenu.decisionInformationAntichain initial horizon scheduler)
      canonicalCertificate rawPayoff)
    (source : countedProtocol.History) (remaining : Nat) (execution : app.Execution)
    (owner : Player) (current : source.state = some ⟨remaining, some owner, execution⟩)
    (request : execution.application.SeedRequest owner (originalCoordinate owner))
    (clock : execution.application.current.native.clock = 0)
    (word : execution.recall owner = [])
    (site : rawModel.InformationSite owner)
    (atSite : site.1 = countedModel.infoOf owner source.trace) :
    0 ≤
      (assessment.continuationContext canonicalCertificate site (rawPayoff owner)).value
        (scheduledProperContinuation 0 owner) := by
  have sourceTrace : countedProtocol.Trace (some ⟨remaining, some owner, execution⟩) :=
    current ▸ source.trace
  let policy := scheduledProperPolicy 0 owner
  let profile := Function.update (countedAssessmentProfile assessment) owner
    (countedMenu.restrictPolicy initial horizon scheduler owner policy)
  let players := countedMenu.decodeProfile initial horizon scheduler profile
  have covered (who : Player) (past : List app.PlayerEntry) (view : app.PlayerView)
      (action : app.Action) (chosen : action ∈ (players who past view).support) :
      action ∈ countedMenu.actions who past view :=
    countedMenu.decode_embedPolicy_covered initial horizon scheduler who (profile who)
      past view action chosen
  have selected : players owner = scheduledProperPolicy 0 owner := by
    change app.decodePolicy (countedMenu.embedPolicy initial horizon scheduler owner
      ((Function.update (countedAssessmentProfile assessment) owner
        (countedMenu.restrictPolicy initial horizon scheduler owner policy)) owner)) = _
    rw [Function.update_self]
    exact countedMenu.decode_restrictPolicy_of_covered initial horizon scheduler owner policy
      (scheduledProperPolicy_counted 0 owner)
  have fiber (target : rawModel.InformationHistory owner site.1) :
      0 ≤
        expect (rawModel.runBehavioralTerminalFrom canonicalCertificate
          (Profile.update (sig := rawModel.behavioralSignature) assessment.strategy owner
            (scheduledProperContinuation 0 owner)) target.1) (rawPayoff owner) := by
    let sameInput : rawModel.InformationHistory owner (countedModel.infoOf owner source.trace) :=
      ⟨target.1, target.2.trans atSite⟩
    obtain ⟨count, next, state, ⟨countedTrace⟩, recalled, observed⟩ :=
      counted_information_raw_fiber_control source remaining execution owner current sameInput
    have rawTrace : rawProtocol.Trace (some ⟨count, some owner, next⟩) :=
      state ▸ target.1.trace
    have valid := raw_native_valid scheduler ⟨remaining, some owner, execution⟩
      (countedMenu.toRawTrace initial horizon scheduler sourceTrace)
    have publicSource := (execution.application.requests_publicView valid owner
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
    have clockNext : next.application.current.native.clock = 0 := by
      change (next.observe app owner).application.2.native.clock = 0
      rw [observed]
      exact clock
    have wordNext : next.recall owner = [] := recalled.trans word
    have bound := counted_proper_early_finish_value_nonnegative count next owner countedTrace
      requestNext clockNext wordNext players selected covered
    let retained : countedProtocol.History := ⟨some ⟨count, some owner, next⟩, countedTrace⟩
    have physical := countedInRaw.runFrom_restrictPolicy_finish initial horizon scheduler
      (countedAssessmentProfile assessment) assessment.strategy
        (raw_equilibrium_extends_counted assessment equilibrium) owner policy
        (scheduledProperPolicy_counted 0 owner) (app.rank horizon retained.state) retained le_rfl
    rw [countedMenu.run_eq_finish initial horizon scheduler profile
      (app.rank horizon retained.state) retained le_rfl] at physical
    have nativeLaw := raw_terminal_state_law
      (Profile.update (sig := rawModel.behavioralSignature) assessment.strategy owner
        (scheduledProperContinuation 0 owner)) target.1
    rw [rawMenu.decodeProfile_update, decode_scheduledProperContinuation] at nativeLaw
    rw [state] at nativeLaw
    have expected := congrArg (fun law : PMF app.ProtocolState =>
      expect law (fun state => netPayoff state owner)) nativeLaw
    rw [expect_map] at expected
    change expect (rawModel.runBehavioralTerminalFrom canonicalCertificate
      (Profile.update (sig := rawModel.behavioralSignature) assessment.strategy owner
        (scheduledProperContinuation 0 owner)) target.1) (rawPayoff owner) = _ at expected
    rw [expected, ← physical]
    exact bound
  have integrable := assessment.continuationContext_integrable_of_bounded_terminal
    canonicalCertificate site (rawPayoff owner) (9 / 2)
      (fun final _ => rawPayoff_abs_le owner final) (scheduledProperContinuation 0 owner)
  change _ ≤ (assessment.continuationContextWith
    (rawModel.runBehavioralTerminalFrom canonicalCertificate) site (rawPayoff owner)).value
      (scheduledProperContinuation 0 owner)
  rw [assessment.continuationContextWith_value_tower
    (rawModel.runBehavioralTerminalFrom canonicalCertificate) site (rawPayoff owner)
      (scheduledProperContinuation 0 owner) integrable]
  apply expect_nonneg
  intro target _supported
  exact fiber target

end Vegas.Examples.CommitSeedBroadcast
