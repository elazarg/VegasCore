/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedBroadcastClockThreeContext
import Vegas.Examples.CommitSeedBroadcastClockThreeWaitValue

/-! # Exact final original WAIT loss on the full raw information fiber -/

noncomputable section

namespace Vegas.Examples.CommitSeedBroadcast

open SourceProgram EventGraphRuntime Interaction GameTheory GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Protocol.InformationModel
  GameTheory.Math.Probability

open Classical in
/-- Every compatible raw history gives the same final-omission loss under
the incumbent continuation, after its literal earlier two WAIT records. -/
theorem raw_clock_three_wait_fiber_value
    (assessment : rawModel.BehavioralAssessment)
    (equilibrium : assessment.IsSequentialEquilibrium
      (rawMenu.decisionInformationAntichain initial horizon scheduler)
      canonicalCertificate rawPayoff)
    (source : countedProtocol.History) (remaining : Nat) (execution : app.Execution)
    (owner : Player) (current : source.state = some ⟨remaining, some owner, execution⟩)
    (request : execution.application.SeedRequest owner (originalCoordinate owner))
    (clock : execution.application.current.native.clock = 3)
    (first second : app.PlayerEntry) (word : execution.recall owner = [first, second])
    (firstRequest : PhaseRuntimeState.requests first.beforeView.application.2 owner
      (originalCoordinate owner))
    (secondRequest : PhaseRuntimeState.requests second.beforeView.application.2 owner
      (originalCoordinate owner))
    (secondClock : second.beforeView.application.2.native.clock = 2)
    (silent : first.action.transmission = none)
    (secondSilent : second.action.transmission = none)
    (zero : first.beforeView.application.2.native.clock = 0)
    (site : rawModel.InformationSite owner)
    (atSite : site.1 = countedModel.infoOf owner source.trace)
    (choice : rawModel.Choice owner site.1) (selected : choice.1 = some ⟨none⟩)
    (target : rawModel.InformationHistory owner site.1) :
    expect (rawModel.runBehavioralTerminalFrom canonicalCertificate
      (Profile.update (sig := rawModel.behavioralSignature) assessment.strategy owner
        ((assessment.strategy owner).commit site.1 choice)) target.1) (rawPayoff owner) =
          -(3 / 2) := by
  have sourceTrace : countedProtocol.Trace (some ⟨remaining, some owner, execution⟩) :=
    current ▸ source.trace
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
  have clockNext : next.application.current.native.clock = 3 := by
    change (next.observe app owner).application.2.native.clock = 3
    rw [observed]
    exact clock
  have wordNext : next.recall owner = [first, second] := recalled.trans word
  have value := counted_clock_three_wait_assessed_value assessment equilibrium count next owner
    countedTrace requestNext clockNext first second wordNext firstRequest secondRequest silent
      secondSilent zero secondClock
  exact (raw_committed_current_value_eq_finish assessment.strategy target.1 owner count next state
    site.1 target.2 choice ⟨none⟩ selected).trans value

open Classical in
/-- Averaging over the original assessment's whole off-path belief retains
the fixed loss of WAIT at the last original opportunity. -/
theorem raw_clock_three_wait_context_value
    (assessment : rawModel.BehavioralAssessment)
    (equilibrium : assessment.IsSequentialEquilibrium
      (rawMenu.decisionInformationAntichain initial horizon scheduler)
      canonicalCertificate rawPayoff)
    (source : countedProtocol.History) (remaining : Nat) (execution : app.Execution)
    (owner : Player) (current : source.state = some ⟨remaining, some owner, execution⟩)
    (request : execution.application.SeedRequest owner (originalCoordinate owner))
    (clock : execution.application.current.native.clock = 3)
    (first second : app.PlayerEntry) (word : execution.recall owner = [first, second])
    (firstRequest : PhaseRuntimeState.requests first.beforeView.application.2 owner
      (originalCoordinate owner))
    (secondRequest : PhaseRuntimeState.requests second.beforeView.application.2 owner
      (originalCoordinate owner))
    (secondClock : second.beforeView.application.2.native.clock = 2)
    (silent : first.action.transmission = none)
    (secondSilent : second.action.transmission = none)
    (zero : first.beforeView.application.2.native.clock = 0)
    (site : rawModel.InformationSite owner)
    (atSite : site.1 = countedModel.infoOf owner source.trace)
    (choice : rawModel.Choice owner site.1) (selected : choice.1 = some ⟨none⟩) :
    (assessment.continuationContext canonicalCertificate site (rawPayoff owner)).value
      ((assessment.strategy owner).commit site.1 choice) = -(3 / 2) := by
  have integrable := assessment.continuationContext_integrable_of_bounded_terminal
    canonicalCertificate site (rawPayoff owner) (9 / 2)
      (fun final _ => rawPayoff_abs_le owner final)
        ((assessment.strategy owner).commit site.1 choice)
  change (assessment.continuationContextWith
    (rawModel.runBehavioralTerminalFrom canonicalCertificate) site (rawPayoff owner)).value
      ((assessment.strategy owner).commit site.1 choice) = _
  rw [assessment.continuationContextWith_value_tower
    (rawModel.runBehavioralTerminalFrom canonicalCertificate) site (rawPayoff owner)
      ((assessment.strategy owner).commit site.1 choice) integrable,
    ← expect_constant (assessment.belief owner site) (-(3 / 2) : ℝ)]
  apply expect_congr_on_support
  intro target _supported
  exact raw_clock_three_wait_fiber_value assessment equilibrium source remaining execution owner
    current request clock first second word firstRequest secondRequest secondClock silent
      secondSilent zero site atSite choice selected target

end Vegas.Examples.CommitSeedBroadcast
