/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedBroadcastEarlyPreparationValue
import Vegas.Examples.CommitSeedBroadcastProperEarlyContext

/-! # Exact unusable initial declaration loss on the full raw information fiber -/

noncomputable section

namespace Vegas.Examples.CommitSeedBroadcast

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Protocol.InformationModel
  GameTheory.Math.Probability

open Classical in
/-- Every compatible raw history gives the same unusable initial declaration loss under
the incumbent continuation, with the same permitted current material. -/
theorem raw_unusable_early_fiber_value
    (assessment : rawModel.BehavioralAssessment)
    (equilibrium : assessment.IsSequentialEquilibrium
      (rawMenu.decisionInformationAntichain initial horizon scheduler)
      canonicalCertificate rawPayoff)
    (source : countedProtocol.History) (remaining : Nat) (execution : app.Execution)
    (owner : Player) (current : source.state = some ⟨remaining, some owner, execution⟩)
    (request : execution.application.SeedRequest owner (originalCoordinate owner))
    (clock : execution.application.current.native.clock = 0)
    (material : WitnessedSubmission graph)
    (offered : (⟨some material⟩ : app.Action) ∈ countedMenu.actions owner
      (execution.recall owner) (execution.observe app owner))
    (unusable : (material.call.opening.bind fun raw => raw.as? .bool) = none)
    (site : rawModel.InformationSite owner)
    (atSite : site.1 = countedModel.infoOf owner source.trace)
    (choice : rawModel.Choice owner site.1) (selected : choice.1 = some ⟨some material⟩)
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
  have clockNext : next.application.current.native.clock = 0 := by
    change (next.observe app owner).application.2.native.clock = 0
    rw [observed]
    exact clock
  have nextOffered : (⟨some material⟩ : app.Action) ∈ countedMenu.actions owner
      (next.recall owner) (next.observe app owner) := by
    rw [recalled, observed]
    exact offered
  have value := counted_unusable_early_assessed_value assessment equilibrium count next owner
    countedTrace requestNext clockNext material nextOffered unusable
  exact (raw_committed_current_value_eq_finish assessment.strategy target.1 owner count next state
    site.1 target.2 choice ⟨some material⟩ selected).trans value

open Classical in
/-- Averaging over the original assessment's whole off-path belief retains
the fixed loss of an unusable initial declaration. -/
theorem raw_unusable_early_context_value
    (assessment : rawModel.BehavioralAssessment)
    (equilibrium : assessment.IsSequentialEquilibrium
      (rawMenu.decisionInformationAntichain initial horizon scheduler)
      canonicalCertificate rawPayoff)
    (source : countedProtocol.History) (remaining : Nat) (execution : app.Execution)
    (owner : Player) (current : source.state = some ⟨remaining, some owner, execution⟩)
    (request : execution.application.SeedRequest owner (originalCoordinate owner))
    (clock : execution.application.current.native.clock = 0)
    (material : WitnessedSubmission graph)
    (offered : (⟨some material⟩ : app.Action) ∈ countedMenu.actions owner
      (execution.recall owner) (execution.observe app owner))
    (unusable : (material.call.opening.bind fun raw => raw.as? .bool) = none)
    (site : rawModel.InformationSite owner)
    (atSite : site.1 = countedModel.infoOf owner source.trace)
    (choice : rawModel.Choice owner site.1) (selected : choice.1 = some ⟨some material⟩) :
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
  exact raw_unusable_early_fiber_value assessment equilibrium source remaining
    execution owner
    current request clock material offered unusable site atSite choice selected target

end Vegas.Examples.CommitSeedBroadcast
