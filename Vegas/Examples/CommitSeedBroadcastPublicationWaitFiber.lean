/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedBroadcastPublicationWait
import Vegas.Examples.CommitSeedBroadcastCountedInformation
import Vegas.Examples.CommitSeedBroadcastCurrentChoiceValue

/-! # The publication WAIT loss on the entire actual native information fiber -/

noncomputable section

namespace Vegas.Examples.CommitSeedBroadcast

open SourceProgram EventGraphRuntime Interaction GameTheory GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Protocol.InformationModel
  GameTheory.Math.Probability

open Classical in
/-- Each compatible raw history retains the same public publication request.
Its literal current WAIT loses the stake under the unchanged assessed tail. -/
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
        ((assessment.strategy owner).commit site.1 choice)) target.1) (rawPayoff owner) =
          -(3 / 2) := by
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
  have value := counted_publication_wait_assessed_value assessment equilibrium count next owner
    trace (by rw [attempt]; exact retired) requestNext
  exact (raw_committed_current_value_eq_finish assessment.strategy target.1 owner count next state
    site.1 target.2 choice ⟨none⟩ selected).trans value

open Classical in
/-- The actual assessment's entire information belief assigns the same fixed
loss to a publication WAIT; its off-path histories need no extra cleanliness premise. -/
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
  exact raw_publication_wait_fiber_committed_value assessment equilibrium source remaining execution
    owner current retired request site atSite choice selected target

end Vegas.Examples.CommitSeedBroadcast
