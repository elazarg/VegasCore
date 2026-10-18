/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedBroadcastPublicationOpeningFiber

/-! # Publication WAIT is excluded by actual native sequential optimality -/

noncomputable section

namespace Vegas.Examples.CommitSeedBroadcast

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Protocol.InformationModel
  GameTheory.Math.Probability

open Classical in
/-- An actual successful publication callback cannot prescribe WAIT in a raw
sequential equilibrium. Candidate availability and timeliness are derived from
the original counted representative; the comparison covers its full raw fiber. -/
theorem counted_successful_publication_wait_not_supported
    (assessment : rawModel.BehavioralAssessment)
    (equilibrium : assessment.IsSequentialEquilibrium
      (rawMenu.decisionInformationAntichain initial horizon scheduler)
      canonicalCertificate rawPayoff)
    (source : countedProtocol.History) (remaining : Nat) (execution : app.Execution)
    (owner : Player) (current : source.state = some ⟨remaining, some owner, execution⟩)
    (retired : execution.application.attempt ≠ originalAttempt)
    (request : execution.application.SeedRequest owner
      ⟨execution.application.attempt, revealEvent owner⟩)
    (value : Bool)
    (stored : execution.application.current.native.config.store (.inr (bindingEvent owner)) =
      some (cast (congrArg EventField.Value (bindingEvent_layout owner).symm)
        (PublicationResult.success value)))
    (site : rawModel.InformationSite owner)
    (atSite : site.1 = countedModel.infoOf owner source.trace)
    (choice : rawModel.Choice owner site.1) (selected : choice.1 = some ⟨none⟩) :
    choice ∉ (assessment.strategy owner site.1).support := by
  have trace : countedProtocol.Trace (some ⟨remaining, some owner, execution⟩) :=
    current ▸ source.trace
  obtain ⟨candidate, allowed⟩ := counted_tail_truthful_opening_available remaining execution
    owner trace retired request value stored
  exact raw_publication_wait_not_supported assessment equilibrium source remaining execution
    owner current retired candidate value allowed request stored site atSite choice selected

end Vegas.Examples.CommitSeedBroadcast
