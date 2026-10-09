/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommittedResolutionBobService
import Interaction.ReactivePassiveDecision

/-! # Bob's actual whole continuation is his current RAW lottery

The physical scheduler never activates any player again after Bob's response.
Consequently arbitrary behavioral policies, including whole-policy deviations,
induce the lottery over Bob's current responses followed by one fixed passive
physical continuation. No one-shot principle or restrictions on beliefs are
used in this conclusion.
-/

noncomputable section

namespace Vegas.Examples.CommittedResolutionBobDecision

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability
open CommittedResolutionService CommittedResolutionBobService

/-- Exact physical endpoint law under an arbitrary native behavioral profile,
from any compatible legal Bob decision history. The result holds for every
finite RAW response menu and uses the complete native assessment fuel. -/
theorem bob_continuation_current_law (menu : app.ResponseMenu)
    (profile : ∀ who, (menu.information (initialLaw setup)
      CommittedResolutionService.horizon
        CommittedResolutionRecovery.scheduler).BehavioralPolicy who)
    (history : (menu.protocol (initialLaw setup) CommittedResolutionService.horizon
      CommittedResolutionRecovery.scheduler).History)
    (remaining : Nat) (execution : app.Execution)
    (current : history.state = some ⟨remaining, some bob, execution⟩) :
    ((menu.information (initialLaw setup) CommittedResolutionService.horizon
      CommittedResolutionRecovery.scheduler).runBehavioralFrom profile
        (2 * CommittedResolutionService.horizon + 1) history).map History.state =
      ((profile bob ((menu.information (initialLaw setup) CommittedResolutionService.horizon
        CommittedResolutionRecovery.scheduler).infoOf bob history.trace)).map
          (fun choice => choice.1.getD ⟨none⟩)).bind fun response =>
        (app.runRounds CommittedResolutionRecovery.scheduler (fun _ => app.silentPolicy)
          remaining (execution.respond app bob response)).map app.finished := by
  have raw : (app.protocol (initialLaw setup) CommittedResolutionService.horizon
      CommittedResolutionRecovery.scheduler).Trace
        (some ⟨remaining, some bob, execution⟩) :=
    current ▸ menu.toRawTrace (initialLaw setup) CommittedResolutionService.horizon
      CommittedResolutionRecovery.scheduler history.trace
  exact menu.run_last_response (initialLaw setup) CommittedResolutionService.horizon
    CommittedResolutionRecovery.scheduler 11 recovery_after_bob_passive profile history
      bob remaining execution current (by rw [(recovery_bob_phase _ raw rfl).1])

end Vegas.Examples.CommittedResolutionBobDecision
