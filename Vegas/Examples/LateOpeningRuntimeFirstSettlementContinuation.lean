/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.LateOpeningRuntimeSettlementContinuation
import Vegas.Examples.LateOpeningRuntimeFirstRetryRationality
import Vegas.Examples.LateOpeningRuntimeAliceFirstPacket

/-! # Complete original continuations from the first late sender response

Every raw first response and original subsequent policy factors through the
actual first receiver binding prefix. This retains the complete final execution
law, including private submission representations and all later raw traffic.
-/

noncomputable section

namespace Vegas.Examples.LateOpeningRuntimeFirstSettlementContinuation

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory GameTheory.Protocol GameTheory.Math.Probability
open LateOpeningRuntimeSource LateOpeningRuntimeService LateOpeningRuntimeLatePrefix
  LateOpeningRuntimeLatePrefixKernel LateOpeningRuntimeSettlementContinuation
  LateOpeningRuntimeFirstRetryComparison

variable (weight : ℝ) (nonnegative : 0 ≤ weight)

theorem response_completion_law
    (decision : LateOpeningRuntimeAliceFirstDecision.DecisionHistory weight nonnegative)
    (response : app.Action) (players : Player → app.Policy) :
    LateOpeningRuntimeAliceFirstPacket.responseLaw weight nonnegative decision response players =
      (firstBindingLaw weight nonnegative decision response players).bind
        (receiverCompletion weight nonnegative players) := by
  unfold LateOpeningRuntimeAliceFirstPacket.responseLaw firstBindingLaw
  rw [show 22 = 7 + 15 from rfl, app.runRounds_add, PMF.bind_bind]
  apply bind_congr_on_support
  intro before reached
  apply receiver_suffix weight nonnegative players before
  rw [app.runRounds_environmentRecall_length
    (LateOpeningRuntimeService.scheduler weight nonnegative) players 7 _ before reached]
  change decision.execution.environmentRecall.length + 7 = 11
  rw [LateOpeningRuntimeAliceFirstDecision.decision_cursor]

theorem original_completion_law (profile : Profile weight nonnegative)
    (bit : Bool) (label : Fin 3) :
    ((firstResponses weight nonnegative profile bit label).bind fun response =>
      LateOpeningRuntimeAliceFirstPacket.responseLaw weight nonnegative
        (LateOpeningRuntimeAliceFirstWitness.decisionHistory weight nonnegative bit label)
          response (players weight nonnegative profile)) =
      (originalLaw weight nonnegative profile bit label).bind
        (receiverCompletion weight nonnegative (players weight nonnegative profile)) := by
  simp_rw [response_completion_law]
  rw [← PMF.bind_bind]
  rfl

end Vegas.Examples.LateOpeningRuntimeFirstSettlementContinuation
