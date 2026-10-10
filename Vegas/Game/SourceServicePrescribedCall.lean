/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceAsyncTimeliness
import Vegas.Pending.ReactiveSampledAcceptance
import Vegas.Pending.ReactivePosteriorAlignment
import Vegas.Pending.ReactiveOriginalResponseStability
import Vegas.Pending.ReactiveOwnerOpportunity

/-! # Fresh service calls from actual timely prescribed responses -/

noncomputable section
namespace Vegas
open SourceProgram Interaction EventGraphRuntime GameTheory.Math.Probability
variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]

/-- An actual supported compiler submission at a timely owner response
satisfies the existing service settlement fresh-call contract. -/
theorem prescribed_response_freshCall (setup : Setup (Player := Player) (L := L))
    {mode : EventGraph.ExecutionMode}
    {deadline : (serviceGraph setup mode).EventId → Nat}
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup mode)))
    (delay bound : (serviceGraph setup mode).EventId → Nat)
    (timely : (serviceRuntime setup mode deadline).AsyncTimely delay bound)
    (execution : (serviceApplication setup mode deadline leaks).Execution)
    (valid : execution.application.BindingInvariant)
    (who : Player) (policy : (serviceGraph setup mode).BehavioralPolicy who)
    (intentions : List (Option (serviceGraph setup mode).Completion))
    (physical : (serviceApplication setup mode deadline leaks).Action)
    (remembered : (serviceGraph setup mode).Completion)
    (supported : (physical, some remembered) ∈
      ((serviceRuntime setup mode deadline).prescribedReactiveResponse leaks who policy
        (execution.recall who) intentions
        (execution.observe (serviceApplication setup mode deadline leaks) who)).support)
    (entered : Nat)
    (activated : execution.application.activatedAt remembered.event = some entered)
    (responded : execution.application.clock ≤ entered + delay remembered.event)
    (material : WitnessedSubmission (serviceGraph setup mode))
    (transmitted : physical.transmission = some material) :
    FreshCall setup leaks who remembered.event bound
      ⟨execution.observe (serviceApplication setup mode deadline leaks) who, physical,
        some ⟨(who, execution.network.nextSerial who),
          material.emit ((serviceApplication setup mode deadline leaks).submit
            execution.application who material) who (execution.network.known who)⟩⟩
      ⟨(who, execution.network.nextSerial who),
        material.emit ((serviceApplication setup mode deadline leaks).submit
          execution.application who material) who (execution.network.known who)⟩ := by
  let runtime := serviceRuntime setup mode deadline
  let app := serviceApplication setup mode deadline leaks
  have ready := runtime.prescribedReactiveResponse_some_ready leaks who policy
    (execution.recall who) intentions (execution.observe app who) physical remembered supported
  have fits : execution.application.publicView.InclusionFitsDeadline runtime bound
      remembered.event := by
    exact PublicView.inclusionFitsDeadline_of_response_delay runtime delay bound timely
      execution.application.publicView remembered.event entered
      (by simp only [ready.2, Option.isSome_some]) activated responded
  have selected := (runtime.prescribedReactiveResponse_some_fresh leaks who policy
    (execution.recall who) intentions (execution.observe app who) physical remembered
      supported).2.2
  have actionTransmission := congrArg ReactiveApplication.Action.transmission selected
  have decisionSent := actionTransmission.symm.trans transmitted
  have addressed : material.call.packet.event? (serviceGraph setup mode) =
      some remembered.event := by
    rcases runtime.reactiveDecision_transmission leaks who remembered.event remembered.action
      (execution.observe app who).application with absent | ⟨other, sent, addressed⟩
    · rw [decisionSent] at absent
      cases absent
    · have equal : other = material := Option.some.inj (sent.symm.trans decisionSent)
      exact equal ▸ addressed
  refine ⟨⟨material, transmitted⟩, rfl, rfl, addressed, ready.1, fits, ?_⟩
  exact runtime.prescribedReactiveResponse_emitted_acceptable leaks execution valid who policy
    (execution.recall who) intentions physical remembered supported
      fits.withinDeadline material transmitted

end Vegas
