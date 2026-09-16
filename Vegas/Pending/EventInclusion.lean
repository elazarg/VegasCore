/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.EventService
import Interaction.MessageApplicationLaws
import Interaction.MessagePoolFreshness

/-! # Immediate inclusion of prescribed event submissions -/

noncomputable section

namespace Vegas.EventGraphRuntime

open GameTheory.Math.Probability Interaction

variable {Player : Type} [DecidableEq Player]
variable {L : IExpr} [R : IExpr.ResultTypes L]
variable {graph : Vegas.EventGraph Player L}

/-- A matching submission is selected by the reserved event slot immediately
after `Interaction.MessageApplication.afterSubmit`, independently of all older
pending traffic. -/
theorem latestEventSubmissionCommand_afterSubmit
    (runtime : EventGraphRuntime graph)
    (execution : runtime.application.PolicyExecution)
    (event : graph.EventId) (owner : Player) (packet : Payload graph)
    (addressed : packet.event? graph = some event) :
    runtime.latestEventSubmissionCommand event owner
        (MessageApplication.State.environmentView runtime.application
          (runtime.application.afterSubmit execution owner packet).native) =
      .include (owner, execution.native.pool.nextSerial owner) := by
  have selected : latestEventSubmission?
      (execution.native.pool.submit owner packet).2 event owner =
        some ⟨(owner, execution.native.pool.nextSerial owner), packet⟩ := by
    apply latestEventSubmission?_append_matching execution.native.pool event owner
    exact ⟨rfl, addressed⟩
  unfold latestEventSubmissionCommand
  change (match latestEventSubmission?
      (execution.native.pool.submit owner packet).2 event owner with
    | some message => MessageInterface.EnvironmentPolicyCommand.include message.id
    | none => MessageInterface.EnvironmentPolicyCommand.wait) = _
  rw [selected]

/-- Exact native effect of the reserved inclusion immediately following an
actual submission. The fresh identifier premise is local and permits an
otherwise arbitrary prior pending pool. -/
theorem serviceStep_includeLatest_afterSubmit_native
    (runtime : EventGraphRuntime graph)
    (players : Player → runtime.application.PlayerPolicy)
    (wire : runtime.application.WirePolicy)
    (execution : runtime.application.PolicyExecution)
    (event : graph.EventId) (owner : Player) (packet : Payload graph)
    (nextState : State graph)
    (addressed : packet.event? graph = some event)
    (fresh : execution.native.pool.lookup
      (owner, execution.native.pool.nextSerial owner) = none)
    (accepted : handle runtime execution.native.application
      ⟨(owner, execution.native.pool.nextSerial owner), packet⟩ = some nextState) :
    (runtime.serviceStep players wire (.includeLatest event owner)
        (runtime.application.afterSubmit execution owner packet)).map
        MessageInterface.PolicyExecution.native =
      FinDist.pure
        ⟨nextState,
          ((execution.native.pool.submit owner packet).2.includePending
            (owner, execution.native.pool.nextSerial owner)).state,
          execution.native.receipts ++
            [((owner, execution.native.pool.nextSerial owner), true)]⟩ := by
  change (runtime.application.environmentPolicyStep
    (runtime.application.afterSubmit execution owner packet)
    (runtime.latestEventSubmissionCommand event owner
      (MessageApplication.State.environmentView runtime.application
        (runtime.application.afterSubmit execution owner packet).native))).map
      MessageInterface.PolicyExecution.native = _
  rw [runtime.latestEventSubmissionCommand_afterSubmit execution event owner packet addressed]
  rw [runtime.application.environmentStep_native]
  simp only [MessageApplication.EnvironmentPolicyCommand.toAction,
    MessageApplication.step]
  rw [runtime.application.includePending_accept
    (runtime.application.afterSubmit execution owner packet).native
    (owner, execution.native.pool.nextSerial owner)
    ⟨(owner, execution.native.pool.nextSerial owner), packet⟩ nextState]
  · rfl
  · exact MessagePool.lookup_submit_fresh execution.native.pool owner packet fresh
  · exact accepted

end Vegas.EventGraphRuntime
