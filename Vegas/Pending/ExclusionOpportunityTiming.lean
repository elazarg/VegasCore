/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ExclusionService
import Vegas.Pending.ReactiveOwnerOpportunity

/-! # Protected opportunity timing on actual clear recovery prefixes -/

noncomputable section

namespace Vegas.EventGraphRuntime.Recovery

open Interaction EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L} (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))

/-- Before the owner's readiness-episode activation, actual recovery opportunity
and timeliness rule out native expiry at every genuine public-clear prefix. -/
theorem expiry_stutters_before_owner_opportunity_clear_native
    {initial : PMF (RecoveryState graph)}
    (initialized : ∀ state ∈ initial.support, ∃ inputs,
      state = (⟨State.initial inputs, ∅⟩ : RecoveryState graph))
    {horizon : Nat} {scheduler : (runtime.recoveryApplication leaks).Scheduler}
    {delay bound : graph.EventId → Nat}
    (opportunity : Opportunity runtime leaks initial horizon scheduler delay)
    (timely : runtime.AsyncTimely delay bound)
    (control : (runtime.reactiveApplication leaks).Control)
    (trace : ((runtime.reactiveApplication leaks).protocol (initial.map RecoveryState.native)
      horizon (RecoveryProjection.nativeScheduler runtime leaks scheduler)).Trace (some control))
    (clear : PublicExclusionRecord (⟨control.execution.application, ∅⟩ : RecoveryState graph))
    (event : graph.EventId) (owner : Player) (actor : graph.actor? event = some owner)
    (ready : control.execution.application.config.cut.Ready event)
    (entered : Nat) (activated : control.execution.application.activatedAt event = some entered)
    (absent : ¬ OwnerActivatedSince runtime leaks control.execution.environmentRecall
      event owner entered) :
    environmentStep runtime control.execution.application (.expire event) =
      PMF.pure control.execution.application := by
  have actual := opportunity.clear_native runtime leaks initialized control trace clear
  apply environmentStep_expire_of_not_due runtime _ event ready entered activated
  intro due
  apply absent
  apply actual event owner entered actor
    ((control.execution.application.publicView_eventReady event).mpr ready) activated
  have margin := timely event (by simp only [actor, Option.isSome_some])
  omega

end Vegas.EventGraphRuntime.Recovery
