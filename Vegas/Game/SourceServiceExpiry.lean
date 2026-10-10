/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceAsyncTimeliness

noncomputable section
namespace Vegas
open SourceProgram Interaction EventGraphRuntime GameTheory.Math.Probability
variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]

/-- A genuinely conforming timely prescribed call excludes actual due expiry:
 protected inclusion settles it before its readiness episode can become due. -/
theorem freshCall_not_due (setup : Setup (Player := Player) (L := L))
    {mode : EventGraph.ExecutionMode}
    {deadline : (serviceGraph setup mode).EventId → Nat}
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup mode)))
    {horizon : Nat} {scheduler : (serviceApplication setup mode deadline leaks).Scheduler}
    {bound : (serviceGraph setup mode).EventId → Nat}
    (inclusion : ProtectedInclusion (serviceRuntime setup mode deadline) leaks
      (serviceInitialLaw setup mode) horizon scheduler bound)
    (control : (serviceApplication setup mode deadline leaks).Control)
    (trace : ((serviceApplication setup mode deadline leaks).protocol (serviceInitialLaw setup mode)
      horizon scheduler).Trace (some control))
    (event : (serviceGraph setup mode).EventId) (owner : Player)
    (owned : (serviceGraph setup mode).actor? event = some owner)
    (earlier later : List (serviceApplication setup mode deadline leaks).PlayerEntry)
    (entry : (serviceApplication setup mode deadline leaks).PlayerEntry)
    (message : Message Player (WitnessedPacket (serviceGraph setup mode)))
    (split : control.execution.recall owner = earlier ++ entry :: later)
    (call : FreshCall setup leaks owner event bound entry message)
    (sole : ∀ other ∈ earlier ++ later,
      ¬ EmitsOtherFor (serviceRuntime setup mode deadline) leaks other event message.id)
    (ready : control.execution.application.config.cut.Ready event)
    (entered : Nat) (activated : control.execution.application.activatedAt event = some entered) :
    control.execution.application.clock - entered < deadline event := by
  by_contra notBefore
  have due : deadline event ≤ control.execution.application.clock - entered := by omega
  have retained : entry ∈ control.execution.recall owner := by
    rw [split]
    exact List.mem_append_right _ (List.mem_cons_self ..)
  have stable := (serviceRuntime setup mode deadline).entryEventStable_history leaks
    (serviceInitialLaw setup mode) horizon scheduler trace
  obtain ⟨_, _, _, episode, _⟩ := stable owner entry retained event call.ready ready.1
  obtain ⟨beforeEntered, recorded, fits⟩ := call.fits.exists
  have same := episode owner owned beforeEntered recorded
  rw [activated] at same
  have equal := Option.some.inj same
  subst beforeEntered
  change entry.beforeView.application.publicView.clock - entered + bound event <
    deadline event at fits
  have late : entry.beforeView.application.publicView.clock + bound event <
      control.execution.application.clock := by omega
  have receipt := (prescribed_packet_settles setup leaks inclusion trace event owner owned
    earlier later entry message split call sole).1 late
  have settled := settlesFreshCalls_history setup leaks inclusion owner event owned trace
    earlier entry later message split call sole
  exact ready.1 (settled.2.2 receipt)

end Vegas
