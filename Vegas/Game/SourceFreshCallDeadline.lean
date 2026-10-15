/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceAsyncTimeliness

/-! # A protected recorded call cannot remain ready at its deadline -/

noncomputable section

namespace Vegas

open SourceProgram EventGraphRuntime Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L)) {mode : EventGraph.ExecutionMode}
  {deadline : (serviceGraph setup mode).EventId → Nat}
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup mode)))

/-- The original protected-inclusion contract forces a still-ready recorded
call to remain before expiry. Its settlement invariant is derived. This uses
the actual event activation stamp preserved along its original native history;
no fixed whole configuration or desired successful outcome is assumed. -/
theorem freshCall_within_deadline_of_ready
    (horizon : Nat) (scheduler : (serviceApplication setup mode deadline leaks).Scheduler)
    (control : (serviceApplication setup mode deadline leaks).Control)
    (trace : ((serviceApplication setup mode deadline leaks).protocol
      (serviceInitialLaw setup mode) horizon scheduler).Trace (some control))
    (owner : Player) (event : (serviceGraph setup mode).EventId)
    (owned : (serviceGraph setup mode).actor? event = some owner)
    (bound : (serviceGraph setup mode).EventId → Nat)
    (inclusion : ProtectedInclusion (serviceRuntime setup mode deadline) leaks
      (serviceInitialLaw setup mode) horizon scheduler bound)
    (earlier later : List (serviceApplication setup mode deadline leaks).PlayerEntry)
    (entry : (serviceApplication setup mode deadline leaks).PlayerEntry)
    (message : Message Player (WitnessedPacket (serviceGraph setup mode)))
    (recorded : control.execution.recall owner = earlier ++ entry :: later)
    (call : FreshCall setup leaks owner event bound entry message)
    (sole : ∀ other ∈ earlier ++ later,
      ¬ EmitsOtherFor (serviceRuntime setup mode deadline) leaks other event message.id)
    (ready : control.execution.application.config.cut.Ready event) :
    control.execution.application.WithinDeadline (serviceRuntime setup mode deadline) event := by
  have facts := legalFacts setup leaks horizon scheduler control trace
  have settles := settlesFreshCalls_history setup leaks inclusion owner event owned trace
  have included := inclusion control trace
  have member : entry ∈ control.execution.recall owner := by
    rw [recorded]
    exact List.mem_append_right _ (List.mem_cons_self ..)
  obtain ⟨entered, activated, fitting⟩ := call.fits.exists
  obtain ⟨_extra, _order, _together, keeps, _accepted⟩ :=
    facts.eventStable owner entry member event call.ready ready.1
  have stamp := keeps owner owned entered activated
  by_contra due
  simp only [EventGraphRuntime.State.WithinDeadline, stamp] at due
  have passed : entry.beforeView.application.publicView.clock + bound event <
      control.execution.application.clock := by omega
  obtain ⟨accepted, receipt⟩ := included event owner owned earlier later entry message recorded
    call.emitted call.authored call.addressed call.ready sole ready.1 passed
  have settled := settles earlier entry later message recorded call sole
  exact ready.1 (settled.2.2 (settled.2.1 accepted receipt))

end Vegas
