/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceDecisionSupport
import Vegas.Pending.ReactiveSubmissionSerial

/-! # Operational resources at every retained decision

The actual source prefix supplies readiness, a live deadline and communication
invariants. Public serial accounting proves that a player has made no fresh
submission during the current phase, without constraining which event a raw
message could name.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]

theorem sourceService_decision_resources
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (bounds : MessageBounds (graph setup)) (values : bounds.CoversBindingValues)
    (capacity : (graph setup).order.eventCount ≤ bounds.candidateCount)
    (rosters : (graph setup).EventId → List Player)
    (opportunities : BindingOpportunities setup rosters)
    (network : (runtime setup).NetworkPolicy leaks)
    (who : Player) (control : (application setup leaks).Control)
    (trace : ((sourceServiceMenu setup leaks bounds rosters).protocol (initialLaw setup)
      (rosterPlan setup rosters).length (rosterScheduler setup leaks rosters network)).Trace
        (some control)) (active : control.actor = some who)
    (event : (graph setup).EventId)
    (ready : control.execution.application.config.cut.Ready event)
    (owner : Player) (owned : (graph setup).actor? event = some owner) :
    control.execution.application.config.cut.Ready event ∧
      control.execution.application.WithinDeadline (runtime setup) event ∧
      control.execution.application.BindingInvariant ∧
      control.execution.InputRecall (application setup leaks) ∧
      control.execution.SerialRecall (application setup leaks) ∧
      control.execution.network.SerialsBeforeNext ∧
      (control.execution.network.nextSerial owner =
        control.execution.network.ledger.countP (fun message => message.sender = owner) →
        (runtime setup).eventRecorded leaks (control.execution.recall owner) event = false) := by
  let app := application setup leaks
  let menu := sourceServiceMenu setup leaks bounds rosters
  obtain ⟨selectedEvent, slot, initial, _, _, Γ, names, remaining, remainingProfile, source,
      refs, embedding, refsBefore, _, _, _, boundary, prior, sample, checkpoint, sole, reached,
      activated, sampled, config, publicEq, _, _⟩ :=
    sourceService_decision_boundary setup leaks bounds values capacity rosters opportunities
      network (failureProfile setup.program) who control trace active
  have eventEq : selectedEvent = event :=
    (sole.2 event ((control.execution.application.publicView_eventReady event).mpr ready)).symm
  subst selectedEvent
  obtain ⟨_, binding, recalled, serialRecall, serials⟩ := checkpoint.run_core
    menu.uniformResponses network (((rosters event).take slot).map ServiceInstruction.player)
      prior reached
  have ready := checkpoint.ready event rfl
  have timely := checkpoint.timely event rfl (by rw [owned]; rfl)
  have clock := congrArg PublicView.clock publicEq
  have activation := congrArg PublicView.activatedAt publicEq
  have currentSerialRecall := app.environment_serialRecall prior control.execution (.activate who)
    serialRecall activated
  refine ⟨by rw [config]; exact ready, ?_, ?_,
    app.environment_inputRecall prior control.execution (.activate who) recalled activated,
    currentSerialRecall, ?_, ?_⟩
  · unfold EventGraphRuntime.State.WithinDeadline at timely ⊢
    change control.execution.application.clock = boundary.application.clock at clock
    change control.execution.application.activatedAt = boundary.application.activatedAt
      at activation
    rw [clock, activation]
    exact timely
  · rw [sampled]
    exact binding
  · rw [sampled]
    exact serials.learn who sample
  · intro clean
    obtain ⟨suffix, recalled⟩ := (runtime setup).runInteractionPlan_recall_prefix leaks
      menu.uniformResponses network (((rosters event).take slot).map ServiceInstruction.player)
        boundary prior reached owner
    have ledger := (runtime setup).player_window_ledger leaks menu.uniformResponses network
      ((rosters event).take slot) boundary prior reached
    apply (runtime setup).eventRecorded_false_of_public_serial leaks boundary control.execution
      owner event checkpoint.serialRecall currentSerialRecall (checkpoint.accounted owner)
        ?_ (checkpoint.unsent owner event (Nat.le_refl _)) suffix ?_ clean
    · rw [sampled]
      exact ledger
    · rw [sampled]
      exact recalled.symm

end Vegas
