/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.RecoverySavedSourceView
import Vegas.Source.DebtObservation

/-! # Own failed bindings read from actual live and saved decision views

The predicates below consume an ordinary player view. Their source-point image
is unambiguous by the owning observation-congruence theorem; no native witness
or scheduler-private history is an input to a classifier. Retained own action
words do not create a failed binding after its semantic cells are restored.
-/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Protocol

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

/-- Failure is tested on a source typed observation, independently of the
particular semantic point realizing that observation. -/
def phaseProposalObservedBindingFailure (setup : Setup (Player := Player) (L := L))
    (who : Player) (view : setup.ProtocolView who) : Prop :=
  ∃ point : SourceProgram.ProtocolState setup.program,
    view = some (ProtocolState.observe who setup.program point) ∧
      ProtocolState.FailedBinding who setup.program point

/-- Every point with the observed typed view gives the SAME answer. -/
theorem phaseProposalObservedBindingFailure_observe
    (setup : Setup (Player := Player) (L := L)) (who : Player)
    (point : SourceProgram.ProtocolState setup.program) :
    phaseProposalObservedBindingFailure setup who
        (some (ProtocolState.observe who setup.program point)) ↔
      ProtocolState.FailedBinding who setup.program point := by
  constructor
  · rintro ⟨other, observed, failed⟩
    exact (ProtocolState.failedBinding_iff_of_observe_eq who setup.program other point
      (Option.some.inj observed).symm).mp failed
  · intro failed
    exact ⟨point, rfl, failed⟩

/-- The ORIGINAL live typed view is used before virtual binding repair. -/
def phaseProposalCurrentBindingFailure
    (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
    (runtime : EventGraphRuntime (serviceGraph setup mode))
    (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))
    (who : Player) (event : (serviceGraph setup mode).EventId)
    (view : (phaseApplication runtime leaks).PlayerView) : Prop :=
  phaseProposalObservedBindingFailure setup who
    (phaseSurvivingSourceView? setup mode runtime leaks who event view)

/-- Public checkpoint position selects the saved portion of the SAME original
typed view. Canceled private response records alone are not tested. -/
def phaseProposalSavedBindingFailure
    (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
    (runtime : EventGraphRuntime (serviceGraph setup mode))
    (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))
    (who : Player) (event : (serviceGraph setup mode).EventId)
    (view : (phaseApplication runtime leaks).PlayerView) : Prop :=
  phaseProposalObservedBindingFailure setup who
    ((phaseSurvivingSourceView? setup mode runtime leaks who event view).bind
      (ProtocolView.atRank who setup.program view.application.2.attempt.phase))

variable (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
  (runtime : EventGraphRuntime (serviceGraph setup mode))
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))
  (plan : RuntimePhasePlan (serviceGraph setup mode))

local notation "app" => phaseApplication runtime leaks

/-- Saved failure is read from this chosen archive-aligned checkpoint itself,
not from an independently selected counterpart. -/
theorem phaseProposalSavedBindingFailure_iff_of_seed_request
    (maximal : plan.phases.IsChain fun before after =>
      before.kind ≠ after.kind ∨ before.kind = .sample)
    (horizon : Nat) (scheduler : (app).Scheduler) {control}
    (trace : ((app).protocol
      (setup.initialLaw.map fun draw => PhaseRuntimeState.initial plan (encodeInputs draw))
      horizon scheduler).Trace (some control))
    (checkpoint : RecoverySourceCheckpoint setup mode control.execution.application)
    (aligned : checkpoint.ArchivedRecall) (who : Player)
    (event : (serviceGraph setup mode).EventId) (payload : L.Ty)
    (binding : (serviceGraph setup mode).outputLayout event = .binding who payload)
    (request : control.execution.application.SeedRequest who
      ⟨control.execution.application.attempt, event⟩) :
    phaseProposalSavedBindingFailure setup mode runtime leaks who event
        (control.execution.observe app who) ↔
      ProtocolState.FailedBinding who setup.program (checkpoint.residual.lift
        (ProtocolState.entry checkpoint.residual.tail checkpoint.source)) := by
  unfold phaseProposalSavedBindingFailure
  have readback := checkpoint.saved_view_of_seed_request runtime leaks plan maximal horizon
    scheduler trace aligned who event payload binding request
  change phaseProposalObservedBindingFailure setup who
    ((phaseSurvivingSourceView? setup mode runtime leaks who event
      (control.execution.observe app who)).bind
      (ProtocolView.atRank who setup.program control.execution.application.attempt.phase)) ↔ _
  rw [readback]
  exact phaseProposalObservedBindingFailure_observe setup who _

/-- Any actual original current readback fixes current own failure. In
particular this applies to the same source trace used by the enriched query. -/
theorem phaseProposalCurrentBindingFailure_iff_of_readback
    (who : Player) (event : (serviceGraph setup mode).EventId)
    (view : (app).PlayerView) (point : SourceProgram.ProtocolState setup.program)
    (readback : phaseSurvivingSourceView? setup mode runtime leaks who event view =
      some (ProtocolState.observe who setup.program point)) :
    phaseProposalCurrentBindingFailure setup mode runtime leaks who event view ↔
      ProtocolState.FailedBinding who setup.program point := by
  unfold phaseProposalCurrentBindingFailure
  rw [readback]
  exact phaseProposalObservedBindingFailure_observe setup who point

end Vegas
