/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.ReservedEpochBindingFrame
import Vegas.Pending.ReactiveSignedCommitments

/-! # Authored private preparation in actual owner-frame comparisons -/

noncomputable section

namespace Vegas.EventGraphRuntime.ReservedEpoch

open SourceProgram EventGraph Interaction

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {Γ : SourceCtx Player L} {O : Finset VarId}
  (program : SourceProgram Player L Γ O)

local notation "graph" =>
  EventGraph.withMode (toEventGraph program) EventGraph.ExecutionMode.concurrentReveals

theorem BindingFrame.submit {owner : Player} {left right : State graph}
    (frame : BindingFrame program owner left right) (submission : Submission graph) :
    BindingFrame program owner
      (submitStep (submission.register left owner) owner submission.packet)
      (submitStep (submission.register right owner) owner submission.packet) := by
  have firstConfig :=
    (submitStep_config (submission.register left owner) owner submission.packet).trans
      (submission.register_facts owner left).1
  have secondConfig :=
    (submitStep_config (submission.register right owner) owner submission.packet).trans
      (submission.register_facts owner right).1
  have firstPublic := (submitStep_publicView (submission.register left owner) owner
    submission.packet).trans (submission.register_facts owner left).2
  have secondPublic := (submitStep_publicView (submission.register right owner) owner
    submission.packet).trans (submission.register_facts owner right).2
  have firstAccepted := (submitStep_accepted (submission.register left owner) owner
    submission.packet).trans (submission.register_accepted left owner)
  have secondAccepted := (submitStep_accepted (submission.register right owner) owner
    submission.packet).trans (submission.register_accepted right owner)
  constructor
  · rw [firstConfig, secondConfig]
    exact frame.inputs
  · intro event visible
    rw [firstConfig, secondConfig]
    exact frame.publicOutputs event visible
  · intro event payload binding
    rw [firstConfig, secondConfig]
    exact frame.ownerOutputs event payload binding
  · rw [firstConfig, secondConfig]
    exact frame.ownHistory
  · intro event payload binding
    rw [firstAccepted, secondAccepted]
    exact frame.accepted event payload binding
  · intro slot
    rw [submission.candidateAfter_eq owner left slot,
      submission.candidateAfter_eq owner right slot]
    rw [funext frame.candidates]
  · intro candidate owned
    unfold State.HandleUnused
    rw [firstAccepted, secondAccepted]
    exact frame.unused candidate owned
  · intro event payload binding
    have first := congrArg PublicView.activatedAt firstPublic
    have second := congrArg PublicView.activatedAt secondPublic
    exact (congrFun first event).trans
      ((frame.activated event payload binding).trans (congrFun second event).symm)
  · have first := congrArg PublicView.clock firstPublic
    have second := congrArg PublicView.clock secondPublic
    exact first.trans (frame.clock.trans second.symm)

theorem foreign_submission_frame (state : State graph) (owner foreign : Player)
    (different : owner ≠ foreign) (submission : Submission graph) :
    BindingFrame program owner state
      (submitStep (submission.register state foreign) foreign submission.packet) := by
  have config :=
    (submitStep_config (submission.register state foreign) foreign submission.packet).trans
      (submission.register_facts foreign state).1
  have publicView := (submitStep_publicView (submission.register state foreign) foreign
    submission.packet).trans (submission.register_facts foreign state).2
  have accepted := (submitStep_accepted (submission.register state foreign) foreign
    submission.packet).trans (submission.register_accepted state foreign)
  have other := submission.register_other state foreign owner different
  have catalogs := congrArg PlayerView.candidates other
  constructor
  · rw [config]
  · intro event visible
    rw [config]
  · intro event payload binding
    rw [config]
  · rw [config]
  · intro event payload binding
    rw [accepted]
  · intro slot
    rw [submitStep_lookup_other _ foreign owner different submission.packet slot]
    exact (congrFun catalogs slot).symm
  · intro candidate owned
    unfold State.HandleUnused
    rw [accepted]
  · intro event payload binding
    exact (congrFun (congrArg PublicView.activatedAt publicView) event).symm
  · exact (congrArg PublicView.clock publicView).symm

end Vegas.EventGraphRuntime.ReservedEpoch
