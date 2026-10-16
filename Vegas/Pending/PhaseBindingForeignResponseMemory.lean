/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseBindingForeignSubmission

/-! # Complete foreign response steps through all-value binding memory -/

noncomputable section

namespace Vegas.EventGraphRuntime.BindingShadow

open EventGraph Interaction

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L} (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks

/-- The same arbitrary foreign raw response derives the next complete physical
reconstruction, identical envelopes and all foreign full private words. The
hidden owner's word stays unchanged on both sides. -/
theorem respond_foreign_memory (memory : BindingShadow graph) (owner actor : Player)
    (different : actor ≠ owner) (owned : memory.OwnBindings owner)
    (left right : (app).Execution)
    (application : left.application = memory.phased owner right.application)
    (network : left.network = right.network) (receipts : left.receipts = right.receipts)
    (service : left.environmentRecall = right.environmentRecall)
    (recalled : ∀ who, who ≠ owner → left.recall who = right.recall who)
    (response : (app).Action) :
    let first := left.respond app actor response
    let second := right.respond app actor response
    first.application = memory.phased owner second.application ∧
      first.network = second.network ∧ first.receipts = second.receipts ∧
      first.environmentRecall = second.environmentRecall ∧
      (∀ who, who ≠ owner → first.recall who = second.recall who) ∧
      first.recall owner = left.recall owner ∧ second.recall owner = right.recall owner := by
  intro first second
  have observed : left.observe app actor = right.observe app actor := by
    change (⟨left.network.observe actor, left.application.playerView actor, left.receipts⟩ :
      (app).PlayerView) = ⟨_, _, _⟩
    rw [network, application, phased_playerView_other owned _ actor different, receipts]
    rfl
  have nativeView : left.application.current.native.playerView actor =
      right.application.current.native.playerView actor := by
    rw [application]
    exact native_playerView_other owned _ actor different
  have nativePublic : left.application.current.native.publicView =
      right.application.current.native.publicView := congrArg PlayerView.publicView nativeView
  have publicView : left.application.publicView = right.application.publicView := by
    rw [application]
    exact phased_publicView owned _
  have attempt : left.application.attempt = right.application.attempt :=
    congrArg PhasePublicView.attempt publicView
  have packet (material : WitnessedSubmission graph) :
      (app).packet ((app).submit left.application actor material) actor (left.network.known actor)
          material =
        (app).packet ((app).submit right.application actor material) actor
          (right.network.known actor)
          material := by
    change (left.application.submit actor material).emit actor (left.network.known actor)
        material =
      (right.application.submit actor material).emit actor (right.network.known actor) material
    rw [PhaseCount.emit_after_submit, PhaseCount.emit_after_submit]
    rw [congrArg PlayerView.candidates nativeView, nativePublic, publicView, attempt, network]
  have nextApplication : first.application = memory.phased owner second.application := by
    cases response with
    | mk transmission =>
        cases transmission with
        | none => exact application
        | some material =>
            change left.application.submit actor material =
              memory.phased owner (right.application.submit actor material)
            rw [application]
            simp only [PhaseRuntimeState.submit, phased, recovery, RecoveryState.submit]
            rw [native_foreign_submission memory owner actor different
              right.application.current.native material.call]
  have nextRecall : ∀ who, who ≠ owner → first.recall who = second.recall who := by
    intro who notOwner
    by_cases acting : who = actor
    · subst who
      cases response with
      | mk transmission =>
          cases transmission with
          | none =>
              simp only [first, second, ReactiveApplication.Execution.respond, ↓reduceIte]
              rw [recalled actor different, observed]
          | some material =>
              simp only [first, second, ReactiveApplication.Execution.respond, ↓reduceIte]
              rw [recalled actor different, observed, packet material, network]
    · exact ((app).respond_recall_other left actor who acting response).trans
        ((recalled who notOwner).trans
          ((app).respond_recall_other right actor who acting response).symm)
  refine ⟨nextApplication, ?_, ?_, service, nextRecall,
    (app).respond_recall_other left actor owner (Ne.symm different) response,
    (app).respond_recall_other right actor owner (Ne.symm different) response⟩
  · cases response with
    | mk transmission =>
        cases transmission with
        | none => exact network
        | some material =>
            change (left.network.submit actor
                ((app).packet ((app).submit left.application actor material) actor
                  (left.network.known actor) material)).2 = _
            rw [packet material, network]
            rfl
  · exact receipts

end Vegas.EventGraphRuntime.BindingShadow
