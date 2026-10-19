/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseProposalShadowNormalization
import Vegas.Pending.PhaseBindingForeignResponseMemory
import Interaction.ReactiveMessageReadout

/-! # Unchanged other-owner responses under general recovery shadows

Every other player's literal action and full input are retained. Private
registration affects only that actual sender's catalogue; no clear-state or
empty-archive reduction is used.
-/

noncomputable section

namespace Vegas.EventGraphRuntime.BindingShadow

open EventGraph Interaction

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks

/-- The same arbitrary other-owner raw response preserves the general
normalized frame and every nonrepairing player's entire recorded input. -/
theorem respond_foreign_external (memory : BindingShadow graph) (owner actor : Player)
    (different : actor ≠ owner) (owned : memory.OwnBindings owner)
    (left right : (app).Execution)
    (frame : PhaseStateFrame memory owner left.application right.application)
    (supported : memory.CompletedAt right.application.current.native.config)
    (network : left.network = right.network) (receipts : left.receipts = right.receipts)
    (service : left.environmentRecall = right.environmentRecall)
    (recalled : ∀ who, who ≠ owner → left.recall who = right.recall who)
    (response : (app).Action) :
    let first := left.respond app actor response
    let second := right.respond app actor response
    PhaseStateFrame memory owner first.application second.application ∧
      memory.CompletedAt second.application.current.native.config ∧
      first.network = second.network ∧
      phaseExternalObservation runtime leaks owner first =
        phaseExternalObservation runtime leaks owner second := by
  classical
  intro first second
  have nativeView : left.application.current.native.playerView actor =
      right.application.current.native.playerView actor := by
    rw [frame.current]
    exact native_playerView_other owned _ actor different
  have nativePublic : left.application.current.native.publicView =
      right.application.current.native.publicView := congrArg PlayerView.publicView nativeView
  have publicEq := frame.publicView owned
  have attempt : left.application.attempt = right.application.attempt :=
    congrArg PhasePublicView.attempt publicEq
  have packet (material : WitnessedSubmission graph) :
      (app).packet ((app).submit left.application actor material) actor (left.network.known actor)
        material = (app).packet ((app).submit right.application actor material) actor
          (right.network.known actor) material := by
    change (left.application.submit actor material).emit actor (left.network.known actor) material =
      (right.application.submit actor material).emit actor (right.network.known actor) material
    rw [PhaseCount.emit_after_submit, PhaseCount.emit_after_submit]
    rw [congrArg PlayerView.candidates nativeView, nativePublic, publicEq, attempt, network]
  have nextFrame : PhaseStateFrame memory owner first.application second.application := by
    cases response with
    | mk transmission =>
        cases transmission with
        | none => exact frame
        | some material =>
            refine ⟨frame.phases, frame.generation, frame.entry, ?_, frame.retired⟩
            change left.application.current.submit actor material =
              memory.recovery owner (right.application.current.submit actor material)
            rw [frame.current]
            simp only [RecoveryState.submit, recovery]
            rw [native_foreign_submission memory owner actor different
              right.application.current.native material.call]
  have nextSupport : memory.CompletedAt second.application.current.native.config := by
    cases response with
    | mk transmission =>
        cases transmission with
        | none => exact supported
        | some material =>
            change memory.CompletedAt
              (submitStep (material.call.register right.application.current.native actor) actor
                material.call.packet).config
            rw [submitStep_config, (material.call.register_facts actor _).1]
            exact supported
  have nextNetwork : first.network = second.network := by
    cases response with
    | mk transmission =>
        cases transmission with
        | none => exact network
        | some material =>
            change (left.network.submit actor _).2 = (right.network.submit actor _).2
            rw [packet material, network]
  have inputEq (who : Player) (notOwner : who ≠ owner) :
      left.observe app who = right.observe app who := by
    change (⟨left.network.observe who, left.application.playerView who, left.receipts⟩ :
      (app).PlayerView) = ⟨_, _, _⟩
    rw [network, frame.playerView_other owned who notOwner, receipts]
    rfl
  have nextRecall (who : Player) (notOwner : who ≠ owner) : first.recall who = second.recall who :=
    (app).respond_focal_recall_eq left right actor who response network (inputEq who notOwner)
      (recalled who notOwner) (fun material _ => packet material)
  refine ⟨nextFrame, nextSupport, nextNetwork, ?_⟩
  exact phaseExternalObservation_congr runtime leaks first second owner nextNetwork receipts service
    (nextFrame.publicView owned) (nextFrame.playerView_other owned) nextRecall

/-- The repairing owner's silence records no new public data, even when
their own private recall already differs. -/
theorem respond_wait_external (memory : BindingShadow graph) (owner : Player)
    (owned : memory.OwnBindings owner) (left right : (app).Execution)
    (frame : PhaseStateFrame memory owner left.application right.application)
    (network : left.network = right.network) (receipts : left.receipts = right.receipts)
    (service : left.environmentRecall = right.environmentRecall)
    (recalled : ∀ who, who ≠ owner → left.recall who = right.recall who) :
    phaseExternalObservation runtime leaks owner (left.respond app owner ⟨none⟩) =
      phaseExternalObservation runtime leaks owner (right.respond app owner ⟨none⟩) := by
  apply phaseExternalObservation_congr runtime leaks
    (left.respond app owner ⟨none⟩) (right.respond app owner ⟨none⟩) owner network receipts service
    (frame.publicView owned) (frame.playerView_other owned)
  intro who different
  rw [(app).respond_recall_other left owner who different,
    (app).respond_recall_other right owner who different]
  exact recalled who different

end Vegas.EventGraphRuntime.BindingShadow
