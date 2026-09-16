/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.DeviationLocality
import Interaction.CommitmentCandidateKnowledge

/-! # Application replay at a synchronized focal checkpoint -/

noncomputable section
namespace Vegas.GraphRuntime

open Interaction Graph

variable {Player : Type} [DecidableEq Player]
variable {L : IExpr} [R : IExpr.ResultTypes L]
variable {Γ Δ : VCtx Player L}

/-- Proof-only state projection used by replay. It includes the full focal
candidate catalogue, including initial handles, but is not a policy input. -/
def State.focalReplayKey (focal : Player) (state : State Player L Δ) :=
  (state.playerView focal, fun slot => state.candidates.lookup (focal, slot))

omit R in
theorem observe_cons_same (focal : Player) (name : VarId)
    (binding : BindTy Player L) (value : L.Val binding.base)
    (left right : VEnv L Γ) (visible : observe focal left = observe focal right) :
    observe focal (VEnv.cons (x := name) (τ := binding) value left) =
      observe focal (VEnv.cons (x := name) (τ := binding) value right) := by
  change Observation.mk _ = Observation.mk _
  congr 1
  funext field ty source
  cases source with
  | here =>
      rcases binding with ⟨base, visibility⟩
      cases visibility <;> rfl
  | there source =>
      have cell := congrArg (fun observation => observation.cells.get source) visible
      rcases ty with ⟨ty, visibility⟩
      cases visibility <;> exact cell

omit R in
private theorem accept_focal_lookup_congr
    (focal : Player) (left right : CommitmentCandidates Player Slot (Raw L))
    (agrees : ∀ slot, left.lookup (focal, slot) = right.lookup (focal, slot))
    (accepted : Handle Player) (slot : Slot) :
    (left.accept accepted).lookup (focal, slot) =
      (right.accept accepted).lookup (focal, slot) :=
  CommitmentCandidates.accept_lookup_eq_of_known
    (known := fun handle => handle.1 = focal) (fun handle owned => by
      obtain ⟨owner, handleSlot⟩ := handle
      simp only at owned
      subst owner
      exact agrees handleSlot) accepted (focal, slot) rfl

private theorem advanceResolve_focalReplayKey_congr
    (_runtime : GraphRuntime Player L Δ) (focal : Player) (outputName : VarId)
    {payload : L.Ty}
    (next : Graph Player L ((outputName, .pub (R.result payload)) :: Γ) Δ)
    (leftIdeal rightIdeal : VEnv L Γ)
    (visible : observe focal leftIdeal = observe focal rightIdeal)
    (values : PublicValues Γ) (bindings : Bindings Player)
    (leftCandidates rightCandidates :
      CommitmentCandidates Player Slot (Raw L))
    (candidates : ∀ slot, leftCandidates.lookup (focal, slot) =
      rightCandidates.lookup (focal, slot)) (pc clock : Nat)
    (result : PublicationResult (L.Val payload)) :
    (advanceResolve next leftIdeal values bindings leftCandidates pc clock result).focalReplayKey
        focal =
      (advanceResolve next rightIdeal values bindings rightCandidates pc clock
        result).focalReplayKey focal := by
  apply Prod.ext
  · change PlayerView.mk focal _ _ _ = PlayerView.mk focal _ _ _
    congr 1
    · exact observe_cons_same focal outputName (.pub (R.result payload))
        ((R.valueEquiv payload).symm result) leftIdeal rightIdeal visible
    · funext serial
      exact candidates (.prepared serial)
  · funext slot
    exact candidates slot

private theorem advanceBind_focalReplayKey_congr
    (_runtime : GraphRuntime Player L Δ) (focal owner : Player) (name : VarId)
    {payload : L.Ty} (next : Graph Player L ((name, .sealed owner (R.result payload)) :: Γ) Δ)
    (leftIdeal rightIdeal : VEnv L Γ)
    (visible : observe focal leftIdeal = observe focal rightIdeal)
    (values : PublicValues Γ) (bindings : Bindings Player)
    (leftCandidates rightCandidates : CommitmentCandidates Player Slot (Raw L))
    (candidates : ∀ slot, leftCandidates.lookup (focal, slot) =
      rightCandidates.lookup (focal, slot)) (pc clock : Nat) (handle : Handle Player)
    (authorized : handle.1 = owner) :
    (advanceBind next leftIdeal values bindings leftCandidates pc clock handle).focalReplayKey
        focal =
      (advanceBind next rightIdeal values bindings rightCandidates pc clock handle).focalReplayKey
        focal := by
  have accepted (slot : Slot) :=
    accept_focal_lookup_congr focal leftCandidates rightCandidates candidates handle slot
  apply Prod.ext
  · by_cases owned : owner = focal
    · have handleFocal : handle.1 = focal := authorized.trans owned
      obtain ⟨handleOwner, handleSlot⟩ := handle
      simp only at handleFocal
      subst owner
      subst handleOwner
      have lookup : leftCandidates.lookup (focal, handleSlot) =
          rightCandidates.lookup (focal, handleSlot) := by
        exact candidates handleSlot
      change PlayerView.mk focal _ _ _ = PlayerView.mk focal _ _ _
      simp only
      rw [lookup]
      congr 1
      · exact observe_cons_same focal name (.sealed focal (R.result payload)) _
          leftIdeal rightIdeal visible
      · funext serial
        exact accepted (.prepared serial)
    · exact advanceBind_other_playerView_congr focal owner owned name payload next
        leftIdeal rightIdeal visible values bindings leftCandidates rightCandidates
        (fun serial => candidates (.prepared serial)) pc clock handle authorized
  · funext slot
    exact accepted slot

/-- A selected message has the same acceptance result and the same complete
focal replay projection at a synchronized cursor. Only a foreign sender's
selected opening needs an explicit verification-coherence premise. -/
theorem FocalReplayCheckpoint.handle_focalReplayKey_congr
    (runtime : GraphRuntime Player L Δ) (focal : Player)
    {left right : runtime.application.PolicyExecution}
    {suffix : Graph Player L Γ Δ}
    (checkpoint : FocalReplayCheckpoint runtime focal suffix left right)
    (message : Message Player (Payload Player L))
    (foreignOpening : ∀ site handle raw,
      message.payload = .opening site handle raw → message.sender ≠ focal →
      checkpoint.leftCandidates.verify handle raw =
        checkpoint.rightCandidates.verify handle raw) :
    Option.map (State.focalReplayKey focal)
        (runtime.handle left.native.application message) =
      Option.map (State.focalReplayKey focal)
        (runtime.handle right.native.application message) := by
  rcases message with ⟨⟨sender, serial⟩, payload⟩
  rw [checkpoint.leftState, checkpoint.rightState]
  cases suffix <;> cases payload <;> simp only [GraphRuntime.handle]
  · rename_i name owner payload fresh next site handle
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    by_cases accepted : (site = checkpoint.pc ∧ sender = owner) ∧ handle.1 = owner
    · have condition : (site = checkpoint.pc ∧
          ({ id := (sender, serial), payload := Payload.commitment site handle } :
            Message Player (Payload Player L)).sender = owner) ∧ handle.1 = owner := by
        simpa [Message.sender] using accepted
      rw [if_pos condition, if_pos condition]
      exact congrArg some (advanceBind_focalReplayKey_congr runtime focal owner name next
        checkpoint.leftIdeal checkpoint.rightIdeal checkpoint.focalObservation
        checkpoint.publicValues checkpoint.bindings checkpoint.leftCandidates
        checkpoint.rightCandidates checkpoint.focalCandidates checkpoint.pc checkpoint.clock
        handle accepted.2)
    · simp [Message.sender, accepted]
  · rename_i output owner binding payload fresh source checks next site handle raw
    by_cases senderOwner : sender = owner
    · by_cases handleOwner : handle.1 = owner
      · have verify : checkpoint.leftCandidates.verify handle raw =
            checkpoint.rightCandidates.verify handle raw := by
          by_cases focalSender : sender = focal
          · have handleFocal : handle.1 = focal := handleOwner.trans
                (senderOwner.symm.trans focalSender)
            obtain ⟨handlePrincipal, handleSlot⟩ := handle
            simp only at handleFocal
            subst handlePrincipal
            unfold CommitmentCandidates.verify
            rw [checkpoint.focalCandidates handleSlot]
          · exact foreignOpening site handle raw rfl focalSender
        simp only [Bool.and_eq_true, decide_eq_true_eq]
        rw [verify]
        by_cases accepted : (((site = checkpoint.pc ∧ sender = owner) ∧
            handle.1 = owner) ∧ lookupBinding checkpoint.bindings binding = some handle) ∧
            checkpoint.rightCandidates.verify handle raw = true
        · have condition :
              (((site = checkpoint.pc ∧
                ({ id := (sender, serial), payload := Payload.opening site handle raw } :
                  Message Player (Payload Player L)).sender = owner) ∧ handle.1 = owner) ∧
                lookupBinding checkpoint.bindings binding = some handle) ∧
                checkpoint.rightCandidates.verify handle raw = true := by
              simpa [Message.sender] using accepted
          rw [if_pos condition, if_pos condition]
          cases decoded : raw.as? (R.result payload) with
          | none => simp
          | some encoded =>
              simp only [Option.map_some]
              exact congrArg some
                (advanceResolve_focalReplayKey_congr runtime focal output next
                  checkpoint.leftIdeal checkpoint.rightIdeal checkpoint.focalObservation
                  checkpoint.publicValues checkpoint.bindings checkpoint.leftCandidates
                  checkpoint.rightCandidates checkpoint.focalCandidates checkpoint.pc
                  checkpoint.clock _)
        · simp [Message.sender, accepted]
      · simp [Message.sender, handleOwner]
    · simp [Message.sender, senderOwner]
  · rename_i output owner binding payload fresh source checks next site
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    by_cases accepted : site = checkpoint.pc ∧ sender = owner
    · have condition : site = checkpoint.pc ∧
          ({ id := (sender, serial), payload := Payload.withhold site } :
            Message Player (Payload Player L)).sender = owner := by
        simpa [Message.sender] using accepted
      rw [if_pos condition, if_pos condition]
      exact congrArg some (advanceResolve_focalReplayKey_congr runtime focal output next
        checkpoint.leftIdeal checkpoint.rightIdeal checkpoint.focalObservation
        checkpoint.publicValues checkpoint.bindings checkpoint.leftCandidates
        checkpoint.rightCandidates checkpoint.focalCandidates checkpoint.pc checkpoint.clock
        (.failure : PublicationResult (L.Val payload)))
    · simp [Message.sender, accepted]

end Vegas.GraphRuntime
