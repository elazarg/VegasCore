/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseProposalCommitReadback
import Vegas.Game.CompiledCommitAttemptSplit
import Vegas.Pending.PhaseRecordedBindingMaterial
import Vegas.Pending.PhaseBindingFreshness

/-! # Emitted typed values at their exact rank in the whole decoded attempt -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime
open Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {wholeΓ : SourceCtx Player L} {wholeO : Finset VarId}
  (whole : SourceProgram Player L wholeΓ wholeO) (mode : ExecutionMode)

/-- A typed admitted value belongs to its original rank in the SAME complete
decoded word. The middle configuration and exclusion set are the actual
earlier decoder, including every inherited automatic coordinate. -/
theorem decodeCommitAttempt_joint_at_typed_admission
    {Γ Δ Ξ : SourceCtx Player L} {O P Q : Finset VarId}
    {name : VarId} {owner : Player} {payload : L.Ty}
    (earlier : CommitPrefix Γ O Δ P) (fresh : name ∉ Δ.map Prod.fst)
    (guard : SourceGuard L Δ owner name payload)
    (rest : CommitPrefix ((name, .commitment owner payload) :: Δ) (insert name P) Ξ Q)
    (suffix : SourceProgram Player L Ξ Q)
    (embedding : OutputEmbedding (inputLayout wholeΓ) (outputLayout whole)
      ((earlier.append (.commit name owner fresh guard rest)).prepend suffix))
    (offset : Nat) (ranked : ∀ index, (embedding.event index).val = offset + index.val)
    (selected : Fin (eventCount
      ((earlier.append (.commit name owner fresh guard rest)).prepend suffix)))
    (atRank : selected.val = earlier.length)
    (native : EventGraphRuntime.State ((toEventGraph whole).withMode mode))
    (entry : SourceProgram.Config Player L Γ) (excluded : Finset Player)
    (source : CommitRecoveryState whole)
    (candidate : Handle ((toEventGraph whole).withMode mode)) (value : L.Val payload)
    (admitted : native.accepted (.inr (embedding.event selected)) = some candidate)
    (meaning : native.bindingResult candidate payload = .success value) :
    let later : CommitPrefix Δ P Ξ Q := .commit name owner fresh guard rest
    let prefixEmbedding := cast
      (congrArg (OutputEmbedding (inputLayout wholeΓ) (outputLayout whole))
        (earlier.prepend_append later suffix)) embedding
    let middle := decodeCommitAttempt whole mode earlier (later.prepend suffix) prefixEmbedding
      native entry excluded
    let complete := decodeCommitAttempt whole mode (earlier.append later) suffix embedding native
      entry excluded
    source.excluded = middle.2.1 →
      complete.2.2.joints[earlier.length]? =
        some (source.commitJoint owner name payload (.success value) false) := by
  intro later prefixEmbedding middle complete inherited
  obtain ⟨tailEmbedding, _sameConfig, _sameExcluded, word, positioned⟩ :=
    decodeCommitAttempt_append whole mode earlier later suffix embedding native entry excluded
  let zero : Fin (eventCount (later.prepend suffix)) :=
    ⟨0, by simp only [later, CommitPrefix.prepend, eventCount]; omega⟩
  have event : tailEmbedding.event zero = embedding.event selected := by
    apply Fin.ext
    rw [positioned offset ranked zero, ranked selected, atRank]
    simp only [zero, Nat.add_zero]
  have found : native.accepted (.inr (tailEmbedding.event zero)) = some candidate := by
    rw [event]
    exact admitted
  let head : CommitPrefix Δ P ((name, .commitment owner payload) :: Δ) (insert name P) :=
    .commit name owner fresh guard .nil
  have headWord : (decodeCommitAttempt whole mode head (rest.prepend suffix) tailEmbedding
      native middle.1 middle.2.1).2.2.joints =
        [source.commitJoint owner name payload (.success value) false] := by
    rw [← inherited]
    exact decodeCommitAttempt_head_joints_of_typed_admission whole mode fresh guard
      (rest.prepend suffix) tailEmbedding native middle.1 source candidate value found meaning
  have tailWord := (decodeCommitAttempt_commit_tail whole mode fresh guard rest suffix
    tailEmbedding native middle.1 middle.2.1).2.2
  change complete.2.2.joints[earlier.length]? = _
  rw [word, tailWord, headWord]
  have length := middle.2.2.joints_length
  rw [← length, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
  rfl

/-- The actual recalled SEND supplies the value at its original rank in the
complete decoder. The native image may be the pre-normalization phase image:
only its literal preserved catalogue and admitted handle are required. No
current-phase origin or newly selected source counterpart is assumed. -/
theorem decodeCommitAttempt_joint_of_recorded_preparation [Fintype Player]
    {Γ Δ Ξ : SourceCtx Player L} {O P Q : Finset VarId}
    {name : VarId} {owner : Player} {payload : L.Ty}
    (earlier : CommitPrefix Γ O Δ P) (fresh : name ∉ Δ.map Prod.fst)
    (guard : SourceGuard L Δ owner name payload)
    (rest : CommitPrefix ((name, .commitment owner payload) :: Δ) (insert name P) Ξ Q)
    (suffix : SourceProgram Player L Ξ Q)
    (embedding : OutputEmbedding (inputLayout wholeΓ) (outputLayout whole)
      ((earlier.append (.commit name owner fresh guard rest)).prepend suffix))
    (offset : Nat) (ranked : ∀ index, (embedding.event index).val = offset + index.val)
    (selected : Fin (eventCount
      ((earlier.append (.commit name owner fresh guard rest)).prepend suffix)))
    (atRank : selected.val = earlier.length)
    (runtime : EventGraphRuntime ((toEventGraph whole).withMode mode))
    (leaks : MessageNetwork.ObservationRule Player
      (CommitAttemptPacket ((toEventGraph whole).withMode mode)))
    (bounds : MessageBounds ((toEventGraph whole).withMode mode))
    (plan : RuntimePhasePlan ((toEventGraph whole).withMode mode))
    (inputs : PMF ((toEventGraph whole).withMode mode).Inputs) (horizon : Nat)
    (scheduler : (phaseApplication runtime leaks).Scheduler)
    (control : (phaseApplication runtime leaks).Control)
    (trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some control))
    (native : EventGraphRuntime.State ((toEventGraph whole).withMode mode))
    (catalogue : native.candidates = control.execution.application.current.native.candidates)
    (entry : SourceProgram.Config Player L Γ) (excluded : Finset Player)
    (source : CommitRecoveryState whole) (serial : Nat) (value : L.Val payload)
    (admitted : native.accepted (.inr (embedding.event selected)) =
      some (owner, .prepared serial))
    (opening : Option (Raw L)) (evidence : EvidenceRequest ((toEventGraph whole).withMode mode))
    (record : (phaseApplication runtime leaks).PlayerEntry)
    (recorded : record ∈ control.execution.recall owner)
    (declared : record.action = ⟨some
      ⟨⟨.commitment (embedding.event selected) (owner, .prepared serial), opening⟩, evidence⟩⟩)
    (prepared : (opening.bind fun raw => raw.as? payload) = some value) :
    let later : CommitPrefix Δ P Ξ Q := .commit name owner fresh guard rest
    let prefixEmbedding := cast
      (congrArg (OutputEmbedding (inputLayout wholeΓ) (outputLayout whole))
        (earlier.prepend_append later suffix)) embedding
    let middle := decodeCommitAttempt whole mode earlier (later.prepend suffix) prefixEmbedding
      native entry excluded
    let complete := decodeCommitAttempt whole mode (earlier.append later) suffix embedding native
      entry excluded
    source.excluded = middle.2.1 →
      complete.2.2.joints[earlier.length]? =
        some (source.commitJoint owner name payload (.success value) false) := by
  let initial := inputs.map (PhaseRuntimeState.initial plan)
  let menu := PhaseCount.onePacketMenu runtime leaks bounds
  obtain ⟨before, prior, _prefix, _acting, viewed, offered, _recalled⟩ :=
    menu.recorded_response_prefix initial horizon scheduler control trace owner record recorded
  rw [declared] at offered
  have freshHere : record.beforeView.application.1.candidates (.prepared serial) = .fresh :=
    viewed ▸ PhaseCount.onePacket_binding_fresh runtime leaks bounds plan inputs horizon scheduler
      prior owner (embedding.event selected) serial opening evidence offered
  have meaning := phase_recorded_material_binding_result runtime leaks menu initial horizon
    scheduler control trace owner (embedding.event selected) payload serial opening evidence record
      recorded declared freshHere
  rw [prepared, Option.elim_some] at meaning
  have actual : native.bindingResult (owner, .prepared serial) payload = .success value := by
    simpa only [State.bindingResult, catalogue] using meaning
  exact decodeCommitAttempt_joint_at_typed_admission whole mode earlier fresh guard rest suffix
    embedding offset ranked selected atRank native entry excluded source (owner, .prepared serial)
      value admitted actual

end Vegas
