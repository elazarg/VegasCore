/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseProposalReadback

/-! # Recorded native disclosure evidence along source replay -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

/-- A genuine active source disclosure retains the actual native completion
that selected its Boolean action. Failure of its guard does not remove it. -/
def NativeDisclosureReadback {graph : Vegas.EventGraph Player L}
    {Γ : SourceCtx Player L} {O : Finset VarId}
    (native : EventGraphRuntime.State graph) (offset : Nat)
    (program : SourceProgram Player L Γ O) (point : ProtocolState program)
    (excluded : Finset Player) (joint : Player → Option (CommitRecoveryMove Player L)) : Prop :=
  ∀ owner, ProtocolState.actor program point = some owner → owner ∉ excluded →
    OwnAction.disclosure ((joint owner).map (·.action)) = true →
    ∃ (event : graph.EventId) (payload : L.Ty)
      (publication : graph.outputLayout event = .publication payload)
      (action : (graph.outputLayout event).Action),
      event.val = offset + (instructionCount program - ProtocolState.remaining program point) ∧
      ⟨event, action⟩ ∈ native.config.history ∧
      cast (congrArg EventField.Action publication) action = true

theorem NativeDisclosureReadback.of_disclosure_eq {graph : Vegas.EventGraph Player L}
    {Γ : SourceCtx Player L} {O : Finset VarId}
    (native : EventGraphRuntime.State graph) (offset : Nat)
    (program : SourceProgram Player L Γ O) (point : ProtocolState program)
    (excluded : Finset Player) (first second : Player → Option (CommitRecoveryMove Player L))
    (readback : NativeDisclosureReadback native offset program point excluded first)
    (same : ∀ owner, ProtocolState.actor program point = some owner → owner ∉ excluded →
      OwnAction.disclosure ((second owner).map (·.action)) =
        OwnAction.disclosure ((first owner).map (·.action))) :
    NativeDisclosureReadback native offset program point excluded second := by
  intro owner acting surviving disclosed
  exact readback owner acting surviving ((same owner acting surviving).symm.trans disclosed)

theorem NativeDisclosureReadback.lift {graph : Vegas.EventGraph Player L}
    {wholeΓ Γ : SourceCtx Player L} {wholeO O : Finset VarId}
    {whole : SourceProgram Player L wholeΓ wholeO} {program : SourceProgram Player L Γ O}
    {embed : ProtocolState program → ProtocolState whole}
    (origin : ProtocolSuffix whole program embed)
    (native : EventGraphRuntime.State graph) (outerOffset offset : Nat)
    (aligned : outerOffset + instructionCount whole = offset + instructionCount program)
    (point : ProtocolState program) (excluded : Finset Player)
    (joint : Player → Option (CommitRecoveryMove Player L))
    (readback : NativeDisclosureReadback native offset program point excluded joint) :
    NativeDisclosureReadback native outerOffset whole (embed point) excluded joint := by
  intro owner acting surviving disclosed
  rw [origin.actor_lift] at acting
  obtain ⟨event, payload, publication, action, ranked, recorded, selected⟩ :=
    readback owner acting surviving disclosed
  refine ⟨event, payload, publication, action, ?_, recorded, selected⟩
  have remaining := origin.remaining_lift point
  have bounded := ProtocolState.remaining_le_instructionCount program point
  have wholeBounded := ProtocolState.remaining_le_instructionCount whole (embed point)
  omega

/-- The disclosure certificate is extracted from the completion already used
by the compiler's source successor calculation. -/
theorem nativeDisclosureReadback_reveal {graph : Vegas.EventGraph Player L}
    {Γ : SourceCtx Player L} {O : Finset VarId}
    {published name : VarId} {owner : Player} {payload : L.Ty}
    (fresh : published ∉ Γ.map Prod.fst)
    (source : HasVar Γ name (.commitment owner payload)) (unresolved : name ∈ O)
    (next : SourceProgram Player L ((published, .publication payload) :: Γ) (O.erase name))
    (native : EventGraphRuntime.State graph) (offset : Nat) (event : graph.EventId)
    (ranked : event.val = offset) (config : Config Player L Γ) (excluded : Finset Player)
    (publication : graph.outputLayout event = .publication payload)
    (action : (graph.outputLayout event).Action) (disclose : Bool)
    (recorded : ⟨event, action⟩ ∈ native.config.history)
    (selected : cast (congrArg EventField.Action publication) action = disclose) :
    NativeDisclosureReadback native offset
      (.reveal published owner name fresh source unresolved next) (.inl config) excluded
      (Function.update (fun _ => none) owner
        (some ⟨.reveal owner name disclose, false⟩)) := by
  intro who acting _surviving disclosed
  have same : owner = who := Option.some.inj acting
  subst who
  simp only [Function.update_self, Option.map_some, OwnAction.disclosure] at disclosed
  refine ⟨event, payload, publication, action, ?_, recorded, selected.trans disclosed⟩
  simpa only [instructionCount, ProtocolState.remaining, Sum.elim_inl,
    Nat.sub_self, Nat.add_zero] using ranked

end Vegas
