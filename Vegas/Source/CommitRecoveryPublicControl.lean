/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.CommitRecoveryPublicHistory

/-! # Exclusion updates read from actual public source successors -/

noncomputable section

namespace Vegas.SourceProgram

open GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

namespace ProtocolView

/-- Read the exclusion update from the original instruction cursor and its
next public result. This reads observations, not hidden declarations or a
second execution. Mismatched cursor shapes have no update. -/
def publicSuccessorExclusions (who : Player) :
    {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (program : SourceProgram Player L Γ O) →
      ProtocolView who program → ProtocolView who program → Finset Player → Finset Player
  | _, _, .ret _, _, _, excluded => excluded
  | _, _, .sample _ _ _ next, before, after, excluded =>
      before.elim (fun _ => excluded) fun before =>
        after.elim (fun _ => excluded) fun after =>
          publicSuccessorExclusions who next before after excluded
  | _, _, .commit _ _ _ _ next, before, after, excluded =>
      before.elim (fun _ => excluded) fun before =>
        after.elim (fun _ => excluded) fun after =>
          publicSuccessorExclusions who next before after excluded
  | _, _, .reveal (payload := payload) published owner _ _ _ _ next,
      before, after, excluded =>
      before.elim (fun _ => after.elim (fun _ => excluded) fun after =>
        match (entryView who next after).1.cells published (.publication payload) .here with
        | .failure => insert owner excluded
        | .success _ => excluded) fun before =>
          after.elim (fun _ => excluded) fun after =>
            publicSuccessorExclusions who next before after excluded

/-- At a reveal instruction, the public update reads precisely the newly
stored publication result, independently of all other source fields. -/
theorem publicSuccessorExclusions_reveal
    {Γ : SourceCtx Player L} {O : Finset VarId} {published name : VarId} {owner : Player}
    {payload : L.Ty} (who : Player) (fresh : published ∉ Γ.map Prod.fst)
    (selected : HasVar Γ name (.commitment owner payload)) (unresolved : name ∈ O)
    (next : SourceProgram Player L ((published, .publication payload) :: Γ) (O.erase name))
    (before : Config Player L Γ)
    (after : Config Player L ((published, .publication payload) :: Γ))
    (excluded : Finset Player) :
    publicSuccessorExclusions who (.reveal published owner name fresh selected unresolved next)
        (publicOnly who _ (ProtocolState.observe who _ (Sum.inl before)))
        (publicOnly who _ (ProtocolState.observe who _
          (Sum.inr (ProtocolState.entry next after)))) excluded =
      match after.state.get .here with
      | .failure => insert owner excluded
      | .success _ => excluded := by
  dsimp only [publicSuccessorExclusions, publicOnly, ProtocolState.observe, Sum.elim_inl,
    Sum.elim_inr]
  rw [entryView_publicOnly, entryView_observe_entry]
  rfl

end ProtocolView

/-- The public exclusion update follows the same actual structural source
suffix as the checkpoint; no private view or prior action word is supplied. -/
theorem ProtocolSuffix.publicSuccessorExclusions_lift
    {wholeΓ Γ : SourceCtx Player L} {wholeO O : Finset VarId}
    {whole : SourceProgram Player L wholeΓ wholeO} {program : SourceProgram Player L Γ O}
    {lift : ProtocolState program → ProtocolState whole}
    (origin : ProtocolSuffix whole program lift) :
    ∀ (who : Player) (first second : ProtocolState program) (excluded : Finset Player),
      ProtocolView.publicSuccessorExclusions who whole
          (ProtocolView.publicOnly who whole (ProtocolState.observe who whole (lift first)))
          (ProtocolView.publicOnly who whole (ProtocolState.observe who whole (lift second)))
          excluded =
        ProtocolView.publicSuccessorExclusions who program
          (ProtocolView.publicOnly who program (ProtocolState.observe who program first))
          (ProtocolView.publicOnly who program (ProtocolState.observe who program second))
          excluded := by
  induction origin with
  | initial => intro who first second excluded; rfl
  | sampleTail fresh law next previous ih =>
      intro who first second excluded
      exact ih who (Sum.inr first) (Sum.inr second) excluded
  | commitTail fresh guard next previous ih =>
      intro who first second excluded
      exact ih who (Sum.inr first) (Sum.inr second) excluded
  | revealTail fresh selected unresolved next previous ih =>
      intro who first second excluded
      exact ih who (Sum.inr first) (Sum.inr second) excluded
end Vegas.SourceProgram
