/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.CommitRecoveryPublicSuccessor
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

namespace ProtocolState

/-- Every actual noncommitment successor has exactly the exclusion set read
from its public next result: samples keep the set and a failed publication
adds precisely its original owner. -/
theorem recoveryStep_noncommit_public_excluded (who : Player) :
    ∀ {Γ : SourceCtx Player L} {O : Finset VarId}
      (program : SourceProgram Player L Γ O) (point : ProtocolState program),
      atCommit program point = false →
      ∀ (excluded : Finset Player) (joint : Player → Option (CommitRecoveryMove Player L)),
      ∀ result ∈ (recoveryStep program point excluded joint).support,
        result.2 = ProtocolView.publicSuccessorExclusions who program
          (ProtocolView.publicOnly who program (observe who program point))
          (ProtocolView.publicOnly who program (observe who program result.1)) excluded
  | _, _, .ret _, _, _, _, _, result, supported => by
      simp only [recoveryStep, PMF.mem_support_pure_iff] at supported
      subst result
      rfl
  | _, _, .sample _ _ _ next, point, notCommit, excluded, joint, result, supported => by
      cases point with
      | inl _ =>
          obtain ⟨_value, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
          rfl
      | inr point =>
          obtain ⟨lower, member, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
          exact recoveryStep_noncommit_public_excluded who next point notCommit
            excluded joint lower member
  | _, _, .commit _ _ _ _ next, point, notCommit, excluded, joint, result, supported => by
      cases point with
      | inl _ => cases notCommit
      | inr point =>
          obtain ⟨lower, member, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
          exact recoveryStep_noncommit_public_excluded who next point notCommit
            excluded joint lower member
  | _, _, .reveal published owner _ _ selected _ next,
      point, notCommit, excluded, joint, result, supported => by
      cases point with
      | inl config =>
          simp only [recoveryStep, Sum.elim_inl, PMF.mem_support_pure_iff] at supported
          subst result
          dsimp only [ProtocolView.publicSuccessorExclusions, observe, ProtocolView.publicOnly,
            Sum.elim_inl, Sum.elim_inr]
          rw [ProtocolView.entryView_publicOnly, ProtocolView.entryView_observe_entry]
          dsimp only [Config.view, SourceObservation.publicOnly, sourceObserve]
          split_ifs <;> rfl
      | inr point =>
          obtain ⟨lower, member, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
          exact recoveryStep_noncommit_public_excluded who next point notCommit
            excluded joint lower member

/-- Equal prior and next public observations determine the same noncommitment
exclusion update without requiring equality of private source views. -/
theorem recoveryStep_noncommit_public_excluded_eq (who : Player)
    {Γ : SourceCtx Player L} {O : Finset VarId}
    (program : SourceProgram Player L Γ O) (first second : ProtocolState program)
    (before : ProtocolView.publicOnly who program (observe who program first) =
      ProtocolView.publicOnly who program (observe who program second))
    (notCommit : atCommit program first = false)
    (excluded : Finset Player) (left right : Player → Option (CommitRecoveryMove Player L))
    (l : ProtocolState program × Finset Player)
    (lm : l ∈ (recoveryStep program first excluded left).support)
    (r : ProtocolState program × Finset Player)
    (rm : r ∈ (recoveryStep program second excluded right).support)
    (after : ProtocolView.publicOnly who program (observe who program l.1) =
      ProtocolView.publicOnly who program (observe who program r.1)) : l.2 = r.2 := by
  have control := (public_control who program first second before).2.1
  have secondNotCommit : atCommit program second = false := control ▸ notCommit
  rw [recoveryStep_noncommit_public_excluded who program first notCommit excluded left l lm,
    recoveryStep_noncommit_public_excluded who program second secondNotCommit excluded right r rm,
    before, after]

end ProtocolState
end Vegas.SourceProgram
