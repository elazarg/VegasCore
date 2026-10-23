/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Source.CommitRecoveryObservedClosure
import Vegas.Source.CommitRecoveryErasure

/-! # Full observations determined by a noncommitment public successor

A sample or reveal extends the immutable typed context by one public cell.
Its public result, the observer's prior full view and its own raw choice
therefore determine the full next view, including original action recall.
-/

noncomputable section

namespace Vegas.SourceProgram

open GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

namespace ProtocolView

/-- Public equality at a genuine entry retains all of that entry's public cells. -/
theorem publicOnly_entry_cells {Γ : SourceCtx Player L} {O : Finset VarId}
    (who : Player) (program : SourceProgram Player L Γ O)
    (first second : Config Player L Γ)
    (same : publicOnly who program (ProtocolState.observe who program
        (ProtocolState.entry program first)) =
      publicOnly who program (ProtocolState.observe who program
        (ProtocolState.entry program second))) :
    (first.view who).1.publicOnly = (second.view who).1.publicOnly := by
  cases program <;>
    simpa only [publicOnly, ProtocolState.observe, ProtocolState.entry, Sum.elim_inl,
      Sum.inl.injEq, Prod.mk.injEq, and_true] using same

end ProtocolView

namespace Config

omit [IExpr.ResultTypes L] in
/-- A public draw adds no private information beyond the observer's prior view. -/
theorem view_sample_congr {Γ : SourceCtx Player L} {payload : L.Ty}
    (who : Player) (name : VarId) (first second : Config Player L Γ)
    (left right : L.Val payload) (before : first.view who = second.view who)
    (after : ((sampleSuccessor name first left).view who).1.publicOnly =
      ((sampleSuccessor name second right).view who).1.publicOnly) :
    (sampleSuccessor name first left).view who =
      (sampleSuccessor name second right).view who := by
  apply Prod.ext
  · apply congrArg SourceObservation.mk
    funext cellName cell member
    cases member with
    | here =>
        exact congrArg (fun view => view.cells name (.publicData payload) .here) after
    | there member =>
        have old := congrArg
          (fun view : DecisionView who Γ => view.1.cells cellName cell member) before
        cases cell <;> exact old
  · change first.history who = second.history who
    exact congrArg (fun view : DecisionView who Γ => view.2) before

omit [IExpr.ResultTypes L] in
/-- A reveal's public result and the observer's own disclosure choice determine
its full next view even when hidden guard registries differ. -/
theorem view_reveal_congr {Γ : SourceCtx Player L} {name : VarId}
    {owner : Player} {payload : L.Ty} (who : Player) (published : VarId)
    (selected : HasVar Γ name (.commitment owner payload))
    (first second : Config Player L Γ) (left right : Bool)
    (before : first.view who = second.view who) (own : owner = who → left = right)
    (after : ((revealSuccessor published selected first left).view who).1.publicOnly =
      ((revealSuccessor published selected second right).view who).1.publicOnly) :
    (revealSuccessor published selected first left).view who =
      (revealSuccessor published selected second right).view who := by
  apply Prod.ext
  · apply congrArg SourceObservation.mk
    funext cellName cell member
    cases member with
    | here =>
        exact congrArg (fun view => view.cells published (.publication payload) .here) after
    | there member =>
        have old := congrArg
          (fun view : DecisionView who Γ => view.1.cells cellName cell member) before
        cases cell <;> exact old
  · by_cases equal : owner = who
    · subst owner
      simp only [Config.view, revealSuccessor, Function.update_self]
      have past : first.history who = second.history who := congrArg Prod.snd before
      rw [past, own rfl]
    · simp only [Config.view, revealSuccessor, Function.update_of_ne (Ne.symm equal)]
      exact congrArg (fun view : DecisionView who Γ => view.2) before

end Config

namespace ProtocolState

/-- At an actual sample or reveal, matching public results and the observer's
own raw coordinate preserve its complete source view and original recall. -/
theorem recoveryStep_noncommit_observe_congr (who : Player) :
    ∀ {Γ : SourceCtx Player L} {O : Finset VarId}
      (program : SourceProgram Player L Γ O) (first second : ProtocolState program),
      observe who program first = observe who program second →
      atCommit program first = false →
      ∀ (excluded : Finset Player)
        (left right : Player → Option (CommitRecoveryMove Player L)), left who = right who →
      ∀ l ∈ (recoveryStep program first excluded left).support,
      ∀ r ∈ (recoveryStep program second excluded right).support,
        ProtocolView.publicOnly who program (observe who program l.1) =
          ProtocolView.publicOnly who program (observe who program r.1) →
        observe who program l.1 = observe who program r.1
  | _, _, .ret _, first, second, before, _, _, _, _, _, l, lm, r, rm, _ => by
      simp only [recoveryStep, PMF.mem_support_pure_iff] at lm rm
      subst l; subst r
      exact before
  | _, _, .sample name _ _ next, first, second, before, notCommit,
      excluded, left, right, own, l, lm, r, rm, after => by
      cases first with
      | inl first =>
          cases second with
          | inr _ => cases before
          | inl second =>
              obtain ⟨lv, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp lm
              obtain ⟨rv, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp rm
              apply congrArg Sum.inr
              apply observe_entry_congr
              apply Config.view_sample_congr who name first second lv rv (Sum.inl.inj before)
              exact ProtocolView.publicOnly_entry_cells who next _ _ (Sum.inr.inj after)
      | inr first =>
          cases second with
          | inl _ => cases before
          | inr second =>
              simp only [recoveryStep, Sum.elim_inr] at lm rm
              obtain ⟨lowerLeft, lowerLeftMember, leftShape⟩ := (PMF.mem_support_map_iff
                (fun result : ProtocolState next × Finset Player => (Sum.inr result.1, result.2))
                (recoveryStep next first excluded left) _).mp lm
              obtain ⟨lowerRight, lowerRightMember, rightShape⟩ := (PMF.mem_support_map_iff
                (fun result : ProtocolState next × Finset Player => (Sum.inr result.1, result.2))
                (recoveryStep next second excluded right) _).mp rm
              subst l; subst r
              exact congrArg Sum.inr (recoveryStep_noncommit_observe_congr who next first second
                (Sum.inr.inj before) notCommit excluded left right own
                lowerLeft lowerLeftMember lowerRight lowerRightMember
                (Sum.inr.inj after))
  | _, _, .commit _ _ _ _ next, first, second, before, notCommit,
      excluded, left, right, own, l, lm, r, rm, after => by
      cases first with
      | inl _ => cases notCommit
      | inr first =>
          cases second with
          | inl _ => cases before
          | inr second =>
              simp only [recoveryStep, Sum.elim_inr] at lm rm
              obtain ⟨lowerLeft, lowerLeftMember, leftShape⟩ := (PMF.mem_support_map_iff
                (fun result : ProtocolState next × Finset Player => (Sum.inr result.1, result.2))
                (recoveryStep next first excluded left) _).mp lm
              obtain ⟨lowerRight, lowerRightMember, rightShape⟩ := (PMF.mem_support_map_iff
                (fun result : ProtocolState next × Finset Player => (Sum.inr result.1, result.2))
                (recoveryStep next second excluded right) _).mp rm
              subst l; subst r
              exact congrArg Sum.inr (recoveryStep_noncommit_observe_congr who next first second
                (Sum.inr.inj before) notCommit excluded left right own
                lowerLeft lowerLeftMember lowerRight lowerRightMember
                (Sum.inr.inj after))
  | _, _, .reveal published owner _ _ selected _ next, first, second, before, notCommit,
      excluded, left, right, own, l, lm, r, rm, after => by
      cases first with
      | inl first =>
          cases second with
          | inr _ => cases before
          | inl second =>
              simp only [recoveryStep, Sum.elim_inl, PMF.mem_support_pure_iff] at lm rm
              subst l; subst r
              apply congrArg Sum.inr
              apply observe_entry_congr
              have old := Sum.inl.inj before
              have publicCells :=
                ProtocolView.publicOnly_entry_cells who next _ _ (Sum.inr.inj after)
              by_cases inactive : owner ∈ excluded
              · simp only [ite_eq_left inactive] at publicCells ⊢
                apply Prod.ext
                · apply congrArg SourceObservation.mk
                  funext cellName cell member
                  cases member with
                  | here => exact congrArg (fun view => view.cells _ _ .here) publicCells
                  | there member =>
                      have seen := congrArg
                        (fun view => view.1.cells cellName cell member) old
                      cases cell <;> exact seen
                · change first.history who = second.history who
                  exact congrArg Prod.snd old
              · simp only [ite_eq_right inactive] at publicCells ⊢
                exact Config.view_reveal_congr who published selected first second _ _ old
                  (fun equal => by subst owner; rw [own]) publicCells
      | inr first =>
          cases second with
          | inl _ => cases before
          | inr second =>
              simp only [recoveryStep, Sum.elim_inr] at lm rm
              obtain ⟨lowerLeft, lowerLeftMember, leftShape⟩ := (PMF.mem_support_map_iff
                (fun result : ProtocolState next × Finset Player => (Sum.inr result.1, result.2))
                (recoveryStep next first excluded left) _).mp lm
              obtain ⟨lowerRight, lowerRightMember, rightShape⟩ := (PMF.mem_support_map_iff
                (fun result : ProtocolState next × Finset Player => (Sum.inr result.1, result.2))
                (recoveryStep next second excluded right) _).mp rm
              subst l; subst r
              exact congrArg Sum.inr (recoveryStep_noncommit_observe_congr who next first second
                (Sum.inr.inj before) notCommit excluded left right own
                lowerLeft lowerLeftMember lowerRight lowerRightMember
                (Sum.inr.inj after))

end ProtocolState

end Vegas.SourceProgram
