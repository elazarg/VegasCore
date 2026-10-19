/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.CommitRecoveryBindingSubstitution
import Vegas.Source.ProposalRecoveryObservation
import Vegas.Source.CommitRecoveryValueMenu

/-! # Selective repair of generated unusable source preparations

Only active nonmissing failed declarations are replaced. Initial cells,
omissions and automatic excluded-owner fields remain literal.
-/

noncomputable section

namespace Vegas.SourceProgram

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

namespace Config

omit [IExpr.ResultTypes L] in
/-- Extending both stores with the same declaration leaves that declaration
unpatched, even when it is an actual omission represented by failure. -/
theorem FocalRepair.commit_kept {who : Player} {Γ : SourceCtx Player L}
    {original repaired : Config Player L Γ} (related : FocalRepair who original repaired)
    (name : VarId) (owner : Player) (payload : L.Ty)
    (guard : SourceGuard L Γ owner name payload)
    (binding : PublicationResult (L.Val payload)) :
    FocalRepair who (commitSuccessor name guard original binding)
      (commitSuccessor name guard repaired binding) := by
  obtain ⟨unpatch, patched, invariant, registry, revelations⟩ := related
  let fixed : PatchMap who ((name, .commitment owner payload) :: Γ) := fun selected _ =>
    match selected with
    | .here => false
    | .there prior => patched prior (sourceObserve who repaired.state, repaired.history who)
  refine ⟨fun _ => (commitSuccessor name guard original binding).view who, fixed, ?_, ?_, ?_⟩
  · constructor
    · intro _ _ selected
      cases selected with | there selected => exact invariant.publicEq selected
    · intro _ _ _ selected
      cases selected with | there selected => exact invariant.inputEq selected
    · intro _ _ selected
      cases selected with | there selected => exact invariant.publicationEq selected
    · intro _ _ _ selected outside
      cases selected with
      | here => rfl
      | there selected => exact invariant.foreignEq selected outside
    · intro _ _ selected changed
      cases selected with
      | here => cases changed
      | there selected => exact invariant.replacedEq selected changed
    · intro _ _ selected unchanged
      cases selected with
      | here => rfl
      | there selected => exact invariant.keptEq selected unchanged
    · intro other outside
      by_cases acts : other = owner
      · subst other
        simp only [commitSuccessor, Function.update_self, invariant.historyEq _ outside]
      · simp only [commitSuccessor, Function.update_of_ne acts, invariant.historyEq _ outside]
    · rfl
  · simp only [commitSuccessor, registry]
  · exact congrArg Revelations.weaken revelations

/-- Only a failed stored binding suppresses the repaired author's disclosure.
A successful original binding, including a guard-rejected one, remains literal. -/
def preparationDisclosure (who owner : Player) {Γ : SourceCtx Player L} {name : VarId}
    {payload : L.Ty} (config : Config Player L Γ)
    (source : HasVar Γ name (.commitment owner payload)) (disclose : Bool) : Bool :=
  if owner = who then match config.state.get source with
    | .failure => false
    | .success _ => disclose
  else disclose

omit [IExpr.ResultTypes L] in
/-- Selective disclosure preserves the actual public guard result while
allowing the repaired author to be excluded by that very transition. -/
theorem FocalRepair.reveal_preparation {who owner : Player} {Γ : SourceCtx Player L}
    {name : VarId} {payload : L.Ty} {original repaired : Config Player L Γ}
    (related : FocalRepair who original repaired) (published : VarId)
    (source : HasVar Γ name (.commitment owner payload)) (disclose : Bool) :
    FocalRepair who (revealSuccessor published source original disclose)
      (revealSuccessor published source repaired
        (preparationDisclosure who owner original source disclose)) := by
  obtain ⟨unpatch, patched, invariant, registry, revelations⟩ := related
  have proposal :
      (if preparationDisclosure who owner original source disclose then
        repaired.state.get source else .failure) =
      (if disclose then original.state.get source else .failure) := by
    by_cases own : owner = who
    · subst owner
      cases bound : original.state.get source with
      | failure => simp [preparationDisclosure, bound]
      | success value =>
          have notPatched : patched source (sourceObserve who repaired.state,
              repaired.history who) = false := by
            cases marked : patched source (sourceObserve who repaired.state,
                repaired.history who) with
            | false => rfl
            | true =>
                have failed := (invariant.replacedEq source marked).1
                rw [bound] at failed
                cases failed
          rw [invariant.keptEq source notPatched]
          simp [preparationDisclosure, bound]
    · rw [invariant.foreignEq source own]
      simp only [preparationDisclosure, own, ↓reduceIte]
  have accepted (value : PublicationResult (L.Val payload)) :
      (repaired.registry.completedBy (published := published) repaired.revelations source).all
        (·.accepts (Revelations.reveal (@repaired.revelations) (published := published) source)
          (Env.cons value repaired.state)) =
      (original.registry.completedBy (published := published) original.revelations source).all
        (·.accepts (Revelations.reveal (@original.revelations) (published := published) source)
          (Env.cons value original.state)) := by
    rw [registry, revelations]
    refine congrArg (List.all _) (funext fun obligation => ?_)
    exact Obligation.accepts_congr obligation _ _ _
      (fun cell => match cell with | .there prior => invariant.publicEq prior)
      (fun cell => match cell with
        | .here => rfl
        | .there prior => invariant.publicationEq prior)
  have result : (revealSuccessor published source repaired
        (preparationDisclosure who owner original source disclose)).state.get .here =
      (revealSuccessor published source original disclose).state.get .here := by
    simp only [revealSuccessor, Env.cons_get_here]
    rw [proposal, accepted]
  simp only [revealSuccessor, Env.cons_get_here] at result
  by_cases own : owner = who
  · subst owner
    refine ⟨unpatch.afterReveal (decide (who = who)) published name who payload
        (fun _ => some disclose),
      patched.afterReveal (decide (who = who)) published payload, ?_, ?_, ?_⟩
    · simpa only [revealSuccessor, Env.cons_get_here, result] using
        patched_reveal_own invariant published name payload
          ((revealSuccessor published source original disclose).state.get .here)
          disclose (preparationDisclosure who who original source disclose)
          (fun _ => some disclose) rfl
    · simpa only [revealSuccessor] using congrArg Registry.weaken registry
    · simp only [revealSuccessor, revelations]
  · have changed : preparationDisclosure who owner original source disclose = disclose := by
      simp only [preparationDisclosure, own, ↓reduceIte]
    have corrected := result
    rw [changed] at corrected
    refine ⟨unpatch.afterReveal (decide (owner = who)) published name owner payload
        (fun _ => none),
      patched.afterReveal (decide (owner = who)) published payload, ?_, ?_, ?_⟩
    · simpa only [revealSuccessor, Env.cons_get_here, changed, corrected] using
        patched_reveal_foreign invariant published name owner payload own
          ((revealSuccessor published source original disclose).state.get .here)
          disclose (fun _ => none)
    · simpa only [revealSuccessor] using congrArg Registry.weaken registry
    · simp only [revealSuccessor, revelations]

end Config

/-- The semantic translation preserves omissions and changes only a
nonmissing unusable preparation of the designated owner. -/
def repairPreparationAtom (owner who : Player) (payload : L.Ty)
    (atom : L.Val payload ⊕ Bool) : L.Val payload ⊕ Bool :=
  if owner = who then match atom with
    | .inr false => .inl (L.someValue payload)
    | atom => atom
  else atom

omit [IExpr.ResultTypes L] in
@[simp] theorem repairPreparationAtom_missing (owner who : Player) (payload : L.Ty)
    (atom : L.Val payload ⊕ Bool) (name : VarId) :
    (CommitRecoveryMove.bindingAtom owner name payload
      (repairPreparationAtom owner who payload atom)).missing =
      (CommitRecoveryMove.bindingAtom owner name payload atom).missing := by
  by_cases own : owner = who
  · cases atom with
    | inl => simp [repairPreparationAtom, own, CommitRecoveryMove.bindingAtom]
    | inr bit => cases bit <;>
        simp [repairPreparationAtom, own, CommitRecoveryMove.bindingAtom]
  · simp [repairPreparationAtom, own]

namespace ProtocolState

/-- A deterministic transformation of the ACTUAL enriched joint move.
Failed reveal contents are never manufactured from the repaired typed cell. -/
def repairPreparationJoint (who : Player) :
    ∀ {Γ : SourceCtx Player L} {O : Finset VarId}
      (program : SourceProgram Player L Γ O), ProtocolState program →
      (Player → Option (ProposalRecoveryMove Player L)) →
      Player → Option (ProposalRecoveryMove Player L)
  | _, _, .ret _, _, joint => joint
  | _, _, .sample _ _ _ next, point, joint => point.elim (fun _ => joint)
      (fun later => repairPreparationJoint who next later joint)
  | _, _, .commit (payload := payload) name owner _ _ next, point, joint => point.elim
      (fun _ => if owner = who then Function.update joint owner ((joint owner).map fun move =>
        if move.semantic.missing then move else
          match OwnAction.binding owner name payload (some move.semantic.action) with
          | .failure => ⟨⟨.commit owner name payload (.success (L.someValue payload)), false⟩,
              false⟩
          | .success _ => move)
        else joint)
      (fun later => repairPreparationJoint who next later joint)
  | _, _, .reveal _ owner name _ source _ next, point, joint => point.elim
      (fun config => if owner = who then
        match config.state.get source with
        | .failure => Function.update joint owner ((joint owner).map fun _ =>
            ⟨⟨.reveal owner name false, false⟩, false⟩)
        | .success _ => joint
        else joint)
      (fun later => repairPreparationJoint who next later joint)

/-- Semantic form of the selective joint transformation. -/
def repairPreparationRawJoint (who : Player) :
    ∀ {Γ : SourceCtx Player L} {O : Finset VarId}
      (program : SourceProgram Player L Γ O), ProtocolState program →
      (Player → Option (CommitRecoveryMove Player L)) →
      Player → Option (CommitRecoveryMove Player L)
  | _, _, .ret _, _, joint => joint
  | _, _, .sample _ _ _ next, point, joint => point.elim (fun _ => joint)
      (fun later => repairPreparationRawJoint who next later joint)
  | _, _, .commit (payload := payload) name owner _ _ next, point, joint => point.elim
      (fun _ => if owner = who then Function.update joint owner ((joint owner).map fun move =>
        if move.missing then move else
          match OwnAction.binding owner name payload (some move.action) with
          | .failure => ⟨.commit owner name payload (.success (L.someValue payload)), false⟩
          | .success _ => move)
        else joint)
      (fun later => repairPreparationRawJoint who next later joint)
  | _, _, .reveal _ owner name _ source _ next, point, joint => point.elim
      (fun config => if owner = who then
        match config.state.get source with
        | .failure => Function.update joint owner ((joint owner).map fun _ =>
            ⟨.reveal owner name false, false⟩)
        | .success _ => joint
        else joint)
      (fun later => repairPreparationRawJoint who next later joint)

/-- No other owner's literal source action or label is changed. -/
theorem repairPreparationJoint_foreign (who observer : Player) :
    ∀ {Γ : SourceCtx Player L} {O : Finset VarId}
      (program : SourceProgram Player L Γ O) (point : ProtocolState program)
      (joint : Player → Option (ProposalRecoveryMove Player L)),
      observer ≠ who →
        repairPreparationJoint who program point joint observer = joint observer := by
  intro Γ O program
  induction program with
  | ret => intros; rfl
  | sample _ _ _ next ih =>
      intro point joint outside
      cases point with
      | inl => rfl
      | inr point => exact ih point joint outside
  | commit name owner fresh guard next ih =>
      intro point joint outside
      cases point with
      | inr point => exact ih point joint outside
      | inl config =>
          dsimp only [repairPreparationJoint, Sum.elim_inl]
          split
          · rename_i own
            exact Function.update_of_ne (fun equal => outside (equal.trans own)) _ _
          · rfl
  | reveal published owner name fresh source unresolved next ih =>
      intro point joint outside
      cases point with
      | inr point => exact ih point joint outside
      | inl config =>
          dsimp only [repairPreparationJoint, Sum.elim_inl]
          split
          · rename_i own
            cases config.state.get source with
            | failure =>
                exact Function.update_of_ne (fun equal => outside (equal.trans own)) _ _
            | success => rfl
          · rfl

end ProtocolState
end Vegas.SourceProgram
