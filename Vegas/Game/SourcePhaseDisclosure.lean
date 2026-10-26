/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Source.CommitRecoveryDisclosureAliases
import Vegas.Source.CommitRecoveryNoMissInformation
import Vegas.Game.CommitRecoveryHiddenInformation
import Vegas.Source.CommitRecoveryWordMass
import Vegas.Source.CommitRecoveryObservedMemory

/-! # Ineffective disclosure aliases preserve foreign source information

The source player still samples its original intention. Suppressing an
ineffective opening changes that player's private action word, but keeps the
typed successor, exclusions and every other player's complete source
information at the actual extended histories. The semantic successor keeps
both saved and live stores, and an ineffective publication excludes its owner.
-/

noncomputable section

namespace Vegas

open SourceProgram GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

private theorem suffix_observe_congr {wholeΓ Γ : SourceCtx Player L}
    {wholeO O : Finset VarId} {whole : SourceProgram Player L wholeΓ wholeO}
    {program : SourceProgram Player L Γ O}
    {lift : ProtocolState program → ProtocolState whole}
    (origin : ProtocolSuffix whole program lift) (who : Player) :
    ∀ first second, ProtocolState.observe who program first =
      ProtocolState.observe who program second →
        ProtocolState.observe who whole (lift first) =
          ProtocolState.observe who whole (lift second) := by
  induction origin with
  | initial => intro first second same; exact same
  | sampleTail _ _ _ _ ih =>
      intro first second same
      exact ih (.inr first) (.inr second) (congrArg Sum.inr same)
  | commitTail _ _ _ _ ih =>
      intro first second same
      exact ih (.inr first) (.inr second) (congrArg Sum.inr same)
  | revealTail _ _ _ _ _ ih =>
      intro first second same
      exact ih (.inr first) (.inr second) (congrArg Sum.inr same)

/-- The literal full source signals and own-play recall of every other player
agree after replacing one disclosure by its effective Boolean. Both sides are
actual legal source steps from the same initialized history. Their saved and
live semantic states agree; a failed publication excludes the actor. -/
theorem sourcePhase_effective_disclosure_foreign_information
    (setup : Setup (Player := Player) (L := L))
    {Γ : SourceCtx Player L} {O : Finset VarId} {published name : VarId}
    {owner : Player} {payload : L.Ty} (fresh : published ∉ Γ.map Prod.fst)
    (selected : HasVar Γ name (.commitment owner payload)) (unresolved : name ∈ O)
    (suffix : SourceProgram Player L ((published, .publication payload) :: Γ) (O.erase name))
    (lift : ProtocolState (.reveal published owner name fresh selected unresolved suffix) →
      ProtocolState setup.program)
    (origin : ProtocolSuffix setup.program
      (.reveal published owner name fresh selected unresolved suffix) lift)
    (config : Config Player L Γ) (current : CommitRecoveryState setup.program)
    (trace : setup.commitRecoveryProtocol.Trace (some current))
    (point : current.point = lift (.inl config)) (active : owner ∉ current.excluded)
    (disclose : Bool)
    (firstJoint secondJoint : Player → Option (CommitRecoveryMove Player L))
    (firstLegal : setup.commitRecoveryProtocol.Legal (some current) firstJoint)
    (secondLegal : setup.commitRecoveryProtocol.Legal (some current) secondJoint)
    (original : OwnAction.disclosure ((firstJoint owner).map (·.action)) = disclose)
    (effective : OwnAction.disclosure ((secondJoint owner).map (·.action)) =
      effectiveDisclosure published selected config disclose)
    (firstState secondState : setup.commitRecoveryProtocol.State)
    (firstReached : firstState ∈ (setup.commitRecoveryProtocol.step (some current)
      ⟨firstJoint, firstLegal⟩).support)
    (secondReached : secondState ∈ (setup.commitRecoveryProtocol.step (some current)
      ⟨secondJoint, secondLegal⟩).support) :
    firstState.elim ∅ (·.excluded) = secondState.elim ∅ (·.excluded) ∧
      (∀ who, who ≠ owner →
        setup.commitRecoveryModel.infoOf who
            (trace.extend firstJoint firstLegal firstReached) =
          setup.commitRecoveryModel.infoOf who
            (trace.extend secondJoint secondLegal secondReached)) ∧
      firstState.map CommitRecoveryState.eraseHistory =
        secondState.map CommitRecoveryState.eraseHistory ∧
      (disclosureResult published selected config disclose = .failure →
        owner ∈ firstState.elim ∅ (·.excluded)) := by
  let excluded := fun choice => match disclosureResult published selected config choice with
    | .failure => insert owner current.excluded
    | .success _ => current.excluded
  let after := fun choice => CommitRecoveryState.atPoint
    (lift (.inr (ProtocolState.entry suffix (revealSuccessor published selected config choice))))
    (excluded choice) current.generation
  have notCommit : ProtocolState.atCommit setup.program current.point = false := by
    rw [point, origin.atCommit_lift]
    rfl
  have stepLaw (joint : Player → Option (CommitRecoveryMove Player L))
      (legal : setup.commitRecoveryProtocol.Legal (some current) joint) (choice : Bool)
      (chosen : OwnAction.disclosure ((joint owner).map (·.action)) = choice) :
      setup.commitRecoveryProtocol.step (some current) ⟨joint, legal⟩ =
        PMF.pure (some (after choice)) := by
    change (current.step joint).map some = _
    rw [current.step_noncommit_law (setup.commitRecovery_blockFrontier trace) notCommit,
      point, origin.recoveryStep_lift]
    simp only [ProtocolState.recoveryStep, Sum.elim_inl, ite_eq_right active, chosen,
      PMF.pure_map]
    unfold after excluded disclosureResult
    cases result : (revealSuccessor published selected config choice).state.get .here <;>
      rfl
  have firstAt : firstState = some (after disclose) := by
    rw [stepLaw firstJoint firstLegal disclose original, PMF.mem_support_pure_iff] at firstReached
    exact firstReached
  have secondAt : secondState =
      some (after (effectiveDisclosure published selected config disclose)) := by
    rw [stepLaw secondJoint secondLegal _ effective, PMF.mem_support_pure_iff] at secondReached
    exact secondReached
  have sameExcluded : excluded disclose =
      excluded (effectiveDisclosure published selected config disclose) :=
    congrArg (fun result => match result with
      | .failure => insert owner current.excluded
      | .success _ => current.excluded)
      (disclosureResult_effectiveDisclosure published selected config disclose).symm
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [firstAt, secondAt]
    exact sameExcluded
  · intro who other
    have actor : ProtocolState.actor setup.program current.point = some owner := by
      rw [point, origin.actor_lift]
      rfl
    have inactive : ¬ setup.commitRecoveryProtocol.active (some current) who := by
      intro offered
      exact other (Option.some.inj (actor.symm.trans offered.1)).symm
    have coordinate (joint : Player → Option (CommitRecoveryMove Player L))
        (legal : setup.commitRecoveryProtocol.Legal (some current) joint) : joint who = none := by
      cases chosen : joint who with
      | none => rfl
      | some move =>
          have offered := legal.2 who
          rw [chosen] at offered
          exact (inactive offered.1).elim
    have privateView : setup.commitRecoveryPrivate who firstState =
        setup.commitRecoveryPrivate who secondState := by
      rw [firstAt, secondAt]
      apply congrArg some
      apply suffix_observe_congr origin who
      apply congrArg Sum.inr
      apply ProtocolState.observe_entry_congr
      exact ((effective_reveal_observations (published := published) selected config disclose).2
        who other).symm
    have publicView : setup.commitRecoveryPublic firstState =
        setup.commitRecoveryPublic secondState := by
      rw [firstAt, secondAt]
      change (excluded disclose, current.generation,
          instructionCount setup.program - ProtocolState.remaining setup.program
            (lift (.inr (ProtocolState.entry suffix
              (revealSuccessor published selected config disclose))))) = _
      rw [sameExcluded]
      simp only [Setup.commitRecoveryPublic, after,
        CommitRecoveryState.atPoint, origin.remaining_lift, ProtocolState.remaining,
        Sum.elim_inr, ProtocolState.remaining_entry]
    exact setup.commitRecovery_info_extend_eq who ⟨some current, trace⟩ ⟨some current, trace⟩
      firstJoint secondJoint firstLegal secondLegal firstState secondState firstReached
      secondReached rfl ((coordinate firstJoint firstLegal).trans
        (coordinate secondJoint secondLegal).symm) privateView publicView
  · rw [firstAt, secondAt]
    apply congrArg some
    have configuration :
        {revealSuccessor published selected config disclose with history := fun _ => []} =
          {revealSuccessor published selected config
            (effectiveDisclosure published selected config disclose) with
              history := fun _ => []} := by
      have cells := (effective_reveal_observations (published := published)
        selected config disclose).1.symm
      exact congrArg (fun state => {revealSuccessor published selected config disclose with
        state := state, history := fun _ => []}) cells
    have points : ProtocolState.withHistory setup.program (after disclose).point (fun _ => []) =
        ProtocolState.withHistory setup.program
          (after (effectiveDisclosure published selected config disclose)).point
            (fun _ => []) := by
      dsimp only [after, CommitRecoveryState.atPoint]
      rw [← origin.withHistory_lift, ← origin.withHistory_lift]
      simp only [ProtocolState.withHistory, Sum.elim_inr, ProtocolState.withHistory_entry]
      rw [configuration]
    change CommitRecoveryState.atPoint
        (ProtocolState.withHistory setup.program (after disclose).point (fun _ => []))
        (excluded disclose) current.generation =
      CommitRecoveryState.atPoint
        (ProtocolState.withHistory setup.program
          (after (effectiveDisclosure published selected config disclose)).point (fun _ => []))
        (excluded (effectiveDisclosure published selected config disclose)) current.generation
    exact congrArg₂ (fun point excluded =>
      CommitRecoveryState.atPoint point excluded current.generation) points sameExcluded
  · intro failed
    rw [firstAt]
    change owner ∈ excluded disclose
    simp only [excluded, failed]
    exact Finset.mem_insert_self ..

end Vegas
