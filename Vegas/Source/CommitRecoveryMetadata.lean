/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.CommitRecoveryAttemptReset

/-! # Deferred source obligations determined by the public control path

Bindings retain their syntactic obligations independently of the hidden
chosen result. Actual retries restore the original saved obligations.
-/

noncomputable section

namespace Vegas.SourceProgram

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

namespace Config

/-- The actual deferred code and its structural publication map. Typed values
and remembered private choices are deliberately unrestricted. -/
def MetadataEq {Γ : SourceCtx Player L} (first second : Config Player L Γ) : Prop :=
  first.registry = second.registry ∧ @first.revelations = @second.revelations

omit [DecidableEq Player] [IExpr.ResultTypes L] in
private theorem metadata_sample {Γ : SourceCtx Player L} {payload : L.Ty}
    (name : VarId) (first second : Config Player L Γ) (same : first.MetadataEq second)
    (left right : L.Val payload) :
    (sampleSuccessor name first left).MetadataEq (sampleSuccessor name second right) := by
  exact ⟨congrArg Registry.weaken same.1, congrArg Revelations.weaken same.2⟩

omit [IExpr.ResultTypes L] in
private theorem metadata_commit {Γ : SourceCtx Player L} {payload : L.Ty} {owner : Player}
    (name : VarId) (guard : SourceGuard L Γ owner name payload)
    (first second : Config Player L Γ) (same : first.MetadataEq second)
    (left right : PublicationResult (L.Val payload)) :
    (commitSuccessor name guard first left).MetadataEq
      (commitSuccessor name guard second right) := by
  constructor
  · simp only [commitSuccessor, same.1]
  · exact congrArg Revelations.weaken same.2

omit [DecidableEq Player] [IExpr.ResultTypes L] in
private theorem metadata_automatic {Γ : SourceCtx Player L}
    (name : VarId) (owner : Player) (payload : L.Ty)
    (first second : Config Player L Γ) (same : first.MetadataEq second) :
    (automaticCommit name owner payload first).MetadataEq
      (automaticCommit name owner payload second) := by
  exact ⟨congrArg Registry.weaken same.1, congrArg Revelations.weaken same.2⟩

omit [IExpr.ResultTypes L] in
private theorem metadata_reveal {Γ : SourceCtx Player L} {name : VarId}
    {owner : Player} {payload : L.Ty} (published : VarId)
    (selected : HasVar Γ name (.commitment owner payload))
    (first second : Config Player L Γ) (same : first.MetadataEq second)
    (left right : Bool) :
    (revealSuccessor published selected first left).MetadataEq
      (revealSuccessor published selected second right) := by
  exact ⟨congrArg Registry.weaken same.1,
    by simp only [revealSuccessor, same.2]⟩

end Config

namespace ProtocolState

/-- Equality of the syntactic cursor, retained obligations and publication
map in the original typed source state. -/
def MetadataEq : {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (program : SourceProgram Player L Γ O) → ProtocolState program → ProtocolState program → Prop
  | _, _, .ret _, first, second => Config.MetadataEq first second
  | _, _, .sample _ _ _ next, first, second => match first, second with
    | .inl first, .inl second => Config.MetadataEq first second
    | .inr first, .inr second => MetadataEq next first second
    | _, _ => False
  | _, _, .commit _ _ _ _ next, first, second => match first, second with
    | .inl first, .inl second => Config.MetadataEq first second
    | .inr first, .inr second => MetadataEq next first second
    | _, _ => False
  | _, _, .reveal _ _ _ _ _ _ next, first, second => match first, second with
    | .inl first, .inl second => Config.MetadataEq first second
    | .inr first, .inr second => MetadataEq next first second
    | _, _ => False

theorem MetadataEq.refl : ∀ {Γ : SourceCtx Player L} {O : Finset VarId}
    (program : SourceProgram Player L Γ O) (point : ProtocolState program),
    MetadataEq program point point
  | _, _, .ret _, _ => ⟨rfl, rfl⟩
  | _, _, .sample _ _ _ next, point => by
      cases point
      · exact ⟨rfl, rfl⟩
      · exact MetadataEq.refl next _
  | _, _, .commit _ _ _ _ next, point => by
      cases point
      · exact ⟨rfl, rfl⟩
      · exact MetadataEq.refl next _
  | _, _, .reveal _ _ _ _ _ _ next, point => by
      cases point
      · exact ⟨rfl, rfl⟩
      · exact MetadataEq.refl next _

theorem metadata_entry {Γ : SourceCtx Player L} {O : Finset VarId}
    (program : SourceProgram Player L Γ O) (first second : Config Player L Γ)
    (same : first.MetadataEq second) :
    MetadataEq program (entry program first) (entry program second) := by
  cases program <;> exact same

theorem MetadataEq.controls : ∀ {Γ : SourceCtx Player L} {O : Finset VarId}
    (program : SourceProgram Player L Γ O) (first second : ProtocolState program),
    MetadataEq program first second →
      remaining program first = remaining program second ∧
      atCommit program first = atCommit program second ∧
      commitEnd program first = commitEnd program second ∧
      commitOwners program first = commitOwners program second
  | _, _, .ret _, _, _, _ => ⟨rfl, rfl, rfl, rfl⟩
  | _, _, .sample _ _ _ next, first, second, same => by
      cases first <;> cases second
      · exact ⟨rfl, rfl, rfl, rfl⟩
      · cases same
      · cases same
      · exact MetadataEq.controls next _ _ same
  | _, _, .commit _ _ _ _ next, first, second, same => by
      cases first <;> cases second
      · exact ⟨rfl, rfl, rfl, rfl⟩
      · cases same
      · cases same
      · exact MetadataEq.controls next _ _ same
  | _, _, .reveal _ _ _ _ _ _ next, first, second, same => by
      cases first <;> cases second
      · exact ⟨rfl, rfl, rfl, rfl⟩
      · cases same
      · cases same
      · exact MetadataEq.controls next _ _ same

theorem MetadataEq.withHistory : ∀ {Γ : SourceCtx Player L} {O : Finset VarId}
    (program : SourceProgram Player L Γ O) (first second : ProtocolState program),
    MetadataEq program first second → ∀ left right : History Player L,
      MetadataEq program (withHistory program first left) (withHistory program second right)
  | _, _, .ret _, _, _, same, _, _ => same
  | _, _, .sample _ _ _ next, first, second, same, left, right => by
      cases first <;> cases second
      · exact same
      · cases same
      · cases same
      · exact MetadataEq.withHistory next _ _ same left right
  | _, _, .commit _ _ _ _ next, first, second, same, left, right => by
      cases first <;> cases second
      · exact same
      · cases same
      · cases same
      · exact MetadataEq.withHistory next _ _ same left right
  | _, _, .reveal _ _ _ _ _ _ next, first, second, same, left, right => by
      cases first <;> cases second
      · exact same
      · cases same
      · cases same
      · exact MetadataEq.withHistory next _ _ same left right

theorem MetadataEq.automaticCommitBlock : ∀ {Γ : SourceCtx Player L} {O : Finset VarId}
    (program : SourceProgram Player L Γ O) (first second : ProtocolState program),
    MetadataEq program first second →
      MetadataEq program (automaticCommitBlock program first) (automaticCommitBlock program second)
  | _, _, .ret _, _, _, same => same
  | _, _, .sample _ _ _ next, first, second, same => by
      cases first <;> cases second
      · exact same
      · cases same
      · cases same
      · exact MetadataEq.automaticCommitBlock next _ _ same
  | _, _, .commit name owner _ _ next, first, second, same => by
      cases first <;> cases second
      · exact MetadataEq.automaticCommitBlock next _ _
          (metadata_entry next _ _ (Config.metadata_automatic name owner _ _ _ same))
      · cases same
      · cases same
      · exact MetadataEq.automaticCommitBlock next _ _ same
  | _, _, .reveal _ _ _ _ _ _ next, first, second, same => by
      cases first <;> cases second
      · exact same
      · cases same
      · cases same
      · exact MetadataEq.automaticCommitBlock next _ _ same

/-- The actual raw instruction retains the same static obligations for any
two supported values at matching source cursors and public exclusions. -/
theorem recoveryStep_metadata : ∀ {Γ : SourceCtx Player L} {O : Finset VarId}
    (program : SourceProgram Player L Γ O) (first second : ProtocolState program),
    MetadataEq program first second → ∀ (excluded : Finset Player)
      (left right : Player → Option (CommitRecoveryMove Player L)),
    ∀ l ∈ (recoveryStep program first excluded left).support,
    ∀ r ∈ (recoveryStep program second excluded right).support,
      MetadataEq program l.1 r.1
  | _, _, .ret _, _, _, same, _, _, _, l, lm, r, rm => by
      rw [recoveryStep, PMF.mem_support_pure_iff] at lm rm
      subst l; subst r
      exact same
  | _, _, .sample name _ _ next, first, second, same, excluded, left, right,
      l, lm, r, rm => by
      cases first <;> cases second
      · obtain ⟨lv, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp lm
        obtain ⟨rv, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp rm
        exact metadata_entry next _ _ (Config.metadata_sample name _ _ same lv rv)
      · cases same
      · cases same
      · simp only [recoveryStep, Sum.elim_inr] at lm rm
        obtain ⟨lowerLeft, lowerLeftMember, leftShape⟩ := (PMF.mem_support_map_iff
          (fun result : ProtocolState next × Finset Player => (Sum.inr result.1, result.2))
          (recoveryStep next _ excluded left) _).mp lm
        obtain ⟨lowerRight, lowerRightMember, rightShape⟩ := (PMF.mem_support_map_iff
          (fun result : ProtocolState next × Finset Player => (Sum.inr result.1, result.2))
          (recoveryStep next _ excluded right) _).mp rm
        subst l; subst r
        exact recoveryStep_metadata next _ _ same excluded left right
          lowerLeft lowerLeftMember lowerRight lowerRightMember
  | _, _, .commit name owner _ guard next, first, second, same, excluded, left, right,
      l, lm, r, rm => by
      cases first <;> cases second
      · simp only [recoveryStep, Sum.elim_inl] at lm rm
        by_cases inactive : owner ∈ excluded
        · rw [ite_eq_left inactive, PMF.mem_support_pure_iff] at lm rm
          subst l; subst r
          exact metadata_entry next _ _ (Config.metadata_automatic name owner _ _ _ same)
        · rw [ite_eq_right inactive, PMF.mem_support_pure_iff] at lm rm
          subst l; subst r
          exact metadata_entry next _ _ (Config.metadata_commit name guard _ _ same _ _)
      · cases same
      · cases same
      · simp only [recoveryStep, Sum.elim_inr] at lm rm
        obtain ⟨lowerLeft, lowerLeftMember, leftShape⟩ := (PMF.mem_support_map_iff
          (fun result : ProtocolState next × Finset Player => (Sum.inr result.1, result.2))
          (recoveryStep next _ excluded left) _).mp lm
        obtain ⟨lowerRight, lowerRightMember, rightShape⟩ := (PMF.mem_support_map_iff
          (fun result : ProtocolState next × Finset Player => (Sum.inr result.1, result.2))
          (recoveryStep next _ excluded right) _).mp rm
        subst l; subst r
        exact recoveryStep_metadata next _ _ same excluded left right
          lowerLeft lowerLeftMember lowerRight lowerRightMember
  | _, _, .reveal published owner _ _ selected _ next, first, second, same,
      excluded, left, right, l, lm, r, rm => by
      cases first <;> cases second
      · simp only [recoveryStep, Sum.elim_inl, PMF.mem_support_pure_iff] at lm rm
        subst l; subst r
        by_cases inactive : owner ∈ excluded
        · simp only [ite_eq_left inactive]
          exact metadata_entry next _ _ (Config.metadata_reveal published selected _ _ same
            false false)
        · simp only [ite_eq_right inactive]
          exact metadata_entry next _ _ (Config.metadata_reveal published selected _ _ same
            false false)
      · cases same
      · cases same
      · simp only [recoveryStep, Sum.elim_inr] at lm rm
        obtain ⟨lowerLeft, lowerLeftMember, leftShape⟩ := (PMF.mem_support_map_iff
          (fun result : ProtocolState next × Finset Player => (Sum.inr result.1, result.2))
          (recoveryStep next _ excluded left) _).mp lm
        obtain ⟨lowerRight, lowerRightMember, rightShape⟩ := (PMF.mem_support_map_iff
          (fun result : ProtocolState next × Finset Player => (Sum.inr result.1, result.2))
          (recoveryStep next _ excluded right) _).mp rm
        subst l; subst r
        exact recoveryStep_metadata next _ _ same excluded left right
          lowerLeft lowerLeftMember lowerRight lowerRightMember

end ProtocolState

namespace CommitRecoveryState

variable {Γ : SourceCtx Player L} {O : Finset VarId}
  {program : SourceProgram Player L Γ O}

/-- Matching actual source checkpoint structure, retaining arbitrary hidden
typed stores and all private remembered words. -/
def MetadataEq (first second : CommitRecoveryState program) : Prop :=
  ProtocolState.MetadataEq program first.point second.point ∧
  ProtocolState.MetadataEq program first.saved second.saved ∧
  first.excluded = second.excluded ∧ first.entryExcluded = second.entryExcluded ∧
  first.generation = second.generation

theorem MetadataEq.close (first second : CommitRecoveryState program)
    (same : first.MetadataEq second) : first.close.MetadataEq second.close := by
  obtain ⟨point, saved, excluded, entryExcluded, generation⟩ := same
  have live := ProtocolState.MetadataEq.controls program first.point second.point point
  have entry := ProtocolState.MetadataEq.controls program first.saved second.saved saved
  have finished : first.Finished = second.Finished := by
    unfold Finished
    rw [entry.2.1, live.1, entry.2.2.1]
  have failed : first.NewFailure = second.NewFailure := by
    unfold NewFailure
    rw [excluded, entryExcluded]
  have survives : first.Survives = second.Survives := by
    unfold Survives
    rw [entry.2.2.2, excluded]
  have restoredMeta := ProtocolState.MetadataEq.withHistory program first.saved second.saved saved
    (ProtocolState.history program first.point) (ProtocolState.history program second.point)
  have automatic := ProtocolState.MetadataEq.automaticCommitBlock program _ _ restoredMeta
  by_cases complete : first.Finished
  · have completeRight : second.Finished := Eq.mp finished complete
    by_cases failure : first.NewFailure
    · have failureRight : second.NewFailure := Eq.mp failed failure
      by_cases survivor : first.Survives
      · have survivorRight : second.Survives := Eq.mp survives survivor
        rw [first.close_of_retry complete failure survivor,
          second.close_of_retry completeRight failureRight survivorRight]
        exact ⟨restoredMeta, restoredMeta, excluded, excluded,
          congrArg (fun generation => generation + 1) generation⟩
      · have noRight : ¬ second.Survives := fun yes => survivor (Eq.mpr survives yes)
        rw [first.close_of_exhausted complete failure survivor,
          second.close_of_exhausted completeRight failureRight noRight]
        exact ⟨automatic, automatic, excluded, excluded, generation⟩
    · have noRight : ¬ second.NewFailure := fun yes => failure (Eq.mpr failed yes)
      simp only [CommitRecoveryState.close, complete, completeRight, failure, noRight, ↓reduceIte]
      exact ⟨point, point, excluded, excluded, generation⟩
  · have noRight : ¬ second.Finished := fun yes => complete (Eq.mpr finished yes)
    by_cases committing : ProtocolState.atCommit program first.saved = true
    · have committingRight : ProtocolState.atCommit program second.saved = true :=
        entry.2.1 ▸ committing
      simp only [CommitRecoveryState.close, complete, noRight, committing,
        committingRight, ↓reduceIte]
      exact ⟨point, saved, excluded, entryExcluded, generation⟩
    · have notRight : ProtocolState.atCommit program second.saved ≠ true := by
        rw [← entry.2.1]
        exact committing
      simp only [CommitRecoveryState.close, complete, noRight, committing, notRight, ↓reduceIte]
      exact ⟨point, point, excluded, excluded, generation⟩

end CommitRecoveryState

namespace Setup

variable (setup : Setup (Player := Player) (L := L))

private theorem publicRecall_extend (who : Player)
    {state target : setup.commitRecoveryProtocol.State}
    (trace : setup.commitRecoveryProtocol.Trace state)
    (joint : Player → Option (CommitRecoveryMove Player L))
    (legal : setup.commitRecoveryProtocol.Legal state joint)
    (reached : target ∈ (setup.commitRecoveryProtocol.step state ⟨joint, legal⟩).support) :
    setup.attemptPublicRecall who (trace.extend joint legal reached) =
      setup.attemptPublicSignal who target :: setup.attemptPublicRecall who trace := by
  rw [attemptPublicRecall, InfoSignals.infoOf_extend]
  rfl

private theorem publicRecall_length (who : Player)
    {state : setup.commitRecoveryProtocol.State}
    (trace : setup.commitRecoveryProtocol.Trace state) :
    (setup.attemptPublicRecall who trace).length = trace.length + 1 := by
  induction trace with
  | start => rfl
  | extend earlier joint legal reached ih =>
      rw [setup.publicRecall_extend, List.length_cons, ih]
      rfl

/-- Two genuine source histories with the same complete public control word
have literally the same deferred code and revelation map at their current
AND saved cursors. This derives the static data through all source branches;
there is no assumed registry, desired query, or historical entry premise. -/
theorem commitRecovery_metadata_of_publicRecall (who : Player)
    {leftState rightState : setup.commitRecoveryProtocol.State}
    (leftTrace : setup.commitRecoveryProtocol.Trace leftState)
    (rightTrace : setup.commitRecoveryProtocol.Trace rightState)
    (samePublic : setup.attemptPublicRecall who leftTrace =
      setup.attemptPublicRecall who rightTrace) :
    match leftState, rightState with
    | none, none => True
    | some left, some right => left.MetadataEq right
    | _, _ => False := by
  have clock : leftTrace.length = rightTrace.length := by
    have lengths := congrArg List.length samePublic
    simpa only [setup.publicRecall_length, Nat.add_left_inj] using lengths
  induction leftTrace generalizing rightState with
  | start =>
      cases rightTrace with
      | start => trivial
      | extend earlier joint legal reached => simp only [Trace.length] at clock; omega
  | @extend leftSource leftTarget leftEarlier leftJoint leftLegal leftReached ih =>
      cases rightTrace with
      | start => simp only [Trace.length] at clock; omega
      | @extend rightSource rightTarget rightEarlier rightJoint rightLegal rightReached =>
          have pair := List.cons.inj (by
            simpa only [setup.publicRecall_extend] using samePublic)
          have previousClock : leftEarlier.length = rightEarlier.length := by
            simpa only [Trace.length, Nat.add_left_inj] using clock
          have previous := ih rightEarlier pair.2 previousClock
          cases leftSource with
          | none =>
              cases rightSource with
              | some right => cases previous
              | none =>
                  obtain ⟨leftInputs, _, rfl⟩ :=
                    (PMF.mem_support_map_iff _ _ _).mp leftReached
                  obtain ⟨rightInputs, _, rfl⟩ :=
                    (PMF.mem_support_map_iff _ _ _).mp rightReached
                  have initial := ProtocolState.metadata_entry setup.program
                    (setup.initialConfig leftInputs) (setup.initialConfig rightInputs) ⟨rfl, rfl⟩
                  exact ⟨initial, initial, rfl, rfl, rfl⟩
          | some left =>
              cases rightSource with
              | none => cases previous
              | some right =>
                  obtain ⟨leftNext, leftSupport, rfl⟩ :=
                    (PMF.mem_support_map_iff _ _ _).mp leftReached
                  obtain ⟨rightNext, rightSupport, rfl⟩ :=
                    (PMF.mem_support_map_iff _ _ _).mp rightReached
                  have excluded : leftNext.excluded = rightNext.excluded :=
                    congrArg (fun signal => signal.2.1) pair.1
                  obtain ⟨leftRaw, leftRawSupport, rfl⟩ :=
                    left.step_raw_result leftJoint leftNext leftSupport
                  obtain ⟨rightRaw, rightRawSupport, rfl⟩ :=
                    right.step_raw_result rightJoint rightNext rightSupport
                  have rawExcluded : leftRaw.1.2 = rightRaw.1.2 := by
                    simpa only [CommitRecoveryState.close_excluded,
                      CommitRecoveryState.install] using excluded
                  have rawMetadata := ProtocolState.recoveryStep_metadata setup.program
                    left.point right.point previous.1 left.excluded leftJoint rightJoint
                    leftRaw.1 leftRawSupport rightRaw.1
                      (by simpa only [previous.2.2.1] using rightRawSupport)
                  apply CommitRecoveryState.MetadataEq.close
                  exact ⟨rawMetadata, previous.2.1, rawExcluded,
                    previous.2.2.2.1, previous.2.2.2.2⟩

end Setup
end Vegas.SourceProgram
