/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.CommitRecoveryAttemptExit
import Vegas.Source.CommitRecoveryNoMissInformation

/-! # Recovering the typed attempt from its actual original instruction window -/

noncomputable section

namespace Vegas.SourceProgram

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

private theorem commit_instruction_attempt
    {wholeΓ Γ : SourceCtx Player L} {wholeO O : Finset VarId}
    {whole : SourceProgram Player L wholeΓ wholeO} (initial : Config Player L wholeΓ)
    {name : VarId} {owner : Player} {payload : L.Ty} {fresh : name ∉ Γ.map Prod.fst}
    (guard : SourceGuard L Γ owner name payload)
    (tail : SourceProgram Player L ((name, .commitment owner payload) :: Γ) (insert name O))
    {lift : ProtocolState (.commit name owner fresh guard tail) → ProtocolState whole}
    (origin : ProtocolSuffix whole (.commit name owner fresh guard tail) lift)
    (config : Config Player L Γ) (state : CommitRecoveryState whole)
    (atEntry : state.point = lift (.inl config))
    (joint : Player → Option (CommitRecoveryMove Player L))
    (legal : (commitRecoveryProtocol whole initial).Legal state joint)
    (result : ProtocolState whole × Finset Player)
    (raw : result ∈ (ProtocolState.recoveryStep whole state.point state.excluded joint).support) :
    ∃ (next : Config Player L ((name, .commitment owner payload) :: Γ))
      (after : Finset Player)
      (attempt : (CommitPrefix.commit (O := O) name owner fresh guard .nil).Attempt
        config state.excluded next after),
      attempt.joints = [joint] ∧
        result = (lift (.inr (ProtocolState.entry tail next)), after) := by
  classical
  have actor : ProtocolState.actor whole state.point = some owner := by
    rw [atEntry, origin.actor_lift]
    rfl
  by_cases inactive : owner ∈ state.excluded
  · have empty : joint = fun _ => none := by
      funext who
      cases selected : joint who with
      | none => rfl
      | some move =>
          have offered := legal.2 who
          rw [selected] at offered
          have same : who = owner := Option.some.inj (offered.1.1.symm.trans actor)
          exact (offered.1.2 (same ▸ inactive)).elim
    refine ⟨automaticCommit name owner payload config, state.excluded,
      .excluded inactive (.nil _ _), ?_, ?_⟩
    · simp only [CommitPrefix.Attempt.joints, empty]
    · rw [atEntry, origin.recoveryStep_lift] at raw
      simpa only [ProtocolState.recoveryStep, Sum.elim_inl, inactive, ↓reduceIte,
        PMF.pure_map, PMF.mem_support_pure_iff] using raw
  · cases selected : joint owner with
    | none =>
        have denied := legal.2 owner
        rw [selected] at denied
        exact (denied ⟨actor, inactive⟩).elim
    | some move =>
        have offered := legal.2 owner
        rw [selected] at offered
        have available : move ∈ ProtocolView.recoveryAvailable owner whole
            (ProtocolState.observe owner whole state.point) := offered.2
        rw [atEntry, origin.recoveryAvailable] at available
        obtain ⟨⟨choice, _admitted, action⟩, missing⟩ := available
        have missingFailure : move.missing = true → choice = .failure := by
          intro missed
          have failed := missing missed
          rw [action] at failed
          exact failed
        have sameMove : move = ⟨.commit owner name payload choice, move.missing⟩ := by
          cases move
          exact congrArg (fun action => CommitRecoveryMove.mk action _) action
        have canonical : joint = fun who => if who = owner then some move else none := by
          funext who
          by_cases own : who = owner
          · subst who
            simp only [ite_true, selected]
          · simp only [own, ↓reduceIte]
            cases chosen : joint who with
            | none => rfl
            | some other =>
                have active := legal.2 who
                rw [chosen] at active
                exact (own (Option.some.inj (active.1.1.symm.trans actor))).elim
        refine ⟨commitSuccessor name guard config choice,
          excludeCommit state.excluded owner move.missing,
          .active inactive choice move.missing missingFailure (.nil _ _), ?_, ?_⟩
        · simp only [CommitPrefix.Attempt.joints]
          rw [canonical, sameMove]
        · rw [atEntry, origin.recoveryStep_lift] at raw
          simpa only [ProtocolState.recoveryStep, Sum.elim_inl, inactive, ↓reduceIte,
            selected, Option.map_some, action, OwnAction.binding_commit,
            CommitRecoveryMove.missed, Option.elim_some, excludeCommit, PMF.pure_map,
            PMF.mem_support_pure_iff] using raw

namespace CommitPrefix

private def prependAttempt
    {Γ Δ : SourceCtx Player L} {O P : Finset VarId}
    {name : VarId} {owner : Player} {payload : L.Ty} {fresh : name ∉ Γ.map Prod.fst}
    {guard : SourceGuard L Γ owner name payload}
    {rest : CommitPrefix ((name, .commitment owner payload) :: Γ) (insert name O) Δ P}
    {entry : Config Player L Γ} {excluded : Finset Player}
    {middle : Config Player L ((name, .commitment owner payload) :: Γ)}
    {owners : Finset Player} {finished : Config Player L Δ} {after : Finset Player}
    (head : (CommitPrefix.commit (O := O) name owner fresh guard .nil).Attempt
      entry excluded middle owners)
    (tail : rest.Attempt middle owners finished after) :
    (CommitPrefix.commit name owner fresh guard rest).Attempt entry excluded finished after := by
  cases head with
  | active active choice missed missing later =>
      cases later
      exact .active active choice missed missing tail
  | excluded inactive later =>
      cases later
      exact .excluded inactive tail

omit [IExpr.ResultTypes L] in
private theorem prependAttempt_joints
    {Γ Δ : SourceCtx Player L} {O P : Finset VarId}
    {name : VarId} {owner : Player} {payload : L.Ty} {fresh : name ∉ Γ.map Prod.fst}
    {guard : SourceGuard L Γ owner name payload}
    {rest : CommitPrefix ((name, .commitment owner payload) :: Γ) (insert name O) Δ P}
    {entry : Config Player L Γ} {excluded : Finset Player}
    {middle : Config Player L ((name, .commitment owner payload) :: Γ)}
    {owners : Finset Player} {finished : Config Player L Δ} {after : Finset Player}
    (head : (CommitPrefix.commit (O := O) name owner fresh guard .nil).Attempt
      entry excluded middle owners)
    (tail : rest.Attempt middle owners finished after) :
    (prependAttempt head tail).joints = head.joints ++ tail.joints := by
  cases head with
  | active active choice missed missing later => cases later; rfl
  | excluded inactive later => cases later; rfl

/-- A supported original instruction window determines an actual typed
attempt with precisely its raw actions and its real closed endpoint. -/
theorem attempt_of_instructions
    {wholeΓ Γ Δ : SourceCtx Player L} {wholeO O P : Finset VarId}
    {whole : SourceProgram Player L wholeΓ wholeO} (initial : Config Player L wholeΓ)
    (block : CommitPrefix Γ O Δ P) :
    ∀ (suffix : SourceProgram Player L Δ P)
      (lift : ProtocolState (block.prepend suffix) → ProtocolState whole),
    ProtocolSuffix whole (block.prepend suffix) lift →
    ∀ (entry : Config Player L Γ) (state last : CommitRecoveryState whole)
      (joints addresses),
    state.point = lift (ProtocolState.entry (block.prepend suffix) entry) →
    ProtocolState.atCommit whole state.saved = true →
    ProtocolState.commitEnd whole state.saved ≤ instructionCount suffix →
    0 < block.length →
    CommitRecoveryState.InstructionPath whole initial joints addresses state last →
    joints.length = block.length →
    ∃ (finished : Config Player L Δ) (after : Finset Player)
      (attempt : block.Attempt entry state.excluded finished after),
      attempt.joints = joints ∧ ∃ monotone : state.excluded ⊆ after,
        last = (state.install
          (lift (block.liftPoint suffix (ProtocolState.entry suffix finished)), after)
          monotone).close := by
  induction block with
  | nil =>
      intro suffix lift origin entry state last joints addresses atEntry saved endpoint positive
      cases positive
  | @commit Γ O Δ P name owner payload fresh guard rest ih =>
      intro suffix lift origin entry state last joints addresses atEntry saved endpoint positive
        path length
      cases path with
      | refl => simp only [List.length_nil, CommitPrefix.length] at length; omega
      | @step _ middle _ joint words signals legal supported later =>
          obtain ⟨result, raw, middleEq⟩ := state.step_raw_result joint middle supported
          obtain ⟨headConfig, headExcluded, head, headWord, rawEq⟩ :=
            commit_instruction_attempt initial guard (rest.prepend suffix) origin entry state
              atEntry joint legal result.1 raw
          have tailLength : words.length = rest.length := by
            simp only [List.length_cons, CommitPrefix.length] at length
            omega
          let next := state.install result.1 result.2
          have nextPoint : next.point = lift (.inr
              (ProtocolState.entry (rest.prepend suffix) headConfig)) := by
            exact congrArg Prod.fst rawEq
          have nextExcluded : next.excluded = headExcluded := congrArg Prod.snd rawEq
          by_cases restPositive : 0 < rest.length
          · have beforeEnd : ProtocolState.commitEnd whole next.saved <
                ProtocolState.remaining whole next.point := by
              rw [nextPoint, origin.remaining_lift]
              change ProtocolState.commitEnd whole state.saved <
                ProtocolState.remaining (rest.prepend suffix)
                  (ProtocolState.entry (rest.prepend suffix) headConfig)
              rw [ProtocolState.remaining_entry, rest.instructionCount_prepend]
              omega
            have noClose := next.close_eq_self_of_remaining_gt saved beforeEnd
            have middleNext : middle = next := middleEq.trans noClose
            rw [middleNext] at later
            let tailOrigin := ProtocolSuffix.commitTail fresh guard (rest.prepend suffix) origin
            obtain ⟨finished, after, tailAttempt, tailWord, monotone, lastEq⟩ :=
              ih suffix (fun point => lift (.inr point)) tailOrigin headConfig next last words
                signals nextPoint saved endpoint restPositive later tailLength
            let tailTyped : rest.Attempt headConfig headExcluded finished after :=
              nextExcluded ▸ tailAttempt
            let attempt := prependAttempt head tailTyped
            refine ⟨finished, after, attempt, ?_, head.excluded_subset.trans
              tailTyped.excluded_subset, ?_⟩
            · rw [prependAttempt_joints, headWord]
              have same : tailTyped.joints = words := by
                dsimp only [tailTyped]
                cases nextExcluded
                exact tailWord
              rw [same]
              rfl
            · exact lastEq
          · have zero : rest.length = 0 := by omega
            have empty : words = [] := List.length_eq_zero_iff.mp (tailLength.trans zero)
            subst words
            cases later
            cases rest with
            | nil =>
                refine ⟨headConfig, headExcluded, head, headWord,
                  head.excluded_subset, ?_⟩
                rcases result with ⟨⟨rawPoint, rawOwners⟩, rawMonotone⟩
                obtain ⟨pointEq, ownersEq⟩ := Prod.mk.inj rawEq
                subst rawPoint
                subst rawOwners
                exact middleEq
            | commit => simp only [CommitPrefix.length] at zero; omega

end CommitPrefix
end Vegas.SourceProgram
