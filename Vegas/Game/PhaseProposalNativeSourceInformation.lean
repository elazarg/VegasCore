/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseProposalSourceFiber
import Vegas.Game.ProposalRecoveryArchivePublicHistory
import Vegas.Game.PhaseProposalInstalledSourceBlock
import Vegas.Compile.CommitPrefixReadStability
import Vegas.Source.CommitAttemptRanks
import Vegas.Source.ProposalRecoveryDisclosure
import Vegas.Source.ProposalRecoveryVirtualLift
import Vegas.Source.CommitPrefixPointAppend
import Vegas.Compile.CommitPrefixCompletionSnoc
import Vegas.Game.PhaseSurvivingSourceView
import Vegas.Game.RecoveryFixedCommitSelector
import Vegas.Game.PhaseCountServiceForeignWord
import Vegas.Source.CommitRecoveryNoMissQuery
import Vegas.Source.ProposalRecoveryCommitWindow
import Vegas.Source.CommitRecoveryPublicObservation
import Vegas.Game.PhaseCommitmentProposalArchive
import Vegas.Source.CommitRecoveryInitialInputs

/-! # Complete source information under foreign disclosure refinements

The source histories remain genuine histories of the original protocol.
Foreign publication causes can differ while their public results and locked
proposal deltas agree. The observer's literal labeled choices are retained.
-/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))

/-- The only changed private label is a foreign truthful disclosure versus
its failed-disclosure copy. Both labels refer to the same owned variable.
All other coordinates, including the observer's, stay literal. -/
def ForeignDisclosureLabels (who : Player)
    (left right : Player → Option (ProposalRecoveryMove Player L)) : Prop :=
  left = right ∨ ∃ owner name, owner ≠ who ∧
    (∀ other, other ≠ owner → left other = right other) ∧
    ((left owner = some (ProposalRecoveryMove.ordinary
          ⟨.reveal owner name true, false⟩) ∧
        right owner = some (ProposalRecoveryMove.failedDisclosure owner name)) ∨
      (right owner = some (ProposalRecoveryMove.ordinary
          ⟨.reveal owner name true, false⟩) ∧
        left owner = some (ProposalRecoveryMove.failedDisclosure owner name)))

omit [DecidableEq Player] [IExpr.ResultTypes L] in
theorem ForeignDisclosureLabels.own {who : Player}
    {left right : Player → Option (ProposalRecoveryMove Player L)}
    (refines : ForeignDisclosureLabels who left right) : left who = right who := by
  rcases refines with same | ⟨owner, _name, foreign, retained, _labels⟩
  · exact congrFun same who
  · exact retained who (Ne.symm foreign)

omit [DecidableEq Player] [IExpr.ResultTypes L] in
private theorem ForeignDisclosureLabels.for_observer {who : Player}
    {left right : Player → Option (ProposalRecoveryMove Player L)}
    (refines : ForeignDisclosureLabels who left right) (observer : Player)
    (own : left observer = right observer) : ForeignDisclosureLabels observer left right := by
  rcases refines with same | ⟨owner, name, _foreign, retained, labels⟩
  · exact Or.inl same
  · have different : owner ≠ observer := by
      intro same
      subst owner
      rcases labels with ⟨leftEq, rightEq⟩ | ⟨rightEq, leftEq⟩
      · rw [leftEq, rightEq] at own
        cases own
      · rw [leftEq, rightEq] at own
        cases own
    exact Or.inr ⟨owner, name, different, retained, labels⟩

/-- A finite pairing of actual supported source steps from the SAME retained
initializer. A changed foreign cause retains its actual public result and
proposal, and permanently excludes its author in both successors. No
probability, information equality or native receipt cause is a field. -/
inductive ProposalRecoveryForeignRefinement (who : Player)
    (first : CommitRecoveryState setup.program)
    (prior : setup.proposalRecoveryProtocol.Trace (some first)) :
    setup.proposalRecoveryProtocol.History → setup.proposalRecoveryProtocol.History → Prop where
  | initial : ProposalRecoveryForeignRefinement who first prior
      ⟨some first, prior⟩ ⟨some first, prior⟩
  | extend {leftState rightState leftAfter rightAfter : setup.proposalRecoveryProtocol.State}
      (left : setup.proposalRecoveryProtocol.Trace leftState)
      (right : setup.proposalRecoveryProtocol.Trace rightState)
      (earlier : ProposalRecoveryForeignRefinement who first prior
        ⟨leftState, left⟩ ⟨rightState, right⟩)
      (leftJoint rightJoint : Player → Option (ProposalRecoveryMove Player L))
      (leftLegal : setup.proposalRecoveryProtocol.Legal leftState leftJoint)
      (rightLegal : setup.proposalRecoveryProtocol.Legal rightState rightJoint)
      (leftSupported : leftAfter ∈
        (setup.proposalRecoveryProtocol.step leftState ⟨leftJoint, leftLegal⟩).support)
      (rightSupported : rightAfter ∈
        (setup.proposalRecoveryProtocol.step rightState ⟨rightJoint, rightLegal⟩).support)
      (labels : ForeignDisclosureLabels who leftJoint rightJoint)
      (publicResult : setup.attemptPublicSignal who leftAfter =
        setup.attemptPublicSignal who rightAfter)
      (proposal : setup.proposalRecoveryProposalOf leftState leftJoint =
        setup.proposalRecoveryProposalOf rightState rightJoint)
      (changed : leftJoint ≠ rightJoint →
        ∃ submitted, setup.proposalRecoveryProposalOf leftState leftJoint = some submitted)
      (excluded : ∀ owner, leftJoint owner ≠ rightJoint owner →
        owner ∈ (setup.commitRecoveryPublic leftAfter).1 ∧
          owner ∈ (setup.commitRecoveryPublic rightAfter).1) :
      ProposalRecoveryForeignRefinement who first prior
        ⟨leftAfter, left.extend leftJoint leftLegal leftSupported⟩
        ⟨rightAfter, right.extend rightJoint rightLegal rightSupported⟩

namespace ProposalRecoveryForeignRefinement

variable {setup} {who : Player} {first : CommitRecoveryState setup.program}
  {prior : setup.proposalRecoveryProtocol.Trace (some first)}
  {left right : setup.proposalRecoveryProtocol.History}

theorem retained (refines : setup.ProposalRecoveryForeignRefinement who first prior left right) :
    TracePrefix prior left.trace ∧ TracePrefix prior right.trace := by
  induction refines with
  | initial => exact ⟨.refl, .refl⟩
  | extend _ _ _ leftJoint rightJoint leftLegal rightLegal leftSupported rightSupported
      _ _ _ _ _ ih =>
      exact ⟨.extend ih.1 leftJoint leftLegal leftSupported,
        .extend ih.2 rightJoint rightLegal rightSupported⟩

theorem publicRecall
    (refines : setup.ProposalRecoveryForeignRefinement who first prior left right) :
    setup.proposalRecoveryPublicRecall who left.trace =
      setup.proposalRecoveryPublicRecall who right.trace := by
  induction refines with
  | initial => rfl
  | extend _ _ _ _ _ _ _ _ _ _ publicResult proposal _ _ ih =>
      simp only [proposalRecoveryPublicRecall, publicResult, proposal, ih]

theorem coordinate
    (refines : setup.ProposalRecoveryForeignRefinement who first prior left right) :
    (setup.proposalRecoveryJointRecall left.trace).map (fun joint => joint who) =
      (setup.proposalRecoveryJointRecall right.trace).map (fun joint => joint who) := by
  induction refines with
  | initial => rfl
  | extend _ _ _ _ _ _ _ _ _ labels _ _ _ _ ih =>
      simp only [proposalRecoveryJointRecall, List.map_cons, labels.own, ih]

/-- Permitted foreign cause refinements preserve the observer's ENTIRE
labeled source information, including all canceled own binding tags. The
full observer theorem uses the original initializer and supported steps. -/
theorem info_eq
    (refines : setup.ProposalRecoveryForeignRefinement who first prior left right) :
    setup.proposalRecoveryModel.infoOf who left.trace =
      setup.proposalRecoveryModel.infoOf who right.trace := by
  exact setup.proposalRecovery_info_eq_of_observed_prefixes who first first prior prior
    rfl rfl rfl left.trace right.trace refines.retained.1 refines.retained.2
    refines.publicRecall refines.coordinate

/-- Every still-surviving observer sees the same complete source history.
A changed author's own label cannot be used here: the actual changed step
permanently excludes that author before any later active policy is queried. -/
theorem for_surviving_observer
    (refines : setup.ProposalRecoveryForeignRefinement who first prior left right)
    (observer : Player)
    (leftSurvives : observer ∉ (setup.commitRecoveryPublic left.state).1)
    (rightSurvives : observer ∉ (setup.commitRecoveryPublic right.state).1) :
    setup.ProposalRecoveryForeignRefinement observer first prior left right := by
  induction refines with
  | initial => exact .initial
  | @extend leftState rightState leftAfter rightAfter left right _ leftJoint rightJoint leftLegal
      rightLegal leftSupported rightSupported labels publicResult proposal changed excluded ih =>
      have previousLeft : observer ∉ (setup.commitRecoveryPublic leftState).1 := by
        intro member
        exact leftSurvives (setup.commitRecovery_step_excluded_subset
          (proposalRecoveryJoint leftJoint) (setup.proposalRecovery_erase_legal _ leftLegal)
            leftSupported member)
      have previousRight : observer ∉ (setup.commitRecoveryPublic rightState).1 := by
        intro member
        exact rightSurvives (setup.commitRecovery_step_excluded_subset
          (proposalRecoveryJoint rightJoint) (setup.proposalRecovery_erase_legal _ rightLegal)
            rightSupported member)
      have own : leftJoint observer = rightJoint observer := by
        by_contra differs
        exact leftSurvives (excluded observer differs).1
      exact .extend left right (ih previousLeft previousRight) leftJoint rightJoint leftLegal
        rightLegal leftSupported rightSupported (labels.for_observer observer own)
        (setup.attemptPublicSignal_eq_for_observer who observer _ _ publicResult)
        proposal changed excluded

/-- Full information equality at every surviving policy input is a
consequence of the actual finite refinement, not a matching premise. -/
theorem surviving_info_eq
    (refines : setup.ProposalRecoveryForeignRefinement who first prior left right)
    (observer : Player)
    (leftSurvives : observer ∉ (setup.commitRecoveryPublic left.state).1)
    (rightSurvives : observer ∉ (setup.commitRecoveryPublic right.state).1) :
    setup.proposalRecoveryModel.infoOf observer left.trace =
      setup.proposalRecoveryModel.infoOf observer right.trace :=
  (refines.for_surviving_observer observer leftSurvives rightSurvives).info_eq

end ProposalRecoveryForeignRefinement

end Vegas.SourceProgram.Setup

namespace Vegas

open SourceProgram SourceProgram.Setup EventGraph EventGraphRuntime Interaction
  GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]

omit [Fintype Player] in
private theorem fillCommitPrefix_eq_withoutMisses
    {wholeΓ : SourceCtx Player L} {wholeO : Finset VarId}
    (whole : SourceProgram Player L wholeΓ wholeO)
    {Γ Δ : SourceCtx Player L} {O P : Finset VarId} (block : SourceProgram.CommitPrefix Γ O Δ P) :
    ∀ (suffix : SourceProgram Player L Δ P)
      (embedding : OutputEmbedding (inputLayout wholeΓ) (outputLayout whole)
        (block.prepend suffix)) (refs : ContextRefs (graphLayout whole) Γ)
      (store : Store (graphLayout whole)) (entry : SourceProgram.Config Player L Γ)
      (excluded : Finset Player) (finished : SourceProgram.Config Player L Δ)
      (after : Finset Player) (attempt : block.Attempt entry excluded finished after)
      (replacement : SourceProgram.Config Player L Γ),
      (commitBlockRefs whole block suffix embedding refs).Agrees finished.state store →
      fillCommitPrefix whole block suffix embedding store replacement =
        attempt.withoutMisses ∅ replacement := by
  induction block with
  | nil =>
      intro suffix embedding refs store entry excluded finished after attempt replacement _agree
      cases attempt
      rfl
  | @commit Γ O Δ P name owner payload fresh guard rest ih =>
      intro suffix embedding refs store entry excluded finished after attempt replacement agree
      let zero : Fin (eventCount
          ((SourceProgram.CommitPrefix.commit name owner fresh guard rest).prepend suffix)) :=
        ⟨0, by simp only [SourceProgram.CommitPrefix.prepend, eventCount]; omega⟩
      let field : FieldRef (graphLayout whole) (.binding owner payload) := by
        simpa only [zero, SourceProgram.CommitPrefix.prepend, outputLayout, Fin.mk_zero,
          Fin.cases_zero]
          using embedding.ref zero
      let laterEmbedding := embedding.tail (rest.prepend suffix)
        (by simp only [SourceProgram.CommitPrefix.prepend, eventCount]) (fun _ => rfl)
      let laterRefs := refs.cons (name := name) (cell := .commitment owner payload) field
      cases attempt with
      | active _active choice _missed _valid later =>
          have middle : laterRefs.Agrees
              (commitSuccessor name guard entry choice).state store :=
            commitBlockRefs_agrees_entry whole rest suffix laterEmbedding laterRefs
              store (commitSuccessor name guard entry choice) _ finished after later agree
          have stored := middle (.here (x := name) (τ := CellTy.commitment owner payload))
          change field.get? store = some choice at stored
          change fillCommitPrefix whole rest suffix laterEmbedding store
              (commitSuccessor name guard replacement ((field.get? store).getD .failure)) =
            later.withoutMisses ∅ (commitSuccessor name guard replacement choice)
          rw [stored, Option.getD_some]
          exact ih suffix laterEmbedding laterRefs store _ _ finished after later _ agree
      | excluded _inactive later =>
          have middle : laterRefs.Agrees
              (automaticCommit name owner payload entry).state store :=
            commitBlockRefs_agrees_entry whole rest suffix laterEmbedding laterRefs
              store (automaticCommit name owner payload entry) _ finished after later agree
          have stored := middle (.here (x := name) (τ := CellTy.commitment owner payload))
          change field.get? store = some .failure at stored
          simp only [SourceProgram.CommitPrefix.Attempt.withoutMisses, Finset.notMem_empty,
            ↓reduceIte]
          change fillCommitPrefix whole rest suffix laterEmbedding store
              (commitSuccessor name guard replacement ((field.get? store).getD .failure)) =
            later.withoutMisses ∅ (commitSuccessor name guard replacement .failure)
          rw [stored, Option.getD_some]
          exact ih suffix laterEmbedding laterRefs store _ _ finished after later _ agree

omit [Fintype Player] in
private theorem fillCommitPrefix_view_of_attempt_agrees
    {wholeΓ : SourceCtx Player L} {wholeO : Finset VarId}
    (whole : SourceProgram Player L wholeΓ wholeO)
    {Γ Δ : SourceCtx Player L} {O P : Finset VarId} (block : SourceProgram.CommitPrefix Γ O Δ P)
    (suffix : SourceProgram Player L Δ P)
    (embedding : OutputEmbedding (inputLayout wholeΓ) (outputLayout whole)
      (block.prepend suffix)) (refs : ContextRefs (graphLayout whole) Γ)
    (store : Store (graphLayout whole)) (entry : SourceProgram.Config Player L Γ)
    (excluded : Finset Player) (finished : SourceProgram.Config Player L Δ)
    (after : Finset Player) (attempt : block.Attempt entry excluded finished after)
    (agree : (commitBlockRefs whole block suffix embedding refs).Agrees finished.state store)
    (who : Player) (survives : who ∉ after) :
    finished.view who = (fillCommitPrefix whole block suffix embedding store entry).view who := by
  have view := attempt.withoutMisses_surviving_view ∅ entry who rfl survives
  rw [← fillCommitPrefix_eq_withoutMisses whole block suffix embedding refs store entry excluded
    finished after attempt entry agree] at view
  exact view

omit [Fintype Player] in
private theorem commitPrefix_observe_lift_of_view
    {Γ Δ : SourceCtx Player L} {O P : Finset VarId}
    (block : SourceProgram.CommitPrefix Γ O Δ P) (suffix : SourceProgram Player L Δ P)
    (who : Player) (left right : SourceProgram.Config Player L Δ)
    (same : left.view who = right.view who) :
    SourceProgram.ProtocolState.observe who (block.prepend suffix)
        (block.liftPoint suffix (SourceProgram.ProtocolState.entry suffix left)) =
      SourceProgram.ProtocolState.observe who (block.prepend suffix)
        (block.liftPoint suffix (SourceProgram.ProtocolState.entry suffix right)) := by
  induction block with
  | nil => exact SourceProgram.ProtocolState.observe_entry_congr who suffix left right same
  | commit _ _ _ _ _ ih => exact congrArg Sum.inr (ih suffix left right same)

omit [Fintype Player] in
private theorem fillCommitPrefix_rank_of_events
    {wholeΓ : SourceCtx Player L} {wholeO : Finset VarId}
    (whole : SourceProgram Player L wholeΓ wholeO)
    {Γ Δ Ξ : SourceCtx Player L} {O P Q : Finset VarId}
    (earlier : SourceProgram.CommitPrefix Γ O Δ P)
    (later : SourceProgram.CommitPrefix Δ P Ξ Q)
    (suffix : SourceProgram Player L Ξ Q)
    (full : OutputEmbedding (inputLayout wholeΓ) (outputLayout whole)
      ((earlier.append later).prepend suffix))
    (prefixEmbedding : OutputEmbedding (inputLayout wholeΓ) (outputLayout whole)
      (earlier.prepend (later.prepend suffix)))
    (same : ∀ left right, left.val = right.val → full.event left = prefixEmbedding.event right)
    (store : Store (graphLayout whole)) (entry : SourceProgram.Config Player L Γ)
    (who : Player) :
    ProtocolView.atRank who (earlier.prepend (later.prepend suffix)) earlier.length
        (SourceProgram.ProtocolState.observe who (earlier.prepend (later.prepend suffix))
          (earlier.liftPoint (later.prepend suffix)
            (later.liftPoint suffix (SourceProgram.ProtocolState.entry suffix
              (fillCommitPrefix whole (earlier.append later) suffix full store entry))))) =
      some (SourceProgram.ProtocolState.observe who (earlier.prepend (later.prepend suffix))
        (earlier.liftPoint (later.prepend suffix)
          (SourceProgram.ProtocolState.entry (later.prepend suffix)
            (fillCommitPrefix whole earlier (later.prepend suffix) prefixEmbedding store
              entry)))) := by
  induction earlier with
  | nil =>
      exact ProtocolView.atRank_zero_of_entryView who (later.prepend suffix) _ entry
        ((fillCommitPrefix_attempt whole later suffix full store entry).entryView suffix who
          (Finset.notMem_empty who))
  | @commit Γ O Δ P name owner payload fresh guard rest ih =>
      let fullZero : Fin (eventCount
          (((SourceProgram.CommitPrefix.commit name owner fresh guard rest).append later).prepend
            suffix)) := ⟨0, by
        simp only [SourceProgram.CommitPrefix.append, SourceProgram.CommitPrefix.prepend,
          eventCount]; omega⟩
      let prefixZero : Fin (eventCount
          ((SourceProgram.CommitPrefix.commit name owner fresh guard rest).prepend
            (later.prepend suffix))) := ⟨0, by
        simp only [SourceProgram.CommitPrefix.prepend, eventCount]; omega⟩
      let fullField : FieldRef (graphLayout whole) (.binding owner payload) :=
        ⟨.inr (full.event fullZero), full.layout_eq _⟩
      let prefixField : FieldRef (graphLayout whole) (.binding owner payload) :=
        ⟨.inr (prefixEmbedding.event prefixZero), prefixEmbedding.layout_eq _⟩
      have sameField : fullField = prefixField := by
        have coordinate : fullField.field = prefixField.field :=
          congrArg Sum.inr (same fullZero prefixZero rfl)
        rcases fullField with ⟨first, firstEq⟩
        rcases prefixField with ⟨second, secondEq⟩
        dsimp only at coordinate
        subst second
        rfl
      let fullTail := full.tail ((rest.append later).prepend suffix)
        (by simp only [SourceProgram.CommitPrefix.append, SourceProgram.CommitPrefix.prepend,
          eventCount]) (fun _ => rfl)
      let prefixTail := prefixEmbedding.tail (rest.prepend (later.prepend suffix))
        (by simp only [SourceProgram.CommitPrefix.prepend, eventCount]) (fun _ => rfl)
      have tailSame : ∀ left right, left.val = right.val →
          fullTail.event left = prefixTail.event right := by
        intro left right coordinate
        exact same (Fin.succ left) (Fin.succ right) (congrArg Nat.succ coordinate)
      have lower := ih later fullTail prefixTail tailSame
        (commitSuccessor name guard entry ((prefixField.get? store).getD .failure))
      change (ProtocolView.atRank who (rest.prepend (later.prepend suffix)) rest.length
        (SourceProgram.ProtocolState.observe who (rest.prepend (later.prepend suffix))
          (rest.liftPoint (later.prepend suffix)
            (later.liftPoint suffix (SourceProgram.ProtocolState.entry suffix
              (fillCommitPrefix whole (rest.append later) suffix fullTail store
                (commitSuccessor name guard entry
                  ((fullField.get? store).getD .failure)))))))).map Sum.inr = _
      rw [sameField, lower]
      rfl

omit [Fintype Player] in
private theorem source_rank_lift_cast
    {Γ Δ : SourceCtx Player L} {O P : Finset VarId}
    {whole : SourceProgram Player L Γ O} {first second : SourceProgram Player L Δ P}
    (same : first = second)
    (lift : SourceProgram.ProtocolState first → SourceProgram.ProtocolState whole)
    (origin : ProtocolSuffix whole first lift) (who : Player)
    (before later : SourceProgram.ProtocolState second) (rank : Nat)
    (read : ProtocolView.atRank who second rank
        (SourceProgram.ProtocolState.observe who second later) =
      some (SourceProgram.ProtocolState.observe who second before)) :
    ProtocolView.atRank who whole
        (instructionCount whole - instructionCount second + rank)
        (SourceProgram.ProtocolState.observe who whole
          (lift (cast (congrArg SourceProgram.ProtocolState same.symm) later))) =
      some (SourceProgram.ProtocolState.observe who whole
        (lift (cast (congrArg SourceProgram.ProtocolState same.symm) before))) := by
  cases same
  exact origin.atRank_lift who before later rank read

omit [Fintype Player] in
private theorem filled_prefix_decode_cast
    {wholeΓ Γ Δ : SourceCtx Player L} {wholeO O P : Finset VarId}
    (whole : SourceProgram Player L wholeΓ wholeO)
    (program : SourceProgram Player L Γ O)
    (earlier : SourceProgram.CommitPrefix Γ O Δ P) (suffix : SourceProgram Player L Δ P)
    (same : program = earlier.prepend suffix)
    (refs : ContextRefs (graphLayout whole) Γ)
    (embedding : OutputEmbedding (inputLayout wholeΓ) (outputLayout whole) program)
    (lift : SourceProgram.ProtocolState program → SourceProgram.ProtocolState whole)
    (views : ProtocolViewSuffix whole program refs embedding lift)
    (store : Store (graphLayout whole)) (entry : SourceProgram.Config Player L Γ)
    (who : Player) (selected : Fin (eventCount (earlier.prepend suffix)))
    (atEnd : selected.val = earlier.length)
    (agree : refs.Agrees entry.state store)
    (available : ∀ index : Fin (eventCount (earlier.prepend suffix)),
      index.val < earlier.length → eventOwner? (earlier.prepend suffix) index = some who →
        (((cast (congrArg (OutputEmbedding (inputLayout wholeΓ) (outputLayout whole)) same)
          embedding).ref index).get? store).isSome = true) :
    let prefixEmbedding := cast
      (congrArg (OutputEmbedding (inputLayout wholeΓ) (outputLayout whole)) same) embedding
    let filled := fillCommitPrefix whole earlier suffix prefixEmbedding store entry
    decodeEventView? whole (ContextRefs.initial wholeΓ (outputLayout whole))
        (outputEmbedding whole).ref who (prefixEmbedding.event selected)
        ((toEventGraph whole).playerStore who store) (filled.history who) =
      some (SourceProgram.ProtocolState.observe who whole
        (lift (cast (congrArg SourceProgram.ProtocolState same.symm)
          (earlier.liftPoint suffix (SourceProgram.ProtocolState.entry suffix filled))))) := by
  subst program
  dsimp only [cast_eq]
  have observation := fillCommitPrefix_observation whole earlier suffix embedding refs store entry
    who (decodeObservation?_eq_some refs who entry.state store agree) available
  have masked := (decodeObservation?_playerStore (graph := toEventGraph whole) who
    (commitBlockRefs whole earlier suffix embedding refs) store).trans observation
  have localView := decodeEventView?_commitPrefix_entry whole earlier suffix embedding refs
    ((toEventGraph whole).playerStore who store) _ who selected atEnd masked
  rw [views.decode, localView, Option.map_some]
  exact congrArg some (views.observe who _).symm

omit [Fintype Player] in
private theorem filled_prefix_rank_readback
    {wholeΓ Γ Δ Ξ : SourceCtx Player L} {wholeO O P Q : Finset VarId}
    (whole : SourceProgram Player L wholeΓ wholeO)
    (block : SourceProgram.CommitPrefix Γ O Ξ Q)
    (earlier : SourceProgram.CommitPrefix Γ O Δ P)
    (later : SourceProgram.CommitPrefix Δ P Ξ Q)
    (split : earlier.append later = block) (suffix : SourceProgram Player L Ξ Q)
    (refs : ContextRefs (graphLayout whole) Γ)
    (embedding : OutputEmbedding (inputLayout wholeΓ) (outputLayout whole)
      (block.prepend suffix))
    (lift : SourceProgram.ProtocolState (block.prepend suffix) →
      SourceProgram.ProtocolState whole)
    (origin : ProtocolSuffix whole (block.prepend suffix) lift)
    (views : ProtocolViewSuffix whole (block.prepend suffix) refs embedding lift)
    (store completedStore : Store (graphLayout whole)) (entry : SourceProgram.Config Player L Γ)
    (who : Player) (event : Fin (eventCount whole))
    (current : SourceProgram.ProtocolState whole)
    (agree : refs.Agrees entry.state store)
    (preserved : ∀ field value, store field = some value → completedStore field = some value)
    (rank : ProtocolView.atRank who whole event.val
      (SourceProgram.ProtocolState.observe who whole
        (lift (block.liftPoint suffix (SourceProgram.ProtocolState.entry suffix
          (fillCommitPrefix whole block suffix embedding completedStore entry))))) =
      some (SourceProgram.ProtocolState.observe who whole current)) :
    let association := (congrArg (fun block => block.prepend suffix) split).symm.trans
      (earlier.prepend_append later suffix)
    let prefixEmbedding := cast
      (congrArg (OutputEmbedding (inputLayout wholeΓ) (outputLayout whole)) association) embedding
    ∀ (selected : Fin (eventCount (earlier.prepend (later.prepend suffix)))),
      selected.val = earlier.length → prefixEmbedding.event selected = event →
      event.val = instructionCount whole - instructionCount (earlier.prepend
        (later.prepend suffix)) + earlier.length →
      (∀ index : Fin (eventCount (earlier.prepend (later.prepend suffix))),
        index.val < earlier.length →
        eventOwner? (earlier.prepend (later.prepend suffix)) index = some who →
        ((prefixEmbedding.ref index).get? store).isSome = true) →
      decodeEventView? whole (ContextRefs.initial wholeΓ (outputLayout whole))
          (outputEmbedding whole).ref who event ((toEventGraph whole).playerStore who store)
          (SourceProgram.Config.history
            (fillCommitPrefix whole earlier (later.prepend suffix) prefixEmbedding store
              entry) who) =
        some (SourceProgram.ProtocolState.observe who whole current) := by
  cases split
  intro association prefixEmbedding selected atEnd selectedEq coordinate available
  have sourceRank := fillCommitPrefix_rank_of_events whole earlier later suffix embedding
    prefixEmbedding (fun left right same => OutputEmbedding.event_cast whole association embedding
      left right same) completedStore entry who
  have extension := fillCommitPrefix_view_of_extension whole earlier (later.prepend suffix)
    prefixEmbedding store completedStore entry who preserved available
  have pointView := commitPrefix_observe_lift_of_view earlier (later.prepend suffix) who _ _
    extension
  rw [← pointView] at sourceRank
  rw [← earlier.liftPoint_append later suffix] at sourceRank
  have wholeRank := source_rank_lift_cast association lift origin who _ _ earlier.length sourceRank
  simp only [cast_cast, cast_eq] at wholeRank
  rw [← coordinate, rank] at wholeRank
  have decoded := filled_prefix_decode_cast whole ((earlier.append later).prepend suffix)
    earlier (later.prepend suffix) association refs embedding lift views store entry who selected
    atEnd agree available
  dsimp only at decoded
  rw [selectedEq] at decoded
  exact decoded.trans wholeRank.symm

omit [Fintype Player] in
private theorem source_binding_prefix_addresses
    (setup : Setup (Player := Player) (L := L)) (who : Player)
    (point : SourceProgram.ProtocolState setup.program) (excluded : Finset Player)
    (generation : Nat)
    (prior : setup.commitRecoveryProtocol.Trace
      (some (CommitRecoveryState.atPoint point excluded generation)))
    (committing : SourceProgram.ProtocolState.atCommit setup.program point = true)
    (survives : who ∉ excluded)
    {state : setup.commitRecoveryProtocol.State}
    (trace : setup.commitRecoveryProtocol.Trace state) (kept : TracePrefix prior trace)
    (inside : trace.length + SourceProgram.ProtocolState.commitEnd setup.program point <
      prior.length + SourceProgram.ProtocolState.remaining setup.program point)
    (unchanged : (setup.commitRecoveryPublic state).1 = excluded) :
    setup.recoveryAddressWord trace = setup.recoveryAddressWord prior ++
      (List.range (trace.length - prior.length)).map (fun index =>
        (some (instructionCount setup.program -
          SourceProgram.ProtocolState.remaining setup.program point + index + 1),
          excluded, generation, instructionCount setup.program -
            SourceProgram.ProtocolState.remaining setup.program point)) := by
  induction kept with
  | refl => simp only [Nat.sub_self, List.range_zero, List.map_nil, List.append_nil]
  | @extend source target earlier retained joint legal supported ih =>
      have previousInside : earlier.length +
          SourceProgram.ProtocolState.commitEnd setup.program point < prior.length +
            SourceProgram.ProtocolState.remaining setup.program point := by
        simp only [Trace.length] at inside
        omega
      have lower := setup.commitRecovery_public_excluded_of_reaches retained.reachesWithin
      have upper := setup.commitRecovery_step_excluded_subset joint legal supported
      have previousUnchanged : (setup.commitRecoveryPublic source).1 = excluded := by
        apply Finset.Subset.antisymm
        · intro owner member
          exact unchanged ▸ upper member
        · exact lower
      have surviving : who ∉ (setup.commitRecoveryPublic target).1 := fun member =>
        survives (unchanged ▸ member)
      obtain ⟨current, _replay, endpoint, saved, _entryExcluded, currentGeneration, _rest⟩ :=
        setup.commitRecovery_noMiss_prefix_information who point excluded generation prior
          committing (earlier.extend joint legal supported) (.extend retained joint legal supported)
            inside surviving
      obtain ⟨rankCurrent, rankEndpoint, _currentCommit, _end, remaining⟩ :=
        setup.commitRecovery_prefix_inside_commit _ prior committing
          (earlier.extend joint legal supported) (.extend retained joint legal supported) inside
      have currentEq : rankCurrent = current := Option.some.inj (rankEndpoint.symm.trans endpoint)
      subst rankCurrent
      change (earlier.extend joint legal supported).length +
        SourceProgram.ProtocolState.remaining setup.program current.point =
        prior.length + SourceProgram.ProtocolState.remaining setup.program point at remaining
      have excludedEq : current.excluded = excluded := by
        simpa only [endpoint, Setup.commitRecoveryPublic] using unchanged
      have address : target.elim (none, (∅, 0, 0)) CommitRecoveryState.publicAddress =
          (some (instructionCount setup.program -
            SourceProgram.ProtocolState.remaining setup.program point +
              ((earlier.extend joint legal supported).length - prior.length)),
            excluded, generation, instructionCount setup.program -
              SourceProgram.ProtocolState.remaining setup.program point) := by
        conv_lhs => rw [endpoint]
        dsimp only [Option.elim, CommitRecoveryState.publicAddress]
        rw [saved, currentGeneration, excludedEq]
        congr 2
        have bounded := SourceProgram.ProtocolState.remaining_le_instructionCount setup.program
          point
        have length := retained.length_le
        simp only [Trace.length] at remaining ⊢
        omega
      have count : (earlier.extend joint legal supported).length - prior.length =
          (earlier.length - prior.length) + 1 := by
        have length := retained.length_le
        simp only [Trace.length]
        omega
      rw [setup.recoveryAddressWord_extend, ih previousInside previousUnchanged, address, count,
        List.range_succ, List.map_append, List.map_singleton, List.append_assoc]
      simp only [Nat.add_assoc]

omit [Fintype Player] in
private theorem checkpoint_history_cast
    {setup : Setup (Player := Player) (L := L)} {mode : ExecutionMode}
    {first second : PhaseRuntimeState (serviceGraph setup mode)} (same : first = second)
    (checkpoint : RecoverySourceCheckpoint setup mode first) :
    (⟨_, (cast (congrArg (RecoverySourceCheckpoint setup mode) same) checkpoint).trace⟩ :
      setup.commitRecoveryProtocol.History) = ⟨_, checkpoint.trace⟩ := by
  cases same
  rfl

omit [Fintype Player] in
private theorem initialized_checkpoint_history
    (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
    (plan : RuntimePhasePlan (serviceGraph setup mode))
    (theta : State L setup.context) (supported : theta ∈ setup.initialLaw.support) :
    (⟨_, (RecoverySourceCheckpoint.initialized setup mode plan theta supported).trace⟩ :
      setup.commitRecoveryProtocol.History) =
      ⟨_, (RecoverySourceCheckpoint.initial setup mode plan theta supported).trace⟩ :=
  checkpoint_history_cast (phaseInitial_eq_raw plan (encodeInputs theta)).symm _

omit [Fintype Player] in
private theorem initialized_lift_info_eq
    (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
    (plan : RuntimePhasePlan (serviceGraph setup mode)) (who : Player)
    (left right : State L setup.context)
    (leftSupported : left ∈ setup.initialLaw.support)
    (rightSupported : right ∈ setup.initialLaw.support)
    (leftLabels rightLabels : setup.commitRecoveryProtocol.StepEvent → Player → Bool)
    (observed : sourceObserve who left = sourceObserve who right) :
    setup.proposalRecoveryModel.infoOf who (setup.proposalRecoveryLiftTrace leftLabels
        (RecoverySourceCheckpoint.initialized setup mode plan left leftSupported).trace) =
      setup.proposalRecoveryModel.infoOf who (setup.proposalRecoveryLiftTrace rightLabels
        (RecoverySourceCheckpoint.initialized setup mode plan right rightSupported).trace) := by
  have leftRaw := congrArg (fun history : setup.commitRecoveryProtocol.History =>
    setup.proposalRecoveryModel.infoOf who (setup.proposalRecoveryLiftTrace leftLabels
      history.trace)) (initialized_checkpoint_history setup mode plan left leftSupported)
  have rightRaw := congrArg (fun history : setup.commitRecoveryProtocol.History =>
    setup.proposalRecoveryModel.infoOf who (setup.proposalRecoveryLiftTrace rightLabels
      history.trace)) (initialized_checkpoint_history setup mode plan right rightSupported)
  rw [leftRaw, rightRaw]
  dsimp only [RecoverySourceCheckpoint.initial, Setup.proposalRecoveryLiftTrace,
    Setup.proposalRecoveryLiftJoint, Setup.proposalRecoveryModel, Setup.proposalRecoverySignals,
    InfoSignals.withOwnPlayRecall, InfoSignals.infoOf, Setup.proposalRecoveryPublic,
    Setup.proposalRecoveryProposalOf, Setup.commitRecoveryPrivate, Setup.commitRecoveryPublic,
    CommitRecoveryState.atPoint]
  simp only [Option.map_none, Option.map_some, id_eq,
    SourceProgram.ProtocolState.remaining_entry]
  have initialState : setup.commitRecoveryProtocol.init = none := rfl
  simp only [initialState, Option.bind_none]
  have entries := SourceProgram.ProtocolState.observe_entry_congr who setup.program
    (setup.initialConfig left) (setup.initialConfig right) (Prod.ext observed rfl)
  change (((some (SourceProgram.ProtocolState.observe who setup.program
        (SourceProgram.ProtocolState.entry setup.program (setup.initialConfig left))),
      (((∅ : Finset Player), 0,
        instructionCount setup.program - instructionCount setup.program), none)),
      [(none, (((∅ : Finset Player), 0, 0), none))]), []) =
    (((some (SourceProgram.ProtocolState.observe who setup.program
        (SourceProgram.ProtocolState.entry setup.program (setup.initialConfig right))),
      (((∅ : Finset Player), 0,
        instructionCount setup.program - instructionCount setup.program), none)),
      [(none, (((∅ : Finset Player), 0, 0), none))]), [])
  rw [entries]

/-- Actual initialized compiler and source-block witnesses for a canonical
source cut before an ordinary native binding. The completion key belongs
only to the current generation. Older canceled declarations remain in the
checkpoint's literal source past. All value, trace and frontier conditions
are support obligations of the native augmentation, not Bayes assumptions. -/
structure PhaseProposalCanonicalBindingCut
    (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
    (runtime : EventGraphRuntime (serviceGraph setup mode))
    (leaks : MessageNetwork.ObservationRule Player
      (CommitAttemptPacket (serviceGraph setup mode)))
    (bounds : MessageBounds (serviceGraph setup mode))
    (plan : RuntimePhasePlan (serviceGraph setup mode))
    (values : ∀ owner (key : setup.ProposalRecoveryComponent owner),
      PMF (setup.CommitRecoveryValueChoice owner key.1))
    (horizon : Nat) (scheduler : (phaseApplication runtime leaks).Scheduler)
    (control : (phaseApplication runtime leaks).Control)
    (nativeTrace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      ((setup.initialLaw.map encodeInputs).map (PhaseRuntimeState.initial plan))
      horizon scheduler).Trace (some control))
    (who : Player) (event : (serviceGraph setup mode).EventId) where
  active : control.actor = some who
  request : control.execution.application.SeedRequest who
    ⟨control.execution.application.attempt, event⟩
  unsent : ∀ message ∈ (phaseApplication runtime leaks).outputs (control.execution.recall who),
    PhaseCount.event? message.payload ≠ some ⟨control.execution.application.attempt, event⟩
  payload : L.Ty
  binding : (serviceGraph setup mode).outputLayout event = .binding who payload
  phase : RuntimePhase (serviceGraph setup mode)
  installed : control.execution.application.phases.head? = some phase
  commitment : phase.kind = .commitment
  inside : event ∈ phase.events
  entry : (phaseApplication runtime leaks).Control
  entryTrace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
    ((setup.initialLaw.map encodeInputs).map (PhaseRuntimeState.initial plan))
    horizon scheduler).Trace (some entry)
  nativeRetained : TracePrefix entryTrace nativeTrace
  sameAttempt : entry.execution.application.attempt = control.execution.application.attempt
  entryInstalled : entry.execution.application.phases.head? = some phase
  entryIdle : entry.actor = none
  entryExcluded : entry.execution.application.entry.excluded =
    entry.execution.application.current.excluded
  fresh : ∀ owner, ∀ record ∈ entry.execution.recall owner,
    record.beforeView.application.2.attempt ≠ entry.execution.application.attempt
  witness : RecoverySourceWitness setup mode plan entry.execution.application
  archived : witness.checkpoint.ArchivedProposals entry.execution.network.inputs
  targetContext : SourceCtx Player L
  targetNames : Finset VarId
  block : SourceProgram.CommitPrefix witness.checkpoint.residual.context
    witness.checkpoint.residual.names targetContext targetNames
  suffix : SourceProgram Player L targetContext targetNames
  cursor : PhaseProposalOrdinarySourceCursor setup mode runtime leaks plan entry phase block suffix
  size : block.length = phase.high - phase.low
  offset : cursor.offset = phase.low
  source : cursor.source = witness.checkpoint.source
  config : cursor.config = entry.execution.application.current.native.config
  cursorHistory : (⟨some cursor.current, cursor.trace⟩ : setup.proposalRecoveryProtocol.History) =
    ⟨_, setup.proposalRecoveryLiftTrace
      (nativeArchiveLabels setup (PhaseProposal.sourceArchive entry.execution.network.inputs))
      witness.checkpoint.trace⟩
  refs : cursor.refs = witness.checkpoint.refs
  reconstruct : block.prepend suffix = witness.checkpoint.residual.tail
  embedding : cursor.embedding = cast (congrArg (fun program => OutputEmbedding
    (inputLayout setup.context) (outputLayout setup.program) program) reconstruct.symm)
      witness.checkpoint.embedding
  lift : ∀ point, cursor.lift point = witness.checkpoint.residual.lift
    (cast (congrArg SourceProgram.ProtocolState reconstruct) point)
  theta : State L setup.context
  thetaSupported : theta ∈ setup.initialLaw.support
  originalInputs : control.execution.application.current.native.config.inputs = encodeInputs theta
  initializer : CommitRecoveryState setup.program
  initializerTrace : setup.proposalRecoveryProtocol.Trace (some initializer)
  initialized : (⟨some initializer, initializerTrace⟩ : setup.proposalRecoveryProtocol.History) =
    ⟨_, setup.proposalRecoveryLiftTrace
      (nativeArchiveLabels setup (PhaseProposal.sourceArchive entry.execution.network.inputs))
      (RecoverySourceCheckpoint.initialized setup mode plan theta thetaSupported).trace⟩
  sourceRetained : TracePrefix initializerTrace cursor.trace
  completed : setup.proposalRecoveryProtocol.History
  key : (serviceGraph setup mode).SemanticKey
  blockResult : PhaseProposalOrdinarySourceBlockResult setup mode block suffix cursor.refs
    cursor.embedding cursor.lift cursor.source cursor.current cursor.trace (completed, key)
  sourceSupported : completed ∈ (setup.proposalRecoveryModel.runBehavioralFrom
    (setup.proposalRecoveryNormalizedTrembledProfile
      0 le_rfl zero_le_one 0 le_rfl zero_le_one 0 le_rfl zero_le_one values)
    block.length ⟨some cursor.current, cursor.trace⟩).support
  graphSupported : key ∈ ((serviceGraph setup mode).canonicalContinuation
    (phaseProposalBindingPotentialProfile setup mode runtime leaks plan entry.execution phase
      values)
    cursor.config).support
  lockedStore : ∀ field value,
    control.execution.application.current.native.config.store field = some value →
      key.2.1 field = some value
  lockedEmissions : ∀ owner, owner ∉ cursor.current.excluded →
    ∀ record ∈ control.execution.recall owner,
      record.beforeView.application.2.attempt = control.execution.application.attempt →
      ∀ message, record.emitted = some message →
      ∀ (declared : (serviceGraph setup mode).EventId) (domain : L.Ty)
        (output : (serviceGraph setup mode).outputLayout declared = .binding owner domain)
        (value : L.Val domain),
      PhaseCount.event? message.payload =
        some ⟨control.execution.application.attempt, declared⟩ →
      record.action.transmission.bind PhaseProposal.bindingPreparation = some ⟨domain, value⟩ →
      (⟨.inr declared, output⟩ : FieldRef (graphLayout setup.program)
        (.binding owner domain)).get? key.2.1 = some (.success value)
  current : CommitRecoveryState setup.program
  trace : setup.proposalRecoveryProtocol.Trace (some current)
  past : TracePrefix cursor.trace trace
  future : TracePrefix trace completed.trace
  clock : trace.length = cursor.trace.length + (event.val - phase.low)
  rank : instructionCount setup.program -
      SourceProgram.ProtocolState.remaining setup.program current.point =
    event.val
  actor : SourceProgram.ProtocolState.actor setup.program current.point = some who
  atCommit : SourceProgram.ProtocolState.atCommit setup.program current.point = true
  survives : who ∉ current.excluded

namespace PhaseProposalCanonicalBindingCut

variable {setup : Setup (Player := Player) (L := L)} {mode : ExecutionMode}
  {runtime : EventGraphRuntime (serviceGraph setup mode)}
  {leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode))}
  {bounds : MessageBounds (serviceGraph setup mode)}
  {plan : RuntimePhasePlan (serviceGraph setup mode)}
  {values : ∀ owner (key : setup.ProposalRecoveryComponent owner),
    PMF (setup.CommitRecoveryValueChoice owner key.1)}
  {horizon : Nat} {scheduler : (phaseApplication runtime leaks).Scheduler}
  {control : (phaseApplication runtime leaks).Control}
  {nativeTrace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
    ((setup.initialLaw.map encodeInputs).map (PhaseRuntimeState.initial plan))
    horizon scheduler).Trace (some control)}
  {who : Player} {event : (serviceGraph setup mode).EventId}

/-- The arbitrary supplied interior source cut is read at its rank from the
SAME completed source history and typed Attempt. This does not select another
source path from an equal terminal store. -/
theorem final_view_rank
    (cut : PhaseProposalCanonicalBindingCut setup mode runtime leaks bounds plan values
      horizon scheduler control nativeTrace who event) :
    ∃ (finished : SourceProgram.Config Player L cut.targetContext)
      (last : CommitRecoveryState setup.program)
      (lastTrace : setup.proposalRecoveryProtocol.Trace (some last))
      (_attempt : cut.block.Attempt cut.cursor.source cut.cursor.current.excluded
        finished last.excluded),
      cut.completed = ⟨some last, lastTrace⟩ ∧
      last.point = cut.cursor.lift
        (cut.block.liftPoint cut.suffix (SourceProgram.ProtocolState.entry cut.suffix finished)) ∧
      (commitBlockRefs setup.program cut.block cut.suffix cut.cursor.embedding
        cut.cursor.refs).Agrees finished.state cut.key.2.1 ∧
      last.excluded = cut.cursor.current.excluded ∧
      ProtocolView.atRank who setup.program event.val
        (SourceProgram.ProtocolState.observe who setup.program last.point) =
          some (SourceProgram.ProtocolState.observe who setup.program cut.current.point) := by
  obtain ⟨finished, last, lastTrace, attempt, completed, point, excluded, _generation,
    _live, agrees, _semanticWord, _labeledWord⟩ := cut.blockResult
  have endpoint : cut.completed.state = some last :=
    congrArg (fun history : setup.proposalRecoveryProtocol.History => history.state) completed
  have earlier := setup.proposalRecoveryEraseTrace_prefix cut.past
  have later := setup.proposalRecoveryEraseTrace_prefix cut.future
  have lower := setup.commitRecovery_public_excluded_of_reaches earlier.reachesWithin
  have upper := setup.commitRecovery_public_excluded_of_reaches later.reachesWithin
  change cut.cursor.current.excluded ⊆ cut.current.excluded at lower
  change cut.current.excluded ⊆ (setup.commitRecoveryPublic cut.completed.state).1 at upper
  rw [endpoint] at upper
  change cut.current.excluded ⊆ last.excluded at upper
  have currentExcluded : cut.current.excluded = cut.cursor.current.excluded :=
    Finset.Subset.antisymm (by simpa only [excluded] using upper) lower
  have cursorEntry : cut.cursor.current.entryExcluded = cut.cursor.current.excluded :=
    cut.cursor.entryExcluded.trans cut.cursor.excluded.symm
  have currentEntry := (setup.commitRecovery_clean_rank_of_reaches who earlier.reachesWithin
    cut.cursor.current cut.current rfl rfl cursorEntry currentExcluded cut.survives).1
  have lastExcluded : last.excluded = cut.current.excluded :=
    excluded.trans currentExcluded.symm
  have lastSurvives : who ∉ last.excluded := fun member =>
    cut.survives (lastExcluded ▸ member)
  have rankRead := (setup.commitRecovery_clean_rank_of_reaches who later.reachesWithin
    cut.current last rfl endpoint currentEntry lastExcluded lastSurvives).2
  have position : ProtocolView.position who setup.program
      (SourceProgram.ProtocolState.observe who setup.program cut.current.point) = event.val := by
    have positional := ProtocolView.position_add_remaining who setup.program cut.current.point
    have exactRank := cut.rank
    omega
  have read := rankRead event.val (by rw [position])
  rw [← position, ProtocolView.atRank_position] at read
  exact ⟨finished, last, lastTrace, attempt, completed, point, agrees, excluded, by
    simpa only [position] using read⟩

/-- The supplied cut is the original rank projection of the completed
locked store, with the surviving owner's entire source action history.
The equality uses the SAME completed typed attempt and source suffix. -/
theorem filled_rank
    (cut : PhaseProposalCanonicalBindingCut setup mode runtime leaks bounds plan values
      horizon scheduler control nativeTrace who event) :
    ProtocolView.atRank who setup.program event.val
        (SourceProgram.ProtocolState.observe who setup.program
          (cut.cursor.lift (cut.block.liftPoint cut.suffix
            (SourceProgram.ProtocolState.entry cut.suffix
              (fillCommitPrefix setup.program cut.block cut.suffix cut.cursor.embedding
                cut.key.2.1 cut.cursor.source))))) =
      some (SourceProgram.ProtocolState.observe who setup.program cut.current.point) := by
  obtain ⟨finished, last, _lastTrace, attempt, _completed, point, agrees, excluded, rank⟩ :=
    cut.final_view_rank
  have earlier := setup.commitRecovery_public_excluded_of_reaches
    (setup.proposalRecoveryEraseTrace_prefix cut.past).reachesWithin
  change cut.cursor.current.excluded ⊆ cut.current.excluded at earlier
  have surviving : who ∉ last.excluded := fun member =>
    cut.survives (earlier (excluded ▸ member))
  have configView := fillCommitPrefix_view_of_attempt_agrees setup.program cut.block cut.suffix
    cut.cursor.embedding cut.cursor.refs cut.key.2.1 cut.cursor.source
    cut.cursor.current.excluded finished last.excluded attempt agrees who surviving
  have localView := commitPrefix_observe_lift_of_view cut.block cut.suffix who _ _ configView
  have fullView := (cut.cursor.views.observe who _).trans
    ((congrArg (cut.cursor.views.view who) localView).trans
      (cut.cursor.views.observe who _).symm)
  rw [point, fullView] at rank
  exact rank

/-- Every supported completion and its supplied interior cut have the full
source view read from this actual native callback. The retained source past
supplies all archived owned actions, including accepted canceled bindings. -/
theorem source_view
    (cut : PhaseProposalCanonicalBindingCut setup mode runtime leaks bounds plan values
      horizon scheduler control nativeTrace who event) :
    phaseSurvivingSourceView? setup mode runtime leaks who event
        (control.execution.observe (phaseApplication runtime leaks) who) =
      some (SourceProgram.ProtocolState.observe who setup.program cut.current.point) := by
  let inputs := setup.initialLaw.map encodeInputs
  let initial := inputs.map (PhaseRuntimeState.initial plan)
  let menu := PhaseCount.onePacketMenu runtime leaks bounds
  let raw := menu.toRawTrace initial horizon scheduler nativeTrace
  let entryRaw := menu.toRawTrace initial horizon scheduler cut.entryTrace
  have initialized : ∀ state ∈ initial.support, state.Ordered := by
    intro state supported
    obtain ⟨draw, _supported, rfl⟩ := PMF.support_map .. ▸ supported
    exact PhaseRuntimeState.initial_ordered plan draw
  have ordered := (phaseApplication_seedOrder runtime leaks).history initial horizon scheduler
    initialized entryRaw
  have saved := ((phase_attempt_progress_of_prefix runtime leaks menu initial initialized
    horizon scheduler cut.entry control cut.entryTrace nativeTrace cut.nativeRetained
      ordered).2.2 cut.sameAttempt).symm
  have controls := phase_attempt_metadata_of_prefix runtime leaks menu initial initialized horizon
    scheduler cut.entry control cut.entryTrace nativeTrace cut.nativeRetained ordered
      cut.sameAttempt
  have retired : control.execution.application.retired =
      cut.entry.execution.application.retired := congrArg Prod.snd controls.symm
  let cp := cut.witness.checkpoint.transfer saved
    (congrArg CommitAttemptId.generation cut.sameAttempt).symm
    (congrArg CommitAttemptId.phase cut.sameAttempt).symm
  have aligned : cp.ArchivedRecall := by
    intro owner survives
    change cut.witness.checkpoint.source.history owner = _
    rw [saved, retired]
    rw [saved] at survives
    exact cut.witness.aligned owner survives
  have exclusion := phaseExclusionRecord_history runtime leaks plan inputs horizon scheduler raw
  have stored := phaseStoredCheckpoint_history runtime leaks plan inputs horizon scheduler raw
  have bindingRecord := phaseBindingRecord_history runtime leaks plan inputs horizon scheduler raw
  have remembered := phaseHistoryCheckpoint_history runtime leaks plan inputs horizon scheduler raw
  have archives := PhaseRuntimeState.archivesBefore_history runtime leaks plan inputs horizon
    scheduler raw
  obtain ⟨_draw, native⟩ := phaseNativeInvariant_history runtime leaks plan inputs horizon
    scheduler raw
  obtain ⟨remaining, installed⟩ := List.head?_eq_some_iff.mp cut.installed
  obtain ⟨selected, selectedEq, Ξ, Q, name, fresh, guard, earlier, later, size, split,
      reconstruct⟩ := cp.fixed_binding_prefix cut.block cut.suffix cut.reconstruct
    exclusion.frontier cut.phase remaining installed (by
      have size := cut.size
      have interval := (cut.phase.mem_events event).mp cut.inside
      omega)
    event cut.inside cut.request.2.2.1 who cut.payload cut.binding
  let next := SourceProgram.commit name who fresh guard (later.prepend cut.suffix)
  let prefixEmbedding := cast (congrArg (fun program => OutputEmbedding
    (inputLayout setup.context) (outputLayout setup.program) program) reconstruct.symm) cp.embedding
  let chosen : Fin (eventCount (earlier.prepend next)) :=
    ⟨selected.val, by
      have counts := congrArg eventCount reconstruct
      have bounded := selected.isLt
      dsimp only [next] at *
      omega⟩
  have chosenVal : chosen.val = selected.val := rfl
  have chosenEvent : prefixEmbedding.event chosen = event := by
    have same := OutputEmbedding.event_cast setup.program reconstruct.symm cp.embedding selected
      chosen chosenVal.symm
    exact same.symm.trans selectedEq
  have acting := cut.request.2.2.2.1
  have plain : ¬ ((serviceGraph setup mode).outputLayout event).IsPublication := by
    rw [cut.binding]
    exact id
  have available := commitPrefix_owned_fields_of_ready setup mode earlier next prefixEmbedding
    control.execution.application.current.native.config who chosen (chosenVal.trans size.symm)
      (chosenEvent.symm ▸ cut.request.2.2.1) (chosenEvent.symm ▸ acting)
      (chosenEvent.symm ▸ plain)
  have positioned := exclusion.frontier.positioned
  rw [installed] at positioned
  have savedPrefix : control.execution.application.entry.native.config.cut.IsPrefix
      control.execution.application.attempt.phase := by
    simpa only [PhaseRuntimeState.attempt, installed, List.head?_cons, Option.map_some,
      Option.getD_some] using positioned.1
  have survives : who ∉ control.execution.application.entry.excluded := by
    intro member
    exact cut.request.2.2.2.2
      ((phaseFailureCoverage_history runtime leaks plan inputs horizon scheduler raw).inherited
        member)
  have owned := cp.filled_prefix_archived_history_of_ready aligned archives fresh guard
    (later.prepend cut.suffix) earlier reconstruct survives selected size.symm
      (selectedEq.symm ▸ cut.request.2.2.1) (selectedEq.symm ▸ acting) bindingRecord.active
        native.active.reachable remembered savedPrefix
  have agreement : cut.cursor.refs.Agrees cut.cursor.source.state
      control.execution.application.current.native.config.store := by
    rw [cut.refs, cut.source]
    intro name cell member
    exact (cp.refs.get member).get?_preserved _ _ stored _ (cp.agrees member)
  have coordinate : event.val = instructionCount setup.program -
      instructionCount (earlier.prepend next) + earlier.length := by
    have offset := cp.saved_position
    rw [cp.remaining, SourceProgram.ProtocolState.remaining_entry] at offset
    have rank := cp.compiled.rankEq selected
    rw [selectedEq] at rank
    rw [reconstruct]
    omega
  have embeddingEq :
      cast (congrArg (OutputEmbedding (inputLayout setup.context) (outputLayout setup.program))
        ((congrArg (fun block => block.prepend cut.suffix) split).symm.trans
          (earlier.prepend_append (.commit name who fresh guard later) cut.suffix)))
          cut.cursor.embedding = prefixEmbedding := by
    rw [cut.embedding]
    simp only [cast_cast]
    rfl
  have decoded := filled_prefix_rank_readback setup.program cut.block earlier
    (.commit name who fresh guard later) split cut.suffix cut.cursor.refs cut.cursor.embedding
      cut.cursor.lift cut.cursor.origin cut.cursor.views
      control.execution.application.current.native.config.store cut.key.2.1 cut.cursor.source
      who event cut.current.point agreement cut.lockedStore cut.filled_rank
  dsimp only at decoded
  rw [embeddingEq, cut.source] at decoded
  have read := decoded chosen (chosenVal.trans size.symm) chosenEvent coordinate available
  change (fillCommitPrefix setup.program earlier next prefixEmbedding
    control.execution.application.current.native.config.store cut.witness.checkpoint.source).history
      who = _ at owned
  change decodeEventView? setup.program
    (ContextRefs.initial setup.context (outputLayout setup.program))
    (outputEmbedding setup.program).ref who event
    ((toEventGraph setup.program).playerStore who
      control.execution.application.current.native.config.store)
    ((fillCommitPrefix setup.program earlier next prefixEmbedding
      control.execution.application.current.native.config.store
      cut.witness.checkpoint.source).history who) = _ at read
  rw [owned] at read
  rw [phaseSurvivingSourceView?_observed_of_history setup mode runtime leaks plan inputs horizon
    scheduler raw who event]
  exact read

/-- The original supported source prefix retains the actual saved source
controls and the complete chronological address suffix. This applies to the
supplied interior cut rather than an independently chosen replay. -/
theorem source_control_word
    (cut : PhaseProposalCanonicalBindingCut setup mode runtime leaks bounds plan values
      horizon scheduler control nativeTrace who event) :
    cut.current.saved = cut.witness.checkpoint.residual.lift
        (SourceProgram.ProtocolState.entry cut.witness.checkpoint.residual.tail
          cut.witness.checkpoint.source) ∧
      cut.current.entryExcluded = cut.entry.execution.application.entry.excluded ∧
      cut.current.excluded = cut.entry.execution.application.entry.excluded ∧
      cut.current.generation = cut.entry.execution.application.generation ∧
      setup.recoveryAddressWord (setup.proposalRecoveryEraseTrace cut.trace) =
        setup.recoveryAddressWord cut.witness.checkpoint.trace ++
          (List.range (event.val - cut.phase.low)).map (fun index =>
            (some (cut.entry.execution.application.attempt.phase + index + 1),
              cut.entry.execution.application.entry.excluded,
              cut.entry.execution.application.generation,
              cut.entry.execution.application.attempt.phase)) ∧
      setup.proposalRecoveryArchive who (setup.proposalRecoveryModel.infoOf who cut.trace) =
        PhaseProposal.sourceArchive cut.entry.execution.network.inputs := by
  let cp := cut.witness.checkpoint
  let firstPoint := cp.residual.lift
    (SourceProgram.ProtocolState.entry cp.residual.tail cp.source)
  let first := CommitRecoveryState.atPoint firstPoint
    cut.entry.execution.application.entry.excluded cut.entry.execution.application.generation
  have sourceStart : (⟨some cut.cursor.current,
        setup.proposalRecoveryEraseTrace cut.cursor.trace⟩ : setup.commitRecoveryProtocol.History) =
      ⟨some first, cp.trace⟩ := by
    have same := congrArg (fun history : setup.proposalRecoveryProtocol.History =>
      (⟨history.state, setup.proposalRecoveryEraseTrace history.trace⟩ :
        setup.commitRecoveryProtocol.History)) cut.cursorHistory
    simpa only [setup.proposalRecoveryEraseTrace_lift] using same
  have firstEq : cut.cursor.current = first :=
    Option.some.inj (congrArg (fun history : setup.commitRecoveryProtocol.History => history.state)
      sourceStart)
  have firstPointEq : cut.cursor.current.point = firstPoint :=
    congrArg CommitRecoveryState.point firstEq
  have firstClock := congrArg (fun history : setup.commitRecoveryProtocol.History =>
    history.trace.length) sourceStart
  simp only [setup.proposalRecoveryEraseTrace_length] at firstClock
  have path := (setup.proposalRecoveryEraseTrace_prefix cut.past).reachesWithin
  change setup.commitRecoveryProtocol.ReachesWithin _
    ⟨some cut.cursor.current, setup.proposalRecoveryEraseTrace cut.cursor.trace⟩
    ⟨some cut.current, setup.proposalRecoveryEraseTrace cut.trace⟩ at path
  rw [sourceStart] at path
  have kept := path.tracePrefix
  have interval := (cut.phase.mem_events event).mp cut.inside
  have beforeEnd : event.val - cut.phase.low < cut.block.length := by
    have size := cut.size
    omega
  have positive : 0 < cut.block.length := by omega
  have committing : SourceProgram.ProtocolState.atCommit setup.program firstPoint = true := by
    have commit := cut.cursor.savedCommit positive
    rw [firstEq] at commit
    exact commit
  have window : cut.block.length + SourceProgram.ProtocolState.commitEnd setup.program firstPoint ≤
      SourceProgram.ProtocolState.remaining setup.program firstPoint := by
    rw [← firstPointEq, cut.cursor.point, cut.cursor.origin.commitEnd_lift,
      cut.cursor.origin.remaining_lift]
    exact cut.block.length_le_commit_window cut.suffix cut.cursor.source
  have inside : (setup.proposalRecoveryEraseTrace cut.trace).length +
      SourceProgram.ProtocolState.commitEnd setup.program firstPoint <
        cp.trace.length + SourceProgram.ProtocolState.remaining setup.program firstPoint := by
    have clock := cut.clock
    rw [setup.proposalRecoveryEraseTrace_length]
    omega
  obtain ⟨_finished, last, _lastTrace, _attempt, completed, _point, _agrees, lastExcluded,
      _rank⟩ := cut.final_view_rank
  have endpoint : cut.completed.state = some last :=
    congrArg (fun history : setup.proposalRecoveryProtocol.History => history.state) completed
  have upper := setup.commitRecovery_public_excluded_of_reaches
    (setup.proposalRecoveryEraseTrace_prefix cut.future).reachesWithin
  change cut.current.excluded ⊆ (setup.commitRecoveryPublic cut.completed.state).1 at upper
  rw [endpoint] at upper
  change cut.current.excluded ⊆ last.excluded at upper
  have lower := setup.commitRecovery_public_excluded_of_reaches
    (setup.proposalRecoveryEraseTrace_prefix cut.past).reachesWithin
  change cut.cursor.current.excluded ⊆ cut.current.excluded at lower
  have excluded : cut.current.excluded = cut.entry.execution.application.entry.excluded := by
    have same : cut.current.excluded = cut.cursor.current.excluded :=
      Finset.Subset.antisymm (fun owner member => lastExcluded ▸ upper member) lower
    exact same.trans (cut.cursor.excluded.trans cut.entryExcluded.symm)
  have surviving : who ∉ cut.entry.execution.application.entry.excluded := fun member =>
    cut.survives (excluded.symm ▸ member)
  obtain ⟨current, _replay, currentEq, saved, entryExcluded, generation, _rest⟩ :=
    setup.commitRecovery_noMiss_prefix_information who firstPoint
      cut.entry.execution.application.entry.excluded cut.entry.execution.application.generation
      cp.trace committing (setup.proposalRecoveryEraseTrace cut.trace) kept inside
        (show who ∉ (setup.commitRecoveryPublic (some cut.current)).1 from cut.survives)
  have sameCurrent : current = cut.current := (Option.some.inj currentEq).symm
  subst current
  have addresses := source_binding_prefix_addresses setup who firstPoint
    cut.entry.execution.application.entry.excluded cut.entry.execution.application.generation
      cp.trace committing surviving (setup.proposalRecoveryEraseTrace cut.trace) kept inside
        excluded
  have position := cp.saved_position
  have clock : (setup.proposalRecoveryEraseTrace cut.trace).length - cp.trace.length =
      event.val - cut.phase.low := by
    have count := cut.clock
    rw [setup.proposalRecoveryEraseTrace_length]
    omega
  rw [clock, position] at addresses
  have sourceArchive := setup.proposalRecoveryArchive_eq_of_commit_window who cut.cursor.current
    cut.cursor.trace (by simpa only [firstEq, first, CommitRecoveryState.atPoint] using committing)
    cut.trace cut.past (by
      rw [firstPointEq]
      rw [setup.proposalRecoveryEraseTrace_length] at inside
      omega)
  rw [cut.cursor.proposals who (by rw [firstEq]; exact surviving)] at sourceArchive
  exact ⟨saved, entryExcluded, excluded, generation, addresses, sourceArchive⟩

/-- Full source controls, numeric public recall and proposal archive are read
from the actual native callback. Physical in-phase failures do not enter the
saved source exclusion set or its preceding public chronology. -/
theorem native_readback
    (cut : PhaseProposalCanonicalBindingCut setup mode runtime leaks bounds plan values
      horizon scheduler control nativeTrace who event) :
    setup.commitRecoveryPublic (some cut.current) =
        (control.execution.application.entry.excluded,
          control.execution.application.generation, control.execution.application.attempt.phase) ∧
      (setup.attemptPublicRecall who (setup.proposalRecoveryEraseTrace cut.trace)).map
          (setup.commitRecoveryPublicAddress who) =
        (control.execution.application.sourcePublicAddressWord plan event.val).reverse ++
          [(none, (∅, 0, 0))] ∧
      setup.proposalRecoveryArchive who (setup.proposalRecoveryModel.infoOf who cut.trace) =
        PhaseProposal.sourceArchive control.execution.network.inputs := by
  let inputs := setup.initialLaw.map encodeInputs
  let initial := inputs.map (PhaseRuntimeState.initial plan)
  let menu := PhaseCount.onePacketMenu runtime leaks bounds
  let raw := menu.toRawTrace initial horizon scheduler nativeTrace
  have initialized : ∀ state ∈ initial.support, state.Ordered := by
    intro state supported
    obtain ⟨draw, _supported, rfl⟩ := PMF.support_map .. ▸ supported
    exact PhaseRuntimeState.initial_ordered plan draw
  have ordered := (phaseApplication_seedOrder runtime leaks).history initial horizon scheduler
    initialized (menu.toRawTrace initial horizon scheduler cut.entryTrace)
  have saved := ((phase_attempt_progress_of_prefix runtime leaks menu initial initialized
    horizon scheduler cut.entry control cut.entryTrace nativeTrace cut.nativeRetained
      ordered).2.2 cut.sameAttempt).symm
  have metadata := phase_attempt_metadata_of_prefix runtime leaks menu initial initialized horizon
    scheduler cut.entry control cut.entryTrace nativeTrace cut.nativeRetained ordered
      cut.sameAttempt
  obtain ⟨sourceSaved, _sourceEntry, sourceExcluded, sourceGeneration, numeric, archive⟩ :=
    cut.source_control_word
  have sameGeneration : cut.entry.execution.application.generation =
      control.execution.application.generation :=
    congrArg CommitAttemptId.generation cut.sameAttempt
  have sourceControl : setup.commitRecoveryPublic (some cut.current) =
      (control.execution.application.entry.excluded, control.execution.application.generation,
        control.execution.application.attempt.phase) := by
    change (cut.current.excluded, cut.current.generation, instructionCount setup.program -
      SourceProgram.ProtocolState.remaining setup.program cut.current.saved) = _
    rw [sourceSaved, sourceExcluded, sourceGeneration, cut.witness.checkpoint.saved_position,
      saved, sameGeneration,
      ← congrArg CommitAttemptId.phase cut.sameAttempt]
  obtain ⟨entryRest, entryInstalled⟩ := List.head?_eq_some_iff.mp cut.entryInstalled
  have entryLow : cut.entry.execution.application.attempt.phase = cut.phase.low := by
    simp only [PhaseRuntimeState.attempt, entryInstalled, List.head?_cons, Option.map_some,
      Option.getD_some]
  have savedE := PhaseRuntimeState.saved_excluded_eq_public_failures cut.witness.exclusions
    cut.witness.failures cut.witness.receipts.exclusion.frontier cut.phase entryRest entryInstalled
  have records := PhaseRuntimeState.sourceRecordFailures_sourceControlRecords
    cut.entry.execution.application.retired
  unfold RuntimePhasePlan.sourceRecordFailures at records
  have nativeNumeric : setup.recoveryAddressWord (setup.proposalRecoveryEraseTrace cut.trace) =
      cut.entry.execution.application.sourcePublicAddressWord plan event.val := by
    rw [numeric, cut.witness.chronology.addresses,
      PhaseRuntimeState.sourcePublicAddressWord_saved]
    dsimp only [PhaseRuntimeState.sourcePublicAddressWord, State.sourceFailureFootprint]
    rw [records, ← savedE, entryLow]
    rfl
  have positioned := cut.witness.receipts.exclusion.frontier.positioned
  rw [entryInstalled] at positioned
  have completed : ∀ prior : (serviceGraph setup mode).EventId,
      prior.val < cut.entry.execution.application.attempt.phase →
        prior ∈ cut.entry.execution.application.entry.native.config.cut.completed := by
    intro prior earlier
    exact (positioned.1.2 prior).mpr (entryLow ▸ earlier)
  have currentFrame := phasePublicFailureCheckpoint_history runtime leaks plan inputs horizon
    scheduler raw
  change control.execution.application.entry.native.PublicFailureExtension
    control.execution.application.current.native at currentFrame
  rw [saved] at currentFrame
  have sameFailures : ∀ rank ≤ cut.entry.execution.application.attempt.phase,
      cut.entry.execution.application.current.native.failureOwnersBefore rank =
        control.execution.application.current.native.failureOwnersBefore rank := by
    intro rank bounded
    exact (cut.witness.failures.failureOwnersBefore_eq_below _ completed rank bounded).symm.trans
      (currentFrame.failureOwnersBefore_eq_below _ completed rank bounded)
  have publicNumeric := PhaseRuntimeState.sourcePublicAddressWord_eq_of_prefix plan
    cut.sameAttempt (congrArg Prod.snd metadata) sameFailures event.val
  have recalled := setup.commitRecovery_publicRecall_addresses who
    (setup.proposalRecoveryEraseTrace cut.trace)
  rw [nativeNumeric, publicNumeric] at recalled
  have scope : ∀ (middle : (phaseApplication runtime leaks).Control)
      (prior : (menu.protocol initial horizon scheduler).Trace (some middle)),
      TracePrefix cut.entryTrace prior → TracePrefix prior nativeTrace →
      prior.length < nativeTrace.length →
        middle.execution.application.attempt = cut.entry.execution.application.attempt := by
    intro middle prior afterEntry beforeCurrent _shorter
    have middleOrdered := (phaseApplication_seedOrder runtime leaks).history initial horizon
      scheduler initialized (menu.toRawTrace initial horizon scheduler prior)
    obtain ⟨lowerGen, lowerPhase, _⟩ := phase_attempt_progress_of_prefix runtime leaks menu initial
      initialized horizon scheduler cut.entry middle cut.entryTrace prior afterEntry ordered
    obtain ⟨upperGen, upperPhase, _⟩ := phase_attempt_progress_of_prefix runtime leaks menu initial
      initialized horizon scheduler middle control prior nativeTrace beforeCurrent middleOrdered
    have generation := congrArg CommitAttemptId.generation cut.sameAttempt
    have phase := congrArg CommitAttemptId.phase cut.sameAttempt
    cases first : cut.entry.execution.application.attempt with
    | mk firstPhase firstGeneration =>
      cases second : middle.execution.application.attempt with
      | mk secondPhase secondGeneration =>
        cases third : control.execution.application.attempt with
        | mk thirdPhase thirdGeneration =>
          simp only [first, second, third] at lowerGen lowerPhase upperGen upperPhase
          simp only [first, third] at generation phase ⊢
          congr 1 <;> omega
  obtain ⟨ending, endpoint, archiveEq⟩ := PhaseProposal.phase_commitment_prefix_sourceArchive
    runtime leaks bounds plan (serviceGraph_revealRelaxedOrdered setup mode) inputs horizon
      scheduler cut.entry cut.entryTrace cut.phase (Option.mem_def.mpr cut.entryInstalled)
        cut.commitment nativeTrace cut.nativeRetained scope
  cases Option.some.inj endpoint
  exact ⟨sourceControl, recalled, archive.trans archiveEq.symm⟩

/-- The supplied initializer is the original single setup draw, with its
literal trace length. This identifies that witness without choosing another
initial source history from the same typed endpoint. -/
theorem initializer_facts
    (cut : PhaseProposalCanonicalBindingCut setup mode runtime leaks bounds plan values
      horizon scheduler control nativeTrace who event) :
    cut.initializer = CommitRecoveryState.atPoint
        (SourceProgram.ProtocolState.entry setup.program (setup.initialConfig cut.theta)) ∅ 0 ∧
      cut.initializerTrace.length = 1 := by
  have raw := congrArg (fun history : setup.commitRecoveryProtocol.History =>
    (⟨history.state, setup.proposalRecoveryLiftTrace
      (nativeArchiveLabels setup (PhaseProposal.sourceArchive cut.entry.execution.network.inputs))
      history.trace⟩ : setup.proposalRecoveryProtocol.History))
        (initialized_checkpoint_history setup mode plan cut.theta cut.thetaSupported)
  have initial := cut.initialized.trans raw
  have state := congrArg (fun history : setup.proposalRecoveryProtocol.History => history.state)
    initial
  have length := congrArg (fun history : setup.proposalRecoveryProtocol.History =>
    history.trace.length) initial
  exact ⟨Option.some.inj state, length⟩

/-- All original input cells of the arbitrary supplied source prefix come
from its literal supported setup draw, even after previous canceled attempts. -/
theorem base_eq_theta
    (cut : PhaseProposalCanonicalBindingCut setup mode runtime leaks bounds plan values
      horizon scheduler control nativeTrace who event) :
    SourceProgram.ProtocolState.base setup.program cut.current.point = cut.theta := by
  have initial := cut.initializer_facts.1
  obtain ⟨current, endpoint, cells, _saved⟩ := setup.commitRecovery_base_of_prefix cut.initializer
    (setup.proposalRecoveryEraseTrace cut.initializerTrace) (by rw [initial]; rfl)
    (setup.proposalRecoveryEraseTrace cut.trace)
    (setup.proposalRecoveryEraseTrace_prefix (cut.sourceRetained.trans cut.past))
  have same : current = cut.current := (Option.some.inj endpoint).symm
  subst current
  rw [initial, CommitRecoveryState.atPoint, SourceProgram.ProtocolState.base_entry] at cells
  exact cells

end PhaseProposalCanonicalBindingCut

/-- Equal complete native information identifies the actual static binding
coordinate. The two requests are quantified separately and compared through
their genuine public request projections and owning-event uniqueness. -/
theorem PhaseProposalCanonicalBindingCut.event_eq_of_information
    {setup : Setup (Player := Player) (L := L)} {mode : ExecutionMode}
    {runtime : EventGraphRuntime (serviceGraph setup mode)}
    {leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode))}
    {bounds : MessageBounds (serviceGraph setup mode)}
    {plan : RuntimePhasePlan (serviceGraph setup mode)}
    {values : ∀ owner (key : setup.ProposalRecoveryComponent owner),
      PMF (setup.CommitRecoveryValueChoice owner key.1)}
    {horizon : Nat} {scheduler : (phaseApplication runtime leaks).Scheduler}
    {leftControl rightControl : (phaseApplication runtime leaks).Control}
    {leftTrace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      ((setup.initialLaw.map encodeInputs).map (PhaseRuntimeState.initial plan))
      horizon scheduler).Trace (some leftControl)}
    {rightTrace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      ((setup.initialLaw.map encodeInputs).map (PhaseRuntimeState.initial plan))
      horizon scheduler).Trace (some rightControl)}
    {who : Player} {leftEvent rightEvent : (serviceGraph setup mode).EventId}
    (left : PhaseProposalCanonicalBindingCut setup mode runtime leaks bounds plan values
      horizon scheduler leftControl leftTrace who leftEvent)
    (right : PhaseProposalCanonicalBindingCut setup mode runtime leaks bounds plan values
      horizon scheduler rightControl rightTrace who rightEvent)
    (same : ((PhaseCount.onePacketMenu runtime leaks bounds).information
        ((setup.initialLaw.map encodeInputs).map (PhaseRuntimeState.initial plan))
        horizon scheduler).infoOf who leftTrace =
      ((PhaseCount.onePacketMenu runtime leaks bounds).information
        ((setup.initialLaw.map encodeInputs).map (PhaseRuntimeState.initial plan))
        horizon scheduler).infoOf who rightTrace) : leftEvent = rightEvent := by
  let initial := (setup.initialLaw.map encodeInputs).map (PhaseRuntimeState.initial plan)
  let menu := PhaseCount.onePacketMenu runtime leaks bounds
  change (menu.signals initial horizon scheduler).infoOf who leftTrace =
    (menu.signals initial horizon scheduler).infoOf who rightTrace at same
  rw [menu.info initial horizon scheduler who leftTrace,
    menu.info initial horizon scheduler who rightTrace] at same
  simp only [ReactiveApplication.observe, left.active, right.active, ↓reduceIte] at same
  have observed := congrArg Prod.snd (Option.some.inj same)
  have publicViewEq : leftControl.execution.application.publicView =
      rightControl.execution.application.publicView :=
    congrArg (fun view => view.application.2) observed
  obtain ⟨_leftInputs, leftValid⟩ := phaseNativeInvariant_history runtime leaks plan
    (setup.initialLaw.map encodeInputs) horizon scheduler
    (menu.toRawTrace initial horizon scheduler leftTrace)
  obtain ⟨_rightInputs, rightValid⟩ := phaseNativeInvariant_history runtime leaks plan
    (setup.initialLaw.map encodeInputs) horizon scheduler
    (menu.toRawTrace initial horizon scheduler rightTrace)
  have publicRequest := (PhaseRuntimeState.requests_publicView _ leftValid who _).mpr left.request
  rw [publicViewEq] at publicRequest
  have transported := (PhaseRuntimeState.requests_publicView _ rightValid who _).mp publicRequest
  exact ((serviceGraph_revealRelaxedOrdered setup mode).ready_actor_unique
    rightControl.execution.application.current.native.config.cut transported.2.2.1
    right.request.2.2.1 transported.2.2.2.1 right.request.2.2.2.1).symm

/- Complete native information determines the entire canonical source information. -/
theorem PhaseProposalCanonicalBindingCut.info_eq_of_information
    {setup : Setup (Player := Player) (L := L)} {mode : ExecutionMode}
    {runtime : EventGraphRuntime (serviceGraph setup mode)}
    {leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode))}
    {bounds : MessageBounds (serviceGraph setup mode)}
    {plan : RuntimePhasePlan (serviceGraph setup mode)}
    {values : ∀ owner (key : setup.ProposalRecoveryComponent owner),
      PMF (setup.CommitRecoveryValueChoice owner key.1)}
    {horizon : Nat} {scheduler : (phaseApplication runtime leaks).Scheduler}
    {leftControl rightControl : (phaseApplication runtime leaks).Control}
    {leftTrace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      ((setup.initialLaw.map encodeInputs).map (PhaseRuntimeState.initial plan))
      horizon scheduler).Trace (some leftControl)}
    {rightTrace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      ((setup.initialLaw.map encodeInputs).map (PhaseRuntimeState.initial plan))
      horizon scheduler).Trace (some rightControl)}
    {who : Player} {leftEvent rightEvent : (serviceGraph setup mode).EventId}
    (left : PhaseProposalCanonicalBindingCut setup mode runtime leaks bounds plan values
      horizon scheduler leftControl leftTrace who leftEvent)
    (right : PhaseProposalCanonicalBindingCut setup mode runtime leaks bounds plan values
      horizon scheduler rightControl rightTrace who rightEvent)
    (complete : leaks = MessageNetwork.completePendingObservation)
    (same : ((PhaseCount.onePacketMenu runtime leaks bounds).information
        ((setup.initialLaw.map encodeInputs).map (PhaseRuntimeState.initial plan))
        horizon scheduler).infoOf who leftTrace =
      ((PhaseCount.onePacketMenu runtime leaks bounds).information
        ((setup.initialLaw.map encodeInputs).map (PhaseRuntimeState.initial plan))
        horizon scheduler).infoOf who rightTrace) :
    setup.proposalRecoveryModel.infoOf who left.trace =
      setup.proposalRecoveryModel.infoOf who right.trace := by
  have events := left.event_eq_of_information right same
  cases events
  let inputs := setup.initialLaw.map encodeInputs
  let initial := inputs.map (PhaseRuntimeState.initial plan)
  let menu := PhaseCount.onePacketMenu runtime leaks bounds
  let leftRaw := menu.toRawTrace initial horizon scheduler leftTrace
  let rightRaw := menu.toRawTrace initial horizon scheduler rightTrace
  have nativeInfo := same
  change (menu.signals initial horizon scheduler).infoOf who leftTrace =
    (menu.signals initial horizon scheduler).infoOf who rightTrace at nativeInfo
  rw [menu.info initial horizon scheduler who leftTrace,
    menu.info initial horizon scheduler who rightTrace] at nativeInfo
  simp only [ReactiveApplication.observe, left.active, right.active, ↓reduceIte] at nativeInfo
  have native := Option.some.inj nativeInfo
  have observed := congrArg Prod.snd native
  have publicViewEq : leftControl.execution.application.publicView =
      rightControl.execution.application.publicView :=
    congrArg (fun view => view.application.2) observed
  have views : SourceProgram.ProtocolState.observe who setup.program left.current.point =
      SourceProgram.ProtocolState.observe who setup.program right.current.point := by
    have decoded := congrArg (phaseSurvivingSourceView? setup mode runtime leaks who leftEvent)
      observed
    rw [left.source_view, right.source_view] at decoded
    exact Option.some.inj decoded
  have savedExclusions := phase_saved_excluded_eq_of_publicView_eq runtime leaks plan inputs
    horizon scheduler leftRaw rightRaw (by
      intro empty
      have installed := left.installed
      rw [empty] at installed
      cases installed) (by
      intro empty
      have installed := right.installed
      rw [empty] at installed
      cases installed) publicViewEq
  have sameGeneration : leftControl.execution.application.generation =
      rightControl.execution.application.generation :=
    congrArg (fun view => view.attempt.generation) publicViewEq
  have samePhase : leftControl.execution.application.attempt.phase =
      rightControl.execution.application.attempt.phase :=
    congrArg (fun view => view.attempt.phase) publicViewEq
  have leftRead := left.native_readback
  have rightRead := right.native_readback
  have controls : setup.commitRecoveryPublic (some left.current) =
      setup.commitRecoveryPublic (some right.current) := by
    rw [leftRead.1, rightRead.1, savedExclusions, sameGeneration, samePhase]
  have numbers : (setup.attemptPublicRecall who
        (setup.proposalRecoveryEraseTrace left.trace)).map
        (setup.commitRecoveryPublicAddress who) =
      (setup.attemptPublicRecall who (setup.proposalRecoveryEraseTrace right.trace)).map
        (setup.commitRecoveryPublicAddress who) := by
    rw [leftRead.2.1, rightRead.2.1,
      PhaseRuntimeState.sourcePublicAddressWord_congr plan publicViewEq]
  have erased : setup.commitRecoveryErasedInformation who
        (setup.commitRecoveryModel.infoOf who (setup.proposalRecoveryEraseTrace left.trace)) =
      setup.commitRecoveryErasedInformation who
        (setup.commitRecoveryModel.infoOf who (setup.proposalRecoveryEraseTrace right.trace)) := by
    rw [setup.commitRecovery_erasedInformation_read who left.current
        (setup.proposalRecoveryEraseTrace left.trace) left.survives,
      setup.commitRecovery_erasedInformation_read who right.current
        (setup.proposalRecoveryEraseTrace right.trace) right.survives,
      views, controls, numbers]
  have proposals : setup.proposalRecoveryArchive who
        (setup.proposalRecoveryModel.infoOf who left.trace) =
      setup.proposalRecoveryArchive who (setup.proposalRecoveryModel.infoOf who right.trace) := by
    rw [leftRead.2.2, rightRead.2.2]
    exact PhaseProposal.sourceArchive_eq_of_completeInput runtime leaks complete initial horizon
      scheduler scheduler leftControl rightControl leftRaw rightRaw who left.active right.active
        (congrArg Prod.fst native) observed
  have original := SourceProgram.ProtocolState.sourceObserve_base_eq_of_observe_eq who
    setup.program left.current.point right.current.point views
  rw [left.base_eq_theta, right.base_eq_theta] at original
  have initialViews := SourceProgram.ProtocolState.observe_entry_congr who setup.program
    (setup.initialConfig left.theta) (setup.initialConfig right.theta) (Prod.ext original rfl)
  have initialObserved :
      (SourceProgram.ProtocolState.observe who setup.program left.initializer.point,
        SourceProgram.ProtocolState.observe who setup.program left.initializer.saved,
        left.initializer.excluded, left.initializer.entryExcluded, left.initializer.generation) =
      (SourceProgram.ProtocolState.observe who setup.program right.initializer.point,
        SourceProgram.ProtocolState.observe who setup.program right.initializer.saved,
        right.initializer.excluded, right.initializer.entryExcluded,
          right.initializer.generation) := by
    rw [left.initializer_facts.1, right.initializer_facts.1]
    dsimp only [CommitRecoveryState.atPoint]
    rw [initialViews]
  have initialInformation : setup.proposalRecoveryModel.infoOf who left.initializerTrace =
      setup.proposalRecoveryModel.infoOf who right.initializerTrace := by
    have leftInitial := congrArg (fun history : setup.proposalRecoveryProtocol.History =>
      setup.proposalRecoveryModel.infoOf who history.trace) left.initialized
    have rightInitial := congrArg (fun history : setup.proposalRecoveryProtocol.History =>
      setup.proposalRecoveryModel.infoOf who history.trace) right.initialized
    exact leftInitial.trans ((initialized_lift_info_eq setup mode plan who left.theta right.theta
      left.thetaSupported right.thetaSupported _ _ original).trans rightInitial.symm)
  have owned := SourceProgram.ProtocolState.history_eq_of_observe who setup.program
    left.current.point right.current.point views
  exact setup.proposalRecovery_info_eq_of_erased_archive_and_own_history who left.initializer
    right.initializer left.initializerTrace right.initializerTrace
    (by rw [left.initializer_facts.2, right.initializer_facts.2]) initialObserved initialInformation
    left.trace right.trace (left.sourceRetained.trans left.past)
    (right.sourceRetained.trans right.past) left.survives right.survives erased proposals
    (congrArg some owned)

/-- Every allowed latent source preimage retains a canonical current-block
support witness and its genuine foreign-cause refinement. This relation does
not assume full information equality, source reach proportionality or
two-sided coverage of source fibers. -/
structure PhaseProposalNativeSourceMatch
    (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
    (runtime : EventGraphRuntime (serviceGraph setup mode))
    (leaks : MessageNetwork.ObservationRule Player
      (CommitAttemptPacket (serviceGraph setup mode)))
    (bounds : MessageBounds (serviceGraph setup mode))
    (plan : RuntimePhasePlan (serviceGraph setup mode))
    (values : ∀ owner (key : setup.ProposalRecoveryComponent owner),
      PMF (setup.CommitRecoveryValueChoice owner key.1))
    (horizon : Nat) (scheduler : (phaseApplication runtime leaks).Scheduler)
    (control : (phaseApplication runtime leaks).Control)
    (nativeTrace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      ((setup.initialLaw.map encodeInputs).map (PhaseRuntimeState.initial plan))
      horizon scheduler).Trace (some control))
    (who : Player) (event : (serviceGraph setup mode).EventId)
    (history : setup.proposalRecoveryProtocol.History) where
  canonical : PhaseProposalCanonicalBindingCut setup mode runtime leaks bounds plan values
    horizon scheduler control nativeTrace who event
  refined : setup.ProposalRecoveryForeignRefinement who canonical.initializer
    canonical.initializerTrace ⟨some canonical.current, canonical.trace⟩ history

namespace PhaseProposalNativeSourceMatch

variable {setup : Setup (Player := Player) (L := L)} {mode : ExecutionMode}
  {runtime : EventGraphRuntime (serviceGraph setup mode)}
  {leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode))}
  {bounds : MessageBounds (serviceGraph setup mode)}
  {plan : RuntimePhasePlan (serviceGraph setup mode)}
  {values : ∀ owner (key : setup.ProposalRecoveryComponent owner),
    PMF (setup.CommitRecoveryValueChoice owner key.1)}
  {horizon : Nat} {scheduler : (phaseApplication runtime leaks).Scheduler}
  {control : (phaseApplication runtime leaks).Control}
  {nativeTrace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
    ((setup.initialLaw.map encodeInputs).map (PhaseRuntimeState.initial plan))
    horizon scheduler).Trace (some control)}
  {who : Player} {event : (serviceGraph setup mode).EventId}
  {history : setup.proposalRecoveryProtocol.History}

/-- Every permitted latent preimage is an actual surviving binding decision
at the same static event. Foreign publication refinements retain this fact
through the full observer comparison; no canonical Boolean identity is used. -/
theorem decision
    (matched : PhaseProposalNativeSourceMatch setup mode runtime leaks bounds plan values
      horizon scheduler control nativeTrace who event history) :
    ∃ current : CommitRecoveryState setup.program,
      history.state = some current ∧
      SourceProgram.ProtocolState.actor setup.program current.point = some who ∧
      who ∉ current.excluded ∧
      SourceProgram.ProtocolState.atCommit setup.program current.point = true ∧
      instructionCount setup.program -
          SourceProgram.ProtocolState.remaining setup.program current.point =
        event.val ∧
      setup.proposalRecoveryModel.IsDecisionInfo who
        (setup.proposalRecoveryModel.infoOf who history.trace) := by
  let cut := matched.canonical
  obtain ⟨current, endpoint⟩ := setup.state_some_of_prefix cut.initializer
    (setup.proposalRecoveryEraseTrace cut.initializerTrace)
    (setup.proposalRecoveryEraseTrace history.trace)
    (setup.proposalRecoveryEraseTrace_prefix matched.refined.retained.2)
  have same := matched.refined.info_eq
  have privateRead := congrArg (fun information => information.1.1.1) same
  have semantic := congrArg (setup.proposalRecoveryEraseInfo who) same
  rw [setup.proposalRecoveryEraseInfo_observed, setup.proposalRecoveryEraseInfo_observed]
    at semantic
  have controls := congrArg (fun information => information.1.1.2) semantic
  have currentPrivate : (setup.proposalRecoveryModel.infoOf who history.trace).1.1.1 =
      setup.commitRecoveryPrivate who history.state := by
    change (setup.proposalRecoverySignals.withOwnPlayRecall.infoOf who history.trace).1.1.1 = _
    rw [InfoSignals.withOwnPlayRecall_infoOf]
    exact congrArg Prod.fst (setup.proposalRecoverySignals_control who history.trace)
  have cutPrivate : (setup.proposalRecoveryModel.infoOf who cut.trace).1.1.1 =
      some (SourceProgram.ProtocolState.observe who setup.program cut.current.point) := by
    change (setup.proposalRecoverySignals.withOwnPlayRecall.infoOf who cut.trace).1.1.1 = _
    rw [InfoSignals.withOwnPlayRecall_infoOf]
    exact congrArg Prod.fst (setup.proposalRecoverySignals_control who cut.trace)
  have currentPublic : (setup.commitRecoveryModel.infoOf who
      (setup.proposalRecoveryEraseTrace history.trace)).1.1.2 =
      setup.commitRecoveryPublic history.state := by
    change (setup.commitRecoverySignals.withOwnPlayRecall.infoOf who
      (setup.proposalRecoveryEraseTrace history.trace)).1.1.2 = _
    rw [InfoSignals.withOwnPlayRecall_infoOf]
    exact congrArg Prod.snd (setup.commitRecoverySignals_current who _)
  have cutPublic : (setup.commitRecoveryModel.infoOf who
      (setup.proposalRecoveryEraseTrace cut.trace)).1.1.2 =
      setup.commitRecoveryPublic (some cut.current) := by
    change (setup.commitRecoverySignals.withOwnPlayRecall.infoOf who
      (setup.proposalRecoveryEraseTrace cut.trace)).1.1.2 = _
    rw [InfoSignals.withOwnPlayRecall_infoOf]
    exact congrArg Prod.snd (setup.commitRecoverySignals_current who _)
  rw [cutPrivate, currentPrivate, endpoint] at privateRead
  have observed := Option.some.inj privateRead
  dsimp only at observed
  rw [cutPublic, currentPublic, endpoint] at controls
  have excludes : cut.current.excluded = current.excluded := congrArg Prod.fst controls
  have actor := congrArg (ProtocolView.actor who setup.program) observed
  simp only [SourceProgram.ProtocolState.actor_observe_eq] at actor
  have committing := congrArg (ProtocolView.atCommit who setup.program) observed
  simp only [SourceProgram.ProtocolState.atCommit_observe] at committing
  have positions := congrArg (ProtocolView.position who setup.program) observed
  have leftPosition := ProtocolView.position_add_remaining who setup.program cut.current.point
  have rightPosition := ProtocolView.position_add_remaining who setup.program current.point
  have currentRank : instructionCount setup.program -
      SourceProgram.ProtocolState.remaining setup.program current.point = event.val := by
    have cutRank := cut.rank
    omega
  have currentDecision := setup.proposalRecovery_isDecisionInfo_of_surviving_actor cut.current
    cut.trace who cut.survives cut.actor
  rw [same] at currentDecision
  exact ⟨current, endpoint, actor.symm.trans cut.actor,
    fun member => cut.survives (excludes.symm ▸ member),
    committing.symm.trans cut.atCommit, currentRank, currentDecision⟩

end PhaseProposalNativeSourceMatch

/-- Every permitted latent preimage of the same complete native information
has the same ENTIRE labeled source information. Original setup draws and
foreign failure-cause refinements remain literal quantified witnesses. -/
theorem PhaseProposalNativeSourceMatch.info_eq_of_information
    {setup : Setup (Player := Player) (L := L)} {mode : ExecutionMode}
    {runtime : EventGraphRuntime (serviceGraph setup mode)}
    {leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode))}
    {bounds : MessageBounds (serviceGraph setup mode)}
    {plan : RuntimePhasePlan (serviceGraph setup mode)}
    {values : ∀ owner (key : setup.ProposalRecoveryComponent owner),
      PMF (setup.CommitRecoveryValueChoice owner key.1)}
    {horizon : Nat} {scheduler : (phaseApplication runtime leaks).Scheduler}
    {leftControl rightControl : (phaseApplication runtime leaks).Control}
    {leftTrace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      ((setup.initialLaw.map encodeInputs).map (PhaseRuntimeState.initial plan))
      horizon scheduler).Trace (some leftControl)}
    {rightTrace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      ((setup.initialLaw.map encodeInputs).map (PhaseRuntimeState.initial plan))
      horizon scheduler).Trace (some rightControl)}
    {who : Player} {leftEvent rightEvent : (serviceGraph setup mode).EventId}
    {leftHistory rightHistory : setup.proposalRecoveryProtocol.History}
    (left : PhaseProposalNativeSourceMatch setup mode runtime leaks bounds plan values
      horizon scheduler leftControl leftTrace who leftEvent leftHistory)
    (right : PhaseProposalNativeSourceMatch setup mode runtime leaks bounds plan values
      horizon scheduler rightControl rightTrace who rightEvent rightHistory)
    (complete : leaks = MessageNetwork.completePendingObservation)
    (same : ((PhaseCount.onePacketMenu runtime leaks bounds).information
        ((setup.initialLaw.map encodeInputs).map (PhaseRuntimeState.initial plan))
        horizon scheduler).infoOf who leftTrace =
      ((PhaseCount.onePacketMenu runtime leaks bounds).information
        ((setup.initialLaw.map encodeInputs).map (PhaseRuntimeState.initial plan))
        horizon scheduler).infoOf who rightTrace) :
    setup.proposalRecoveryModel.infoOf who leftHistory.trace =
      setup.proposalRecoveryModel.infoOf who rightHistory.trace := by
  exact left.refined.info_eq.symm.trans
    ((left.canonical.info_eq_of_information right.canonical complete same).trans
      right.refined.info_eq)

end Vegas
