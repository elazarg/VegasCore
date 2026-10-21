/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.ProposalRecoveryPublicClassConstancy
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
import Vegas.Pending.PhaseValueSwap
import Vegas.Pending.ValueSwapPairs
import Vegas.Pending.PhaseArchiveOrder
import Vegas.Game.ConcurrentRawSequentialPreservation
import Vegas.Game.PhaseProposalHistory
import Vegas.Game.ReservedEpochBindingAliases
import Vegas.Game.PhaseBindingRecallWord
import Vegas.Source.CommitPrefixWordHistory
import Vegas.Source.CommitPrefixProduct
import Vegas.Game.PhaseCommitWordSourceView
import Interaction.ReactiveEmissionOrder
import Vegas.Pending.PhaseProposalPacketLaw
import Vegas.Game.PhaseProposalGeneratedPreparation
import Vegas.Game.PhaseProposalGenuineReference
import Vegas.Pending.PhaseProposalLostRecallReplay

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

namespace Vegas.PhaseProposalQualifiedBinding

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability
open scoped ENNReal

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))
  (values : ∀ who (key : setup.ProposalRecoveryComponent who),
    PMF (setup.CommitRecoveryValueChoice who key.1))

/-- The original ordinary source policy with all future flags zero. -/
def sourceUnflaggedStrategy : ∀ who, setup.proposalRecoveryModel.BehavioralPolicy who :=
  setup.proposalRecoveryNormalizedTrembledProfile
    0 le_rfl zero_le_one 0 le_rfl zero_le_one 0 le_rfl zero_le_one values

/-- The actual remaining commitment instructions, including the closing row. -/
def sourceCommitFuel (history : setup.proposalRecoveryProtocol.History) : Nat :=
  history.state.elim 0 fun current =>
    ProtocolState.remaining setup.program current.point -
      ProtocolState.commitEnd setup.program current.point

open Classical in
/-- Insert a choice at the actual source information, then run the original
zero-flag kernel through the remaining commitment instructions. -/
def sourceForcedBlock (who : Player) (history : setup.proposalRecoveryProtocol.History)
    (choice : setup.proposalRecoveryModel.Choice who
      (setup.proposalRecoveryModel.infoOf who history.trace)) :
    PMF setup.proposalRecoveryProtocol.History :=
  let profile := sourceUnflaggedStrategy setup values
  (setup.proposalRecoveryModel.runBehavioralFrom
    (Profile.update (sig := setup.proposalRecoveryModel.behavioralSignature) profile who
      ((profile who).commit (setup.proposalRecoveryModel.infoOf who history.trace) choice))
    1 history).bind
      (setup.proposalRecoveryModel.runBehavioralFrom profile (sourceCommitFuel setup history - 1))

omit [Fintype Player] in
private theorem suffix_injective
    {wholeΓ Γ : SourceCtx Player L} {wholeO O : Finset VarId}
    {whole : SourceProgram Player L wholeΓ wholeO} {program : SourceProgram Player L Γ O}
    {lift : ProtocolState program → ProtocolState whole}
    (origin : ProtocolSuffix whole program lift) : Function.Injective lift := by
  induction origin with
  | initial => exact Function.injective_id
  | sampleTail fresh law next previous ih =>
      exact fun _ _ same => Sum.inr.inj (ih same)
  | commitTail fresh guard next previous ih =>
      exact fun _ _ same => Sum.inr.inj (ih same)
  | revealTail fresh selected unresolved next previous ih =>
      exact fun _ _ same => Sum.inr.inj (ih same)

open Classical in
/-- Pull a point through the actual suffix and its entry constructor. This
partial inverse does not inspect a source posterior or a selected source tag. -/
private def residualEntry?
    {wholeΓ Γ : SourceCtx Player L} {wholeO O : Finset VarId}
    {whole : SourceProgram Player L wholeΓ wholeO} (program : SourceProgram Player L Γ O)
    (lift : ProtocolState program → ProtocolState whole) (point : ProtocolState whole) :
    Option (SourceProgram.Config Player L Γ) :=
  if present : ∃ entry, lift (ProtocolState.entry program entry) = point then
    some (Classical.choose present)
  else none

omit [Fintype Player] in
private theorem residualEntry?_eq_some_iff
    {wholeΓ Γ : SourceCtx Player L} {wholeO O : Finset VarId}
    {whole : SourceProgram Player L wholeΓ wholeO} {program : SourceProgram Player L Γ O}
    {lift : ProtocolState program → ProtocolState whole}
    (origin : ProtocolSuffix whole program lift) (point : ProtocolState whole)
    (entry : SourceProgram.Config Player L Γ) :
    residualEntry? program lift point = some entry ↔
      lift (ProtocolState.entry program entry) = point := by
  classical
  unfold residualEntry?
  split_ifs with present
  · constructor
    · intro same
      have chosen := Classical.choose_spec present
      exact Option.some.inj same ▸ chosen
    · intro same
      congr 1
      apply ProtocolState.entry_injective program
      apply suffix_injective origin
      exact (Classical.choose_spec present).trans same.symm
  · constructor
    · intro impossible
      cases impossible
    · intro same
      exact False.elim (present ⟨entry, same⟩)

omit [Fintype Player] in
private theorem residualEntry?_entry
    {wholeΓ Γ : SourceCtx Player L} {wholeO O : Finset VarId}
    {whole : SourceProgram Player L wholeΓ wholeO} {program : SourceProgram Player L Γ O}
    {lift : ProtocolState program → ProtocolState whole}
    (origin : ProtocolSuffix whole program lift) (entry : SourceProgram.Config Player L Γ) :
    residualEntry? program lift (lift (ProtocolState.entry program entry)) = some entry :=
  (residualEntry?_eq_some_iff origin _ entry).mpr rfl


section NativeCheckpoint

variable (implementation : ReservedConcurrentImplementation setup)

local notation "nativeApplication" => implementation.application
local notation "nativeMenu" => PhaseCount.onePacketMenu implementation.runtime
  implementation.leaks implementation.bounds
local notation "nativeInitial" => implementation.initial
local notation "nativeProtocol" =>
  ReactiveApplication.ResponseMenu.protocol
    (PhaseCount.onePacketMenu implementation.runtime implementation.leaks
      implementation.bounds) implementation.initial
      implementation.horizon implementation.scheduler
local notation "sourceModel" => setup.proposalRecoveryModel

open Classical in
private def sourceBindingAt
    (attempt : CommitAttemptId) (event : (serviceGraph setup .concurrent).EventId)
    (owner : Player) (payload : L.Ty)
    (binding : (serviceGraph setup .concurrent).outputLayout event = .binding owner payload) :
    ∀ {state}, setup.proposalRecoveryProtocol.Trace state → Option (L.Val payload)
  | _, .start => none
  | _, @Trace.extend _ _ before _ prior joint _ _ =>
      match before with
      | none => sourceBindingAt attempt event owner payload binding prior
      | some current =>
        if current.generation = attempt.generation ∧
            instructionCount setup.program -
              ProtocolState.remaining setup.program current.saved = attempt.phase ∧
            instructionCount setup.program -
              ProtocolState.remaining setup.program current.point = event.val then
          match phaseRecoveryBindingData setup .concurrent event owner payload binding
              ((joint owner).map (·.semantic)) with
          | (.success value, false) => some value
          | _ => none
        else sourceBindingAt attempt event owner payload binding prior

omit [Fintype Player] in
private theorem sourceBindingAt_extend
    (attempt : CommitAttemptId) (event : (serviceGraph setup .concurrent).EventId)
    (owner : Player) (payload : L.Ty)
    (binding : (serviceGraph setup .concurrent).outputLayout event = .binding owner payload)
    (current : CommitRecoveryState setup.program)
    (prior : setup.proposalRecoveryProtocol.Trace (some current))
    (joint : Player → Option (ProposalRecoveryMove Player L))
    (legal : setup.proposalRecoveryProtocol.Legal (some current) joint)
    (after : setup.proposalRecoveryProtocol.State)
    (realized : after ∈ (setup.proposalRecoveryProtocol.step (some current)
      ⟨joint, legal⟩).support)
    (generation : current.generation = attempt.generation)
    (saved : instructionCount setup.program -
      ProtocolState.remaining setup.program current.saved = attempt.phase)
    (position : instructionCount setup.program -
      ProtocolState.remaining setup.program current.point = event.val)
    (value : L.Val payload)
    (read : phaseRecoveryBindingData setup .concurrent event owner payload binding
      ((joint owner).map (·.semantic)) = (.success value, false)) :
    sourceBindingAt setup attempt event owner payload binding
      (prior.extend joint legal realized) = some value := by
  simp only [sourceBindingAt, generation, saved, position, and_self, ↓reduceIte]
  exact congrArg (fun data : PublicationResult (L.Val payload) × Bool =>
    match data with
    | (.success result, false) => some result
    | _ => none) read

omit [Fintype Player] in
private theorem sourceBindingAt_other_address
    (attempt : CommitAttemptId) (event : (serviceGraph setup .concurrent).EventId)
    (owner : Player) (payload : L.Ty)
    (binding : (serviceGraph setup .concurrent).outputLayout event = .binding owner payload)
    (current : CommitRecoveryState setup.program)
    (prior : setup.proposalRecoveryProtocol.Trace (some current))
    (joint : Player → Option (ProposalRecoveryMove Player L))
    (legal : setup.proposalRecoveryProtocol.Legal (some current) joint)
    (after : setup.proposalRecoveryProtocol.State)
    (realized : after ∈ (setup.proposalRecoveryProtocol.step (some current)
      ⟨joint, legal⟩).support)
    (different : ¬ (current.generation = attempt.generation ∧
      instructionCount setup.program -
        ProtocolState.remaining setup.program current.saved = attempt.phase ∧
      instructionCount setup.program -
        ProtocolState.remaining setup.program current.point = event.val)) :
    sourceBindingAt setup attempt event owner payload binding
        (prior.extend joint legal realized) =
      sourceBindingAt setup attempt event owner payload binding prior := by
  simp only [sourceBindingAt, different, ↓reduceIte]

omit [Fintype Player] in
private theorem sourceBindingAt_origin
    (attempt : CommitAttemptId) (event : (serviceGraph setup .concurrent).EventId)
    (owner : Player) (payload : L.Ty)
    (binding : (serviceGraph setup .concurrent).outputLayout event = .binding owner payload)
    {state} (trace : setup.proposalRecoveryProtocol.Trace state) (value : L.Val payload)
    (read : sourceBindingAt setup attempt event owner payload binding trace = some value) :
    ∃ (current : CommitRecoveryState setup.program)
      (prior : setup.proposalRecoveryProtocol.Trace (some current))
      (joint : Player → Option (ProposalRecoveryMove Player L))
      (legal : setup.proposalRecoveryProtocol.Legal (some current) joint)
      (after : setup.proposalRecoveryProtocol.State)
      (realized : after ∈ (setup.proposalRecoveryProtocol.step (some current)
        ⟨joint, legal⟩).support),
      TracePrefix (prior.extend joint legal realized) trace ∧
      current.generation = attempt.generation ∧
      instructionCount setup.program -
        ProtocolState.remaining setup.program current.saved = attempt.phase ∧
      instructionCount setup.program -
        ProtocolState.remaining setup.program current.point = event.val ∧
      phaseRecoveryBindingData setup .concurrent event owner payload binding
        ((joint owner).map (·.semantic)) = (.success value, false) := by
  induction trace with
  | start => cases read
  | @extend before after prior joint legal realized ih =>
      cases before with
      | none =>
          obtain ⟨current, source, choices, offered, target, moved, priorPrefix, rest⟩ := ih read
          exact ⟨current, source, choices, offered, target, moved,
            TracePrefix.extend priorPrefix joint legal realized, rest⟩
      | some current =>
          by_cases addressed : current.generation = attempt.generation ∧
              instructionCount setup.program -
                ProtocolState.remaining setup.program current.saved = attempt.phase ∧
              instructionCount setup.program -
                ProtocolState.remaining setup.program current.point = event.val
          · have row : phaseRecoveryBindingData setup .concurrent event owner payload binding
                ((joint owner).map (·.semantic)) = (.success value, false) := by
              simp only [sourceBindingAt, addressed] at read
              cases data : phaseRecoveryBindingData setup .concurrent event owner payload binding
                  ((joint owner).map (·.semantic)) with
              | mk result omitted =>
                  cases result <;> cases omitted <;> simp_all
            exact ⟨current, prior, joint, legal, after, realized, .refl,
              addressed.1, addressed.2.1, addressed.2.2, row⟩
          · have earlier : sourceBindingAt setup attempt event owner payload binding prior =
                some value := by
              simpa only [sourceBindingAt, addressed, ↓reduceIte] using read
            obtain ⟨sourceState, source, choices, offered, target, moved, priorPrefix, rest⟩ :=
              ih earlier
            exact ⟨sourceState, source, choices, offered, target, moved,
              TracePrefix.extend priorPrefix joint legal realized, rest⟩

open Classical in
private def sourceHandleMeaning
    (target : setup.proposalRecoveryProtocol.History)
    (control : (nativeApplication).Control)
    (handle : Handle (serviceGraph setup .concurrent)) : Option (Raw L) :=
  match handle.2 with
  | .initial _ => target.state.bind fun current =>
      match (EventGraphRuntime.State.initial
          (graph := serviceGraph setup .concurrent)
          (encodeInputs (ProtocolState.base setup.program current.point))).candidates.lookup
          handle with
      | .openable raw => some raw
      | .fresh | .unopenable => none
  | .prepared _ =>
      (control.execution.recall handle.1).findSome? fun entry =>
        entry.emitted.bind fun message =>
          match message.payload.packet.call with
          | .commitment event candidate =>
              if candidate = handle then
                match binding : (serviceGraph setup .concurrent).outputLayout event with
                | .binding owner payload =>
                    (sourceBindingAt setup message.payload.attempt event owner payload binding
                      target.trace).map fun value => (⟨payload, value⟩ : Raw L)
                | _ => none
              else none
          | _ => none

private def sourceHandlePairs
    (target : setup.proposalRecoveryProtocol.History)
    (control : (nativeApplication).Control)
    (lost : Handle (serviceGraph setup .concurrent) → Option (Raw L))
    (handle : Handle (serviceGraph setup .concurrent)) : Option (Raw L × Raw L) :=
  match control.execution.application.current.native.candidates.lookup handle with
  | .openable before =>
      ((sourceHandleMeaning setup implementation target control handle).orElse
        (fun _ => lost handle)).map fun after => (before, after)
  | .fresh | .unopenable => none

omit [Fintype Player] in
private theorem sourceHandlePairs_maps
    (target : setup.proposalRecoveryProtocol.History)
    (control : (nativeApplication).Control)
    (lost : Handle (serviceGraph setup .concurrent) → Option (Raw L))
    (handle : Handle (serviceGraph setup .concurrent)) (before after : Raw L)
    (registered : control.execution.application.current.native.candidates.lookup handle =
      .openable before)
    (read : sourceHandleMeaning setup implementation target control handle = some after) :
    EventGraph.pairSwap (sourceHandlePairs setup implementation target control lost handle)
      before = after := by
  classical
  simp only [sourceHandlePairs, registered, read, Option.orElse_some, Option.map_some,
    EventGraph.pairSwap, Equiv.swap_apply_left]

omit [Fintype Player] in
private theorem sourceHandlePairs_involutive
    (target : setup.proposalRecoveryProtocol.History)
    (control : (nativeApplication).Control)
    (lost : Handle (serviceGraph setup .concurrent) → Option (Raw L))
    (handle : Handle (serviceGraph setup .concurrent)) :
    Function.Involutive
      (EventGraph.pairSwap (sourceHandlePairs setup implementation target control lost handle)) :=
  EventGraph.pairSwap_involutive _

open Classical in
private def sourceSnapshotPair
    (target : setup.proposalRecoveryProtocol.History)
    (control : (nativeApplication).Control)
    (lost : Handle (serviceGraph setup .concurrent) → Option (Raw L))
    (snapshot : EventGraphRuntime.State (serviceGraph setup .concurrent))
    (field : (serviceGraph setup .concurrent).Field) :
    Option (((serviceGraph setup .concurrent).layout field).Value ×
      ((serviceGraph setup .concurrent).layout field).Value) :=
  if (serviceGraph setup .concurrent).fieldPublic field then none else
    (snapshot.config.store field).bind fun before =>
      match field with
      | .inl input => target.state.map fun current =>
          (before, encodeInputs (ProtocolState.base setup.program current.point) input)
      | .inr event =>
          match nodeView (serviceGraph setup .concurrent) event with
          | .bind _owner payload shape _ =>
              match cast (congrArg EventField.Value shape) before with
              | .failure => none
              | .success first =>
                  (snapshot.accepted (.inr event)).bind fun handle =>
                    ((sourceHandleMeaning setup implementation target control handle).orElse
                      (fun _ => lost handle)).bind fun raw =>
                        (raw.as? payload).map fun second =>
                          (cast (congrArg EventField.Value shape.symm) (.success first),
                            cast (congrArg EventField.Value shape.symm) (.success second))
          | .resolve .. | .sample .. => none

omit [Fintype Player] in
private theorem sourceSnapshotPair_public
    (target : setup.proposalRecoveryProtocol.History)
    (control : (nativeApplication).Control)
    (lost : Handle (serviceGraph setup .concurrent) → Option (Raw L))
    (snapshot : EventGraphRuntime.State (serviceGraph setup .concurrent))
    (field : (serviceGraph setup .concurrent).Field)
    (visible : (serviceGraph setup .concurrent).fieldPublic field) :
    sourceSnapshotPair setup implementation target control lost snapshot field = none := by
  classical
  simp only [sourceSnapshotPair, visible, ↓reduceIte]

omit [Fintype Player] in
private theorem sourceSnapshotPair_binding
    (target : setup.proposalRecoveryProtocol.History)
    (control : (nativeApplication).Control)
    (lost : Handle (serviceGraph setup .concurrent) → Option (Raw L))
    (snapshot : EventGraphRuntime.State (serviceGraph setup .concurrent))
    (event : (serviceGraph setup .concurrent).EventId) (owner : Player) (payload : L.Ty)
    (shape : (serviceGraph setup .concurrent).outputLayout event = .binding owner payload)
    (first second : ((serviceGraph setup .concurrent).outputLayout event).Value)
    (paired : sourceSnapshotPair setup implementation target control lost snapshot (.inr event) =
      some (first, second)) :
    first ≠ cast (congrArg EventField.Value shape.symm) .failure ∧
      second ≠ cast (congrArg EventField.Value shape.symm) .failure := by
  classical
  unfold sourceSnapshotPair at paired
  split at paired
  · cases paired
  · obtain ⟨before, _stored, paired⟩ := Option.bind_eq_some_iff.mp paired
    dsimp only at paired
    cases descriptor : nodeView (serviceGraph setup .concurrent) event with
    | bind other ty outputEq codeEq =>
        have kinds := EventField.binding.inj (outputEq.symm.trans shape)
        obtain ⟨rfl, rfl⟩ := kinds
        rw [descriptor] at paired
        dsimp only at paired
        cases result : cast (congrArg EventField.Value outputEq) before with
        | failure =>
            rw [result] at paired
            cases paired
        | success value =>
            rw [result] at paired
            obtain ⟨handle, _accepted, paired⟩ := Option.bind_eq_some_iff.mp paired
            obtain ⟨raw, _meaning, paired⟩ := Option.bind_eq_some_iff.mp paired
            obtain ⟨next, _typed, pairEq⟩ := Option.map_eq_some_iff.mp paired
            obtain ⟨rfl, rfl⟩ := Prod.mk.inj pairEq
            constructor <;> intro impossible <;>
              have contradiction := congrArg (cast (congrArg EventField.Value shape)) impossible
            all_goals
              simp only [cast_cast, cast_eq] at contradiction
              cases contradiction
    | resolve other ty ref checks outputEq codeEq =>
        simp only [descriptor] at paired
        cases paired
    | sample ty law outputEq codeEq =>
        simp only [descriptor] at paired
        cases paired

omit [Fintype Player] in
private theorem sourceSnapshotPair_binding_value
    (target : setup.proposalRecoveryProtocol.History)
    (reference : (nativeApplication).Control)
    (lost : Handle (serviceGraph setup .concurrent) → Option (Raw L))
    (snapshot : EventGraphRuntime.State (serviceGraph setup .concurrent))
    (event : (serviceGraph setup .concurrent).EventId) (owner : Player) (payload : L.Ty)
    (shape : (serviceGraph setup .concurrent).outputLayout event = .binding owner payload)
    (code : cast (congrArg (EventCode (serviceGraph setup .concurrent).layout) shape)
      ((serviceGraph setup .concurrent).nodes event) = .bind owner payload)
    (node : nodeView (serviceGraph setup .concurrent) event = .bind owner payload shape code)
    (handle : Handle (serviceGraph setup .concurrent)) (old next : L.Val payload)
    (stored : snapshot.config.store (.inr event) =
      some (cast (congrArg EventField.Value shape.symm) (.success old)))
    (accepted : snapshot.accepted (.inr event) = some handle)
    (meaning : sourceHandleMeaning setup implementation target reference handle =
      some (⟨payload, next⟩ : Raw L)) :
    sourceSnapshotPair setup implementation target reference lost snapshot (.inr event) =
      some (cast (congrArg EventField.Value shape.symm) (.success old),
        cast (congrArg EventField.Value shape.symm) (.success next)) := by
  classical
  have hidden : ¬ (serviceGraph setup .concurrent).fieldPublic (.inr event) := by
    change ¬ ((serviceGraph setup .concurrent).outputLayout event).IsPublic
    rw [shape]
    exact not_false
  simp only [sourceSnapshotPair, hidden, ↓reduceIte, stored, Option.bind_some, node,
    cast_cast, cast_eq, accepted, meaning, Option.orElse_some, Raw.as?, ↓reduceDIte,
    Option.map_some]

private def sourceSnapshotPairs
    (target : setup.proposalRecoveryProtocol.History)
    (control : (nativeApplication).Control)
    (lost : Handle (serviceGraph setup .concurrent) → Option (Raw L))
    (snapshot : EventGraphRuntime.State (serviceGraph setup .concurrent)) :
    (serviceGraph setup .concurrent).SwapPairs where
  pair := sourceSnapshotPair setup implementation target control lost snapshot
  public_none := sourceSnapshotPair_public setup implementation target control lost snapshot
  binding_success := sourceSnapshotPair_binding setup implementation target control lost snapshot

private def sourceSnapshotState
    (target : setup.proposalRecoveryProtocol.History)
    (reference : (nativeApplication).Control)
    (lost : Handle (serviceGraph setup .concurrent) → Option (Raw L))
    (snapshot : EventGraphRuntime.State (serviceGraph setup .concurrent)) :
    EventGraphRuntime.State (serviceGraph setup .concurrent) :=
  snapshot.swap (HiddenSwap.ofPairs
    (sourceSnapshotPairs setup implementation target reference lost snapshot)
    (sourceHandlePairs setup implementation target reference lost))

private def sourceSnapshotAssignment
    (target : setup.proposalRecoveryProtocol.History)
    (reference : (nativeApplication).Control)
    (lost : Handle (serviceGraph setup .concurrent) → Option (Raw L))
    (before : PhaseRuntimeState (serviceGraph setup .concurrent)) :
    PhaseRuntimeState (serviceGraph setup .concurrent) :=
  { before with
    entry := { before.entry with
      native := sourceSnapshotState setup implementation target reference lost before.entry.native }
    current := { before.current with
      native := sourceSnapshotState setup implementation target reference lost
        before.current.native }
    retired := before.retired.map fun record => { record with
      state := sourceSnapshotState setup implementation target reference lost record.state } }

omit [Fintype Player] in
private theorem sourceSnapshotPair_accept_other
    (target : setup.proposalRecoveryProtocol.History)
    (reference : (nativeApplication).Control)
    (lost : Handle (serviceGraph setup .concurrent) → Option (Raw L))
    (before : EventGraphRuntime.State (serviceGraph setup .concurrent))
    (event : (serviceGraph setup .concurrent).EventId)
    (ready : before.config.cut.Ready event)
    (action : (serviceGraph setup .concurrent).Action event)
    (value : ((serviceGraph setup .concurrent).outputLayout event).Value)
    (handle : Handle (serviceGraph setup .concurrent))
    (field : (serviceGraph setup .concurrent).Field)
    (different : field ≠ Sum.inr event) :
    sourceSnapshotPair setup implementation target reference lost
        { before.complete event ready action value with
          accepted := Function.update before.accepted (.inr event) (some handle)
          candidates := before.candidates.freeze handle } field =
      sourceSnapshotPair setup implementation target reference lost before field := by
  classical
  have store :
      (before.complete event ready action value).config.store field =
        before.config.store field := by
    cases field with
    | inl input => rfl
    | inr query =>
        exact Config.complete_output_of_ne before.config event query ready action value
          (fun same => different (congrArg Sum.inr same))
  unfold sourceSnapshotPair
  split
  · rfl
  · change ((before.complete event ready action value).config.store field).bind _ = _
    rw [store]
    cases field with
    | inl input => rfl
    | inr query =>
        simp only [Function.update_of_ne different]

omit [Fintype Player] in
private theorem sourceSnapshotSwap_accept_before
    (target : setup.proposalRecoveryProtocol.History)
    (reference : (nativeApplication).Control)
    (lost : Handle (serviceGraph setup .concurrent) → Option (Raw L))
    (before : EventGraphRuntime.State (serviceGraph setup .concurrent))
    (event : (serviceGraph setup .concurrent).EventId)
    (ready : before.config.cut.Ready event)
    (action : (serviceGraph setup .concurrent).Action event)
    (value : ((serviceGraph setup .concurrent).outputLayout event).Value)
    (handle : Handle (serviceGraph setup .concurrent)) :
    let after : EventGraphRuntime.State (serviceGraph setup .concurrent) :=
      { before.complete event ready action value with
        accepted := Function.update before.accepted (.inr event) (some handle)
        candidates := before.candidates.freeze handle }
    before.swap (HiddenSwap.ofPairs
        (sourceSnapshotPairs setup implementation target reference lost after)
        (sourceHandlePairs setup implementation target reference lost)) =
      before.swap (HiddenSwap.ofPairs
        (sourceSnapshotPairs setup implementation target reference lost before)
        (sourceHandlePairs setup implementation target reference lost)) := by
  classical
  dsimp only
  let after : EventGraphRuntime.State (serviceGraph setup .concurrent) :=
    { before.complete event ready action value with
      accepted := Function.update before.accepted (.inr event) (some handle)
      candidates := before.candidates.freeze handle }
  have other (field : (serviceGraph setup .concurrent).Field)
      (different : field ≠ Sum.inr event) :
      (sourceSnapshotPairs setup implementation target reference lost after).pair field =
        (sourceSnapshotPairs setup implementation target reference lost before).pair field :=
    sourceSnapshotPair_accept_other setup implementation target reference lost before event
      ready action value handle field different
  have absent : before.config.outputs event = none := by
    cases read : before.config.outputs event with
    | none => rfl
    | some value =>
        exact False.elim (ready.1 ((before.config.output_available event).mp
          (by simp only [read, Option.isSome_some])))
  have sameConfig :
      before.config.swap (ValueSwap.ofPairs
        (sourceSnapshotPairs setup implementation target reference lost after)) =
      before.config.swap (ValueSwap.ofPairs
        (sourceSnapshotPairs setup implementation target reference lost before)) := by
    apply Config.ext_fields
    · funext input
      change EventGraph.pairSwap
        ((sourceSnapshotPairs setup implementation target reference lost after).pair (.inl input))
          _ = _
      rw [other (.inl input) (by simp)]
      rfl
    · rfl
    · funext query
      change (before.config.outputs query).map _ = (before.config.outputs query).map _
      by_cases same : query = event
      · subst query
        rw [absent]
        rfl
      · change (before.config.outputs query).map
          (EventGraph.pairSwap ((sourceSnapshotPairs setup implementation target reference lost
            after).pair (.inr query))) = _
        rw [other (.inr query) (fun equal => same (Sum.inr.inj equal))]
        rfl
    · change before.config.history.map _ = before.config.history.map _
      apply List.map_congr_left
      intro completion member
      have different : completion.event ≠ event := by
        intro same
        apply ready.1
        apply (before.config.history_exact event).mp
        exact same ▸ List.mem_map.mpr ⟨completion, member, rfl⟩
      have pairs := other (.inr completion.event)
        (fun same => different (Sum.inr.inj same))
      change Completion.mk completion.event
        ((sourceSnapshotPairs setup implementation target reference lost after).action
          completion.event completion.action) = _
      congr 1
      change (sourceSnapshotPairs setup implementation target reference lost after).action
        completion.event completion.action =
        (sourceSnapshotPairs setup implementation target reference lost before).action
          completion.event completion.action
      unfold SwapPairs.action
      rw [pairs]
  change State.mk _ _ _ _ _ = State.mk _ _ _ _ _
  simp only [State.mk.injEq]
  refine ⟨sameConfig, ?_, ?_, ?_, ?_⟩ <;> first | rfl | trivial

omit [Fintype Player] in
private theorem sourceSnapshot_handle_binding
    (target : setup.proposalRecoveryProtocol.History)
    (reference : (nativeApplication).Control)
    (lost : Handle (serviceGraph setup .concurrent) → Option (Raw L))
    (runtime : EventGraphRuntime (serviceGraph setup .concurrent))
    (before after : EventGraphRuntime.State (serviceGraph setup .concurrent))
    (id : MessageId Player) (event : (serviceGraph setup .concurrent).EventId)
    (handle : Handle (serviceGraph setup .concurrent)) (owner : Player) (payload : L.Ty)
    (shape : (serviceGraph setup .concurrent).outputLayout event = .binding owner payload)
    (old next : L.Val payload)
    (original : before.candidates.lookup handle = .openable (⟨payload, old⟩ : Raw L))
    (registered : reference.execution.application.current.native.candidates.lookup handle =
      .openable (⟨payload, old⟩ : Raw L))
    (meaning : sourceHandleMeaning setup implementation target reference handle =
      some (⟨payload, next⟩ : Raw L))
    (accepted : EventGraphRuntime.handle runtime before ⟨id, .commitment event handle⟩ =
      some after) :
    EventGraphRuntime.handle runtime
        (before.swap (HiddenSwap.ofPairs
          (sourceSnapshotPairs setup implementation target reference lost before)
          (sourceHandlePairs setup implementation target reference lost)))
        ⟨id, .commitment event handle⟩ =
      some (after.swap (HiddenSwap.ofPairs
        (sourceSnapshotPairs setup implementation target reference lost after)
        (sourceHandlePairs setup implementation target reference lost))) := by
  classical
  obtain ⟨ready, timely, actualOwner, actualPayload, actualShape, code, node, sender,
    handleOwner, vacant, unused⟩ :=
    handle_commitment_conditions runtime before after id event handle accepted
  obtain ⟨rfl, rfl⟩ := EventField.binding.inj (shape.symm.trans actualShape)
  have result : before.bindingResult handle payload = .success old := by
    simp only [State.bindingResult, original, Raw.as?, ↓reduceDIte, cast_eq, Option.elim_some]
  have afterEq : after =
      { before.complete event ready
          (cast (congrArg EventField.Action shape.symm) (.success old))
          (cast (congrArg EventField.Value shape.symm) (.success old)) with
        accepted := Function.update before.accepted (.inr event) (some handle)
        candidates := before.candidates.freeze handle } := by
    have actual := handle_commitment_eq runtime before id event handle owner payload shape code
      node ready timely sender handleOwner vacant unused
    rw [result] at actual
    exact Option.some.inj (accepted.symm.trans actual)
  let swap := HiddenSwap.ofPairs
    (sourceSnapshotPairs setup implementation target reference lost after)
    (sourceHandlePairs setup implementation target reference lost)
  have handlePair : sourceHandlePairs setup implementation target reference lost handle =
      some ((⟨payload, old⟩ : Raw L), (⟨payload, next⟩ : Raw L)) := by
    simp only [sourceHandlePairs, registered, meaning, Option.orElse_some, Option.map_some]
  have fieldPair :
      (sourceSnapshotPairs setup implementation target reference lost after).pair (.inr event) =
        some (cast (congrArg EventField.Value shape.symm) (.success old),
          cast (congrArg EventField.Value shape.symm) (.success next)) := by
    apply sourceSnapshotPair_binding_value setup implementation target reference lost after
      event owner payload shape code node handle old next
    · rw [afterEq]
      exact Config.complete_output_same _ _ _ _ _
    · rw [afterEq]
      simp only [Function.update_self]
    · exact meaning
  have compatible : BindCompatible swap event handle :=
    HiddenSwap.bindCompatible_ofPairs _ _ shape old next fieldPair handlePair
  have preEq : before.swap swap =
      before.swap (HiddenSwap.ofPairs
        (sourceSnapshotPairs setup implementation target reference lost before)
        (sourceHandlePairs setup implementation target reference lost)) := by
    dsimp only [swap]
    rw [afterEq]
    exact sourceSnapshotSwap_accept_before setup implementation target reference lost before
      event ready _ _ handle
  rw [← preEq]
  have replay := handle_swap runtime swap before ⟨id, .commitment event handle⟩
    (by
      intro state actualEvent actualHandle _ packet
      obtain ⟨rfl, rfl⟩ := Payload.commitment.inj packet
      exact compatible)
    (by
      intro actualEvent opening _
      obtain ⟨candidate, raw, impossible⟩ := opening
      cases impossible)
  rw [replay, accepted, Option.map_some]

omit [Fintype Player] in
private theorem sourceSnapshot_handle_failed_binding
    (target : setup.proposalRecoveryProtocol.History)
    (reference : (nativeApplication).Control)
    (lost : Handle (serviceGraph setup .concurrent) → Option (Raw L))
    (runtime : EventGraphRuntime (serviceGraph setup .concurrent))
    (before after : EventGraphRuntime.State (serviceGraph setup .concurrent))
    (id : MessageId Player) (event : (serviceGraph setup .concurrent).EventId)
    (handle : Handle (serviceGraph setup .concurrent)) (owner : Player) (payload : L.Ty)
    (shape : (serviceGraph setup .concurrent).outputLayout event = .binding owner payload)
    (failed : before.bindingResult handle payload = .failure)
    (unchanged : sourceHandlePairs setup implementation target reference lost handle = none)
    (accepted : EventGraphRuntime.handle runtime before ⟨id, .commitment event handle⟩ =
      some after) :
    EventGraphRuntime.handle runtime
        (sourceSnapshotState setup implementation target reference lost before)
        ⟨id, .commitment event handle⟩ =
      some (sourceSnapshotState setup implementation target reference lost after) := by
  classical
  obtain ⟨ready, timely, actualOwner, actualPayload, actualShape, code, node, sender,
    handleOwner, vacant, unused⟩ :=
    handle_commitment_conditions runtime before after id event handle accepted
  obtain ⟨rfl, rfl⟩ := EventField.binding.inj (shape.symm.trans actualShape)
  have afterEq : after =
      { before.complete event ready
          (cast (congrArg EventField.Action shape.symm) (PublicationResult.failure :
            PublicationResult (L.Val payload)))
          (cast (congrArg EventField.Value shape.symm) (PublicationResult.failure :
            PublicationResult (L.Val payload))) with
        accepted := Function.update before.accepted (.inr event) (some handle)
        candidates := before.candidates.freeze handle } := by
    have actual := handle_commitment_eq runtime before id event handle owner payload shape code
      node ready timely sender handleOwner vacant unused
    rw [failed] at actual
    exact Option.some.inj (accepted.symm.trans actual)
  let swap := HiddenSwap.ofPairs
    (sourceSnapshotPairs setup implementation target reference lost after)
    (sourceHandlePairs setup implementation target reference lost)
  have eventNone : (sourceSnapshotPairs setup implementation target reference lost after).pair
      (.inr event) = none := by
    simp only [sourceSnapshotPairs, sourceSnapshotPair]
    split
    · rfl
    · simp only [afterEq, State.complete, Config.store, Config.complete_output_same,
        Option.bind_some, node, cast_cast, cast_eq]
  have compatible : BindCompatible swap event handle :=
    HiddenSwap.bindCompatible_ofPairs_none _ _ eventNone unchanged
  have beforeEq : before.swap swap =
      sourceSnapshotState setup implementation target reference lost before := by
    dsimp only [swap, sourceSnapshotState]
    rw [afterEq]
    exact sourceSnapshotSwap_accept_before setup implementation target reference lost before
      event ready _ _ handle
  change EventGraphRuntime.handle runtime
      (sourceSnapshotState setup implementation target reference lost before)
      ⟨id, .commitment event handle⟩ = some (after.swap swap)
  rw [← beforeEq]
  have replay := handle_swap runtime swap before ⟨id, .commitment event handle⟩
    (by
      intro state actualEvent actualHandle _ packet
      obtain ⟨rfl, rfl⟩ := Payload.commitment.inj packet
      exact compatible)
    (by
      intro actualEvent opening _
      obtain ⟨candidate, raw, impossible⟩ := opening
      cases impossible)
  rw [replay, accepted, Option.map_some]

omit [Fintype Player] in
private theorem sourceSnapshotPair_submit
    (target : setup.proposalRecoveryProtocol.History)
    (reference : (nativeApplication).Control)
    (lost : Handle (serviceGraph setup .concurrent) → Option (Raw L))
    (before : EventGraphRuntime.State (serviceGraph setup .concurrent))
    (who : Player) (material : WitnessedSubmission (serviceGraph setup .concurrent)) :
    sourceSnapshotPair setup implementation target reference lost
        (submitStep (material.call.register before who) who material.call.packet) =
      sourceSnapshotPair setup implementation target reference lost before := by
  have registered := material.call.register_facts who before
  have configEq := (submitStep_config (material.call.register before who) who
    material.call.packet).trans registered.1
  have acceptedEq := congrArg PublicView.accepted
    ((submitStep_publicView (material.call.register before who) who material.call.packet).trans
      registered.2)
  change (submitStep (material.call.register before who) who material.call.packet).accepted =
    before.accepted at acceptedEq
  funext field
  unfold sourceSnapshotPair
  rw [configEq, acceptedEq]

omit [Fintype Player] in
private theorem sourceSnapshot_submit
    (target : setup.proposalRecoveryProtocol.History)
    (reference : (nativeApplication).Control)
    (lost : Handle (serviceGraph setup .concurrent) → Option (Raw L))
    (before : EventGraphRuntime.State (serviceGraph setup .concurrent))
    (who : Player) (material : WitnessedSubmission (serviceGraph setup .concurrent)) :
    let swap := HiddenSwap.ofPairs
      (sourceSnapshotPairs setup implementation target reference lost before)
      (sourceHandlePairs setup implementation target reference lost)
    let after := submitStep (material.call.register before who) who material.call.packet
    submitStep (((material.swap swap).call).register (before.swap swap) who) who
        (material.swap swap).call.packet =
      after.swap (HiddenSwap.ofPairs
        (sourceSnapshotPairs setup implementation target reference lost after)
        (sourceHandlePairs setup implementation target reference lost)) := by
  classical
  dsimp only
  rw [WitnessedSubmission.submit_swap]
  have pairsEq :
      sourceSnapshotPairs setup implementation target reference lost
          (submitStep (material.call.register before who) who material.call.packet) =
        sourceSnapshotPairs setup implementation target reference lost before := by
    unfold sourceSnapshotPairs
    congr 1
    exact sourceSnapshotPair_submit setup implementation target reference lost before who material
  rw [pairsEq]

omit [Fintype Player] in
private theorem sourceSnapshotPair_complete_public
    (target : setup.proposalRecoveryProtocol.History)
    (reference : (nativeApplication).Control)
    (lost : Handle (serviceGraph setup .concurrent) → Option (Raw L))
    (before : EventGraphRuntime.State (serviceGraph setup .concurrent))
    (event : (serviceGraph setup .concurrent).EventId)
    (ready : before.config.cut.Ready event)
    (action : (serviceGraph setup .concurrent).Action event)
    (value : ((serviceGraph setup .concurrent).outputLayout event).Value)
    (visible : (serviceGraph setup .concurrent).fieldPublic (.inr event)) :
    sourceSnapshotPair setup implementation target reference lost
        (before.complete event ready action value) =
      sourceSnapshotPair setup implementation target reference lost before := by
  classical
  funext field
  by_cases same : field = Sum.inr event
  · subst field
    simp only [sourceSnapshotPair, visible, ↓reduceIte]
  · have store : (before.complete event ready action value).config.store field =
        before.config.store field := by
      cases field with
      | inl input => rfl
      | inr query =>
          exact Config.complete_output_of_ne before.config event query ready action value
            (fun equal => same (congrArg Sum.inr equal))
    unfold sourceSnapshotPair
    split
    · rfl
    · change ((before.complete event ready action value).config.store field).bind _ = _
      rw [store]
      rfl

omit [Fintype Player] in
private theorem sourceSnapshotPair_sample
    (target : setup.proposalRecoveryProtocol.History)
    (reference : (nativeApplication).Control)
    (lost : Handle (serviceGraph setup .concurrent) → Option (Raw L))
    (runtime : EventGraphRuntime (serviceGraph setup .concurrent))
    (before after : EventGraphRuntime.State (serviceGraph setup .concurrent))
    (event : (serviceGraph setup .concurrent).EventId)
    (supported : after ∈ (environmentStep runtime before (.executeSample event)).support) :
    sourceSnapshotPair setup implementation target reference lost after =
      sourceSnapshotPair setup implementation target reference lost before := by
  classical
  by_cases ready : before.config.cut.Ready event
  · cases node : nodeView (serviceGraph setup .concurrent) event with
    | bind owner payload shape code =>
        rw [environmentStep_executeSample_of_nonsample runtime before event ready (by
          intro other law output code sample
          rw [node] at sample
          cases sample), PMF.mem_support_pure_iff] at supported
        cases supported
        rfl
    | resolve owner payload binding checks shape code =>
        rw [environmentStep_executeSample_of_nonsample runtime before event ready (by
          intro other law output code sample
          rw [node] at sample
          cases sample), PMF.mem_support_pure_iff] at supported
        cases supported
        rfl
    | sample payload law shape code =>
        rw [environmentStep_executeSample_eq runtime before event ready payload law
          shape code node, Config.step, PMF.map_comp, PMF.support_map] at supported
        obtain ⟨value, _positive, rfl⟩ := supported
        exact sourceSnapshotPair_complete_public setup implementation target reference lost
          before event ready _ value (by
            change ((serviceGraph setup .concurrent).outputLayout event).IsPublic
            rw [shape]
            trivial)
  · rw [environmentStep_executeSample_of_not_ready runtime before event ready,
      PMF.mem_support_pure_iff] at supported
    cases supported
    rfl

omit [Fintype Player] in
private theorem sourceSnapshotPair_completeFailure
    (target : setup.proposalRecoveryProtocol.History)
    (reference : (nativeApplication).Control)
    (lost : Handle (serviceGraph setup .concurrent) → Option (Raw L))
    (before : EventGraphRuntime.State (serviceGraph setup .concurrent))
    (event : (serviceGraph setup .concurrent).EventId)
    (ready : before.config.cut.Ready event) :
    sourceSnapshotPair setup implementation target reference lost
        (before.completeFailure event ready) =
      sourceSnapshotPair setup implementation target reference lost before := by
  classical
  have absent : before.config.outputs event = none := by
    cases read : before.config.outputs event with
    | none => rfl
    | some value =>
        exact False.elim (ready.1 ((before.config.output_available event).mp
          (by simp only [read, Option.isSome_some])))
  have acceptedEq : (before.completeFailure event ready).accepted = before.accepted := by
    unfold State.completeFailure
    split <;> rfl
  funext field
  by_cases same : field = Sum.inr event
  · subst field
    cases node : nodeView (serviceGraph setup .concurrent) event with
    | bind owner payload shape code =>
        have hidden : ¬ (serviceGraph setup .concurrent).fieldPublic (.inr event) := by
          change ¬ ((serviceGraph setup .concurrent).outputLayout event).IsPublic
          rw [shape]
          exact not_false
        simp [sourceSnapshotPair, hidden, State.completeFailure, node, State.complete,
          Config.store, Config.complete, absent]
    | resolve owner payload binding checks shape code =>
        have visible : (serviceGraph setup .concurrent).fieldPublic (.inr event) := by
          change ((serviceGraph setup .concurrent).outputLayout event).IsPublic
          rw [shape]
          trivial
        exact (sourceSnapshotPair_public setup implementation target reference lost
          (before.completeFailure event ready) (.inr event) visible).trans
            (sourceSnapshotPair_public setup implementation target reference lost before
              (.inr event) visible).symm
    | sample => simp only [State.completeFailure, node]
  · have storeEq : (before.completeFailure event ready).config.store field =
        before.config.store field := by
      cases field with
      | inl input =>
          unfold State.completeFailure
          split <;> rfl
      | inr query =>
          have different : query ≠ event := fun equal => same (congrArg Sum.inr equal)
          unfold State.completeFailure
          split
          · exact Config.complete_output_of_ne _ _ _ _ _ _ different
          · exact Config.complete_output_of_ne _ _ _ _ _ _ different
          · rfl
    unfold sourceSnapshotPair
    rw [storeEq, acceptedEq]

omit [Fintype Player] in
private theorem sourceSnapshotPair_expiry
    (target : setup.proposalRecoveryProtocol.History)
    (reference : (nativeApplication).Control)
    (lost : Handle (serviceGraph setup .concurrent) → Option (Raw L))
    (runtime : EventGraphRuntime (serviceGraph setup .concurrent))
    (before after : EventGraphRuntime.State (serviceGraph setup .concurrent))
    (event : (serviceGraph setup .concurrent).EventId)
    (supported : after ∈ (environmentStep runtime before (.expire event)).support) :
    sourceSnapshotPair setup implementation target reference lost after =
      sourceSnapshotPair setup implementation target reference lost before := by
  classical
  have stutter (law : environmentStep runtime before (.expire event) = PMF.pure before) :
      sourceSnapshotPair setup implementation target reference lost after =
        sourceSnapshotPair setup implementation target reference lost before := by
    rw [law, PMF.mem_support_pure_iff] at supported
    cases supported
    rfl
  by_cases ready : before.config.cut.Ready event
  · cases activated : before.activatedAt event with
    | none =>
        exact stutter
          (environmentStep_expire_of_not_activated runtime before event ready activated)
    | some entered =>
      by_cases due : runtime.deadline event ≤ before.clock - entered
      · cases node : nodeView (serviceGraph setup .concurrent) event with
        | bind owner payload shape code =>
          rw [environmentStep_expire_bind_eq runtime before event ready entered activated due
            owner payload shape code node, PMF.mem_support_pure_iff] at supported
          subst after
          simpa only [State.completeFailure, node] using
            sourceSnapshotPair_completeFailure setup implementation target reference lost
              before event ready
        | resolve owner payload binding checks shape code =>
          rw [environmentStep_expire_resolve_eq runtime before event ready entered activated due
            owner payload binding checks shape code node, PMF.mem_support_pure_iff] at supported
          subst after
          exact sourceSnapshotPair_complete_public setup implementation target reference lost
            before event ready _ _ (by
              change ((serviceGraph setup .concurrent).outputLayout event).IsPublic
              rw [shape]
              trivial)
        | sample payload law shape code =>
          exact stutter (environmentStep_expire_sample_eq runtime before event ready entered
            activated due payload law shape code node)
      · exact stutter
          (environmentStep_expire_of_not_due runtime before event ready entered activated due)
  · exact stutter (environmentStep_expire_of_not_ready runtime before event ready)

omit [Fintype Player] in
private theorem sourceSnapshot_environment
    (target : setup.proposalRecoveryProtocol.History)
    (reference : (nativeApplication).Control)
    (lost : Handle (serviceGraph setup .concurrent) → Option (Raw L))
    (runtime : EventGraphRuntime (serviceGraph setup .concurrent))
    (before : EventGraphRuntime.State (serviceGraph setup .concurrent))
    (command : EnvironmentCommand (serviceGraph setup .concurrent)) :
    environmentStep runtime (sourceSnapshotState setup implementation target reference lost before)
        command =
      (environmentStep runtime before command).map
        (sourceSnapshotState setup implementation target reference lost) := by
  classical
  unfold sourceSnapshotState
  rw [environmentStep_swap runtime _ before command
    (fun address _ _ _ _ _ => ValueSwap.ofPairs_expiryFixed _ address)]
  apply GameTheory.Math.Probability.map_congr_on_support
  intro after supported
  have pairsEq : sourceSnapshotPairs setup implementation target reference lost after =
      sourceSnapshotPairs setup implementation target reference lost before := by
    unfold sourceSnapshotPairs
    congr 1
    cases command with
    | advanceClock =>
      simp only [environmentStep, PMF.mem_support_pure_iff] at supported
      subst after
      rfl
    | executeSample event =>
      exact sourceSnapshotPair_sample setup implementation target reference lost runtime
        before after event supported
    | expire event =>
      exact sourceSnapshotPair_expiry setup implementation target reference lost runtime
        before after event supported
  rw [pairsEq]

omit [Fintype Player] in
private theorem sourceSnapshot_reveal_fixed_initial
    (target : setup.proposalRecoveryProtocol.History)
    (reference : (nativeApplication).Control)
    (lost : Handle (serviceGraph setup .concurrent) → Option (Raw L))
    (before : EventGraphRuntime.State (serviceGraph setup .concurrent))
    (source : CommitRecoveryState setup.program) (present : target.state = some source)
    (event : (serviceGraph setup .concurrent).EventId)
    (input : (serviceGraph setup .concurrent).InputId)
    (owner : Player) (payload : L.Ty)
    (binding : FieldRef (serviceGraph setup .concurrent).layout (.binding owner payload))
    (checks : List (GuardCheck (serviceGraph setup .concurrent).layout payload))
    (shape : (serviceGraph setup .concurrent).outputLayout event = .publication payload)
    (code : cast (congrArg (EventCode (serviceGraph setup .concurrent).layout) shape)
      ((serviceGraph setup .concurrent).nodes event) = .resolve owner payload binding checks)
    (node : nodeView (serviceGraph setup .concurrent) event =
      .resolve owner payload binding checks shape code)
    (field : binding.field = .inl input)
    (kind : (serviceGraph setup .concurrent).inputLayout input = .binding owner payload)
    (value : L.Val payload)
    (stored : before.config.store (.inl input) =
      some (cast (congrArg EventField.Value kind.symm) (.success value)))
    (initial : encodeInputs (ProtocolState.base setup.program source.point) input =
      cast (congrArg EventField.Value kind.symm) (.success value))
    (accepted : before.accepted (.inl input) = some (owner, .initial input))
    (registered : reference.execution.application.current.native.candidates.lookup
      (owner, .initial input) = .openable (⟨payload, value⟩ : Raw L)) :
    RevealFixed (HiddenSwap.ofPairs
      (sourceSnapshotPairs setup implementation target reference lost before)
      (sourceHandlePairs setup implementation target reference lost)) before event := by
  classical
  have targetCandidate := State.initial_candidate_binding_success
    (encodeInputs (ProtocolState.base setup.program source.point)) input owner payload kind value
    (by rw [initial]; simp only [cast_cast, cast_eq])
  have meaning : sourceHandleMeaning setup implementation target reference
      (owner, .initial input) = some (⟨payload, value⟩ : Raw L) := by
    simp only [sourceHandleMeaning, present, Option.bind_some, targetCandidate]
  rw [RevealFixed, node]
  constructor
  · change EventGraph.pairSwap
      (sourceSnapshotPair setup implementation target reference lost before binding.field) = id
    rw [field]
    unfold sourceSnapshotPair
    split
    · rfl
    · simp only [stored, Option.bind_some, present, Option.map_some, initial]
      simp [EventGraph.pairSwap]
  · intro candidate retainedHandle
    rw [field, accepted] at retainedHandle
    have same : candidate = (owner, .initial input) := (Option.some.inj retainedHandle).symm
    subst candidate
    change EventGraph.pairSwap
      (sourceHandlePairs setup implementation target reference lost (owner, .initial input)) = id
    simp [sourceHandlePairs, registered, meaning, EventGraph.pairSwap]

omit [Fintype Player] in
private theorem sourceSnapshot_reveal_fixed_output
    (target : setup.proposalRecoveryProtocol.History)
    (reference : (nativeApplication).Control)
    (lost : Handle (serviceGraph setup .concurrent) → Option (Raw L))
    (before : EventGraphRuntime.State (serviceGraph setup .concurrent))
    (event bound : (serviceGraph setup .concurrent).EventId)
    (owner : Player) (payload : L.Ty)
    (binding : FieldRef (serviceGraph setup .concurrent).layout (.binding owner payload))
    (checks : List (GuardCheck (serviceGraph setup .concurrent).layout payload))
    (shape : (serviceGraph setup .concurrent).outputLayout event = .publication payload)
    (code : cast (congrArg (EventCode (serviceGraph setup .concurrent).layout) shape)
      ((serviceGraph setup .concurrent).nodes event) = .resolve owner payload binding checks)
    (node : nodeView (serviceGraph setup .concurrent) event =
      .resolve owner payload binding checks shape code)
    (field : binding.field = .inr bound)
    (boundShape : (serviceGraph setup .concurrent).outputLayout bound = .binding owner payload)
    (boundCode : cast (congrArg (EventCode (serviceGraph setup .concurrent).layout) boundShape)
      ((serviceGraph setup .concurrent).nodes bound) = .bind owner payload)
    (boundNode : nodeView (serviceGraph setup .concurrent) bound =
      .bind owner payload boundShape boundCode)
    (handle : Handle (serviceGraph setup .concurrent)) (value : L.Val payload)
    (stored : before.config.store (.inr bound) =
      some (cast (congrArg EventField.Value boundShape.symm) (.success value)))
    (accepted : before.accepted (.inr bound) = some handle)
    (registered : reference.execution.application.current.native.candidates.lookup handle =
      .openable (⟨payload, value⟩ : Raw L))
    (meaning : sourceHandleMeaning setup implementation target reference handle =
      some (⟨payload, value⟩ : Raw L)) :
    RevealFixed (HiddenSwap.ofPairs
      (sourceSnapshotPairs setup implementation target reference lost before)
      (sourceHandlePairs setup implementation target reference lost)) before event := by
  classical
  rw [RevealFixed, node]
  constructor
  · change EventGraph.pairSwap
      (sourceSnapshotPair setup implementation target reference lost before binding.field) = id
    rw [field, sourceSnapshotPair_binding_value setup implementation target reference lost
      before bound owner payload boundShape boundCode boundNode handle value value
      stored accepted meaning]
    simp [EventGraph.pairSwap]
  · intro candidate present
    rw [field, accepted] at present
    have same : candidate = handle := (Option.some.inj present).symm
    subst candidate
    change EventGraph.pairSwap
      (sourceHandlePairs setup implementation target reference lost handle) = id
    simp [sourceHandlePairs, registered, meaning, EventGraph.pairSwap]

omit [Fintype Player] in
private theorem sourceSnapshot_handle_opening
    (target : setup.proposalRecoveryProtocol.History)
    (reference : (nativeApplication).Control)
    (lost : Handle (serviceGraph setup .concurrent) → Option (Raw L))
    (runtime : EventGraphRuntime (serviceGraph setup .concurrent))
    (before : EventGraphRuntime.State (serviceGraph setup .concurrent))
    (id : MessageId Player) (event : (serviceGraph setup .concurrent).EventId)
    (handle : Handle (serviceGraph setup .concurrent)) (raw : Raw L)
    (fixed : RevealFixed (HiddenSwap.ofPairs
      (sourceSnapshotPairs setup implementation target reference lost before)
      (sourceHandlePairs setup implementation target reference lost)) before event) :
    EventGraphRuntime.handle runtime
        (sourceSnapshotState setup implementation target reference lost before)
        ⟨id, .opening event handle raw⟩ =
      (EventGraphRuntime.handle runtime before ⟨id, .opening event handle raw⟩).map
        (sourceSnapshotState setup implementation target reference lost) := by
  classical
  let swap := HiddenSwap.ofPairs
    (sourceSnapshotPairs setup implementation target reference lost before)
    (sourceHandlePairs setup implementation target reference lost)
  have replay := handle_swap runtime swap before ⟨id, .opening event handle raw⟩
    (by intro next other candidate _ impossible; cases impossible)
    (by
      intro other packet _
      obtain ⟨candidate, value, equal⟩ := packet
      have same : event = other := (Payload.opening.inj equal).1
      subst other
      exact fixed)
  cases step : EventGraphRuntime.handle runtime before ⟨id, .opening event handle raw⟩ with
  | none => simpa only [step, Option.map_none, sourceSnapshotState, swap] using replay
  | some after =>
      obtain ⟨ready, _timely, owner, payload, binding, checks, shape, code, value, result,
        _node, _sender, _owner, _accepted, _raw, _catalogue, _stored, _evaluated, completed⟩ :=
        handle_opening_conditions runtime before after id event handle raw step
      have visible : (serviceGraph setup .concurrent).fieldPublic (.inr event) := by
        change ((serviceGraph setup .concurrent).outputLayout event).IsPublic
        rw [shape]
        trivial
      have pairEq : sourceSnapshotPairs setup implementation target reference lost after =
          sourceSnapshotPairs setup implementation target reference lost before := by
        unfold sourceSnapshotPairs
        congr 1
        rw [completed]
        exact sourceSnapshotPair_complete_public setup implementation target reference lost
          before event ready _ _ visible
      simpa only [step, Option.map_some, sourceSnapshotState, pairEq, swap] using replay

omit [Fintype Player] in
private theorem sourceSnapshotPair_drain
    (target : setup.proposalRecoveryProtocol.History)
    (reference : (nativeApplication).Control)
    (lost : Handle (serviceGraph setup .concurrent) → Option (Raw L))
    (phase : RuntimePhase (serviceGraph setup .concurrent))
    (before : RecoveryState (serviceGraph setup .concurrent)) :
    sourceSnapshotPair setup implementation target reference lost (phase.drain before).native =
      sourceSnapshotPair setup implementation target reference lost before.native := by
  suffices ∀ fuel (state : RecoveryState (serviceGraph setup .concurrent)),
      sourceSnapshotPair setup implementation target reference lost
          (phase.drainFuel fuel state).native =
        sourceSnapshotPair setup implementation target reference lost state.native from
    this _ before
  intro fuel
  induction fuel with
  | zero => intro state; rfl
  | succ fuel ih =>
      intro state
      unfold RuntimePhase.drainFuel
      split
      · rename_i pending
        rw [ih]
        exact sourceSnapshotPair_completeFailure setup implementation target reference lost
          state.native _ _
      · rfl

omit [Fintype Player] in
private theorem sourceSnapshotPair_restore
    (target : setup.proposalRecoveryProtocol.History)
    (reference : (nativeApplication).Control)
    (lost : Handle (serviceGraph setup .concurrent) → Option (Raw L))
    (entry current : RecoveryState (serviceGraph setup .concurrent)) :
    sourceSnapshotPair setup implementation target reference lost
        (PhaseRuntimeState.restore entry current).native =
      sourceSnapshotPair setup implementation target reference lost entry.native := rfl

omit [Fintype Player] in
private theorem sourceSnapshotAssignment_normalize
    (target : setup.proposalRecoveryProtocol.History)
    (reference : (nativeApplication).Control)
    (lost : Handle (serviceGraph setup .concurrent) → Option (Raw L))
    (before : PhaseRuntimeState (serviceGraph setup .concurrent)) :
    (sourceSnapshotAssignment setup implementation target reference lost before).normalize =
      sourceSnapshotAssignment setup implementation target reference lost before.normalize := by
  classical
  let image (state : RecoveryState (serviceGraph setup .concurrent)) :=
    { state with native :=
        sourceSnapshotState setup implementation target reference lost state.native }
  let retire (record : RetiredCommitAttempt (serviceGraph setup .concurrent)) :=
    { record with state :=
        sourceSnapshotState setup implementation target reference lost record.state }
  have excluded (state : RecoveryState (serviceGraph setup .concurrent)) :
      (image state).excluded = state.excluded := rfl
  have drain (phase : RuntimePhase (serviceGraph setup .concurrent))
      (state : RecoveryState (serviceGraph setup .concurrent)) :
      phase.drain (image state) = image (phase.drain state) := by
    have pairsEq : sourceSnapshotPairs setup implementation target reference lost
        (phase.drain state).native =
        sourceSnapshotPairs setup implementation target reference lost state.native := by
      unfold sourceSnapshotPairs
      congr 1
      exact sourceSnapshotPair_drain setup implementation target reference lost phase state
    change phase.drain (state.swap (HiddenSwap.ofPairs
      (sourceSnapshotPairs setup implementation target reference lost state.native)
      (sourceHandlePairs setup implementation target reference lost))) = _
    rw [phase.drain_swap _ state (fun event => ValueSwap.ofPairs_expiryFixed _ event)]
    dsimp only [image, sourceSnapshotState, RecoveryState.swap]
    rw [pairsEq]
  have restore (entry current : RecoveryState (serviceGraph setup .concurrent)) :
      PhaseRuntimeState.restore (image entry) (image current) =
        image (PhaseRuntimeState.restore entry current) := by
    have pairsEq : sourceSnapshotPairs setup implementation target reference lost
        (PhaseRuntimeState.restore entry current).native =
        sourceSnapshotPairs setup implementation target reference lost entry.native := by
      rfl
    dsimp only [image, sourceSnapshotState]
    rw [pairsEq]
    rfl
  have finished (phase : RuntimePhase (serviceGraph setup .concurrent))
      (state : RecoveryState (serviceGraph setup .concurrent)) :
      phase.Finished (image state) ↔ phase.Finished state :=
    RuntimePhase.finished_swap _ phase state
  have settle : ∀ (phases : List (RuntimePhase (serviceGraph setup .concurrent)))
      generation entry current retired,
      PhaseRuntimeState.settle phases generation (image entry) (image current)
          (retired.map retire) =
        sourceSnapshotAssignment setup implementation target reference lost
          (PhaseRuntimeState.settle phases generation entry current retired) := by
    intro phases
    induction phases with
    | nil => intro generation entry current retired; rfl
    | cons phase remaining ih =>
      intro generation entry current retired
      simp only [PhaseRuntimeState.settle, drain, finished, excluded]
      by_cases done : phase.Finished (phase.drain current)
      · simp only [done, ↓reduceIte]
        by_cases missed : phase.kind = .commitment ∧
            (((phase.drain current).excluded \ entry.excluded) ∩ phase.owners).Nonempty
        · simp only [missed, and_self, ↓reduceIte]
          by_cases survives : (phase.owners \ (phase.drain current).excluded).Nonempty
          · simp only [survives, ↓reduceIte, restore, drain]
            simp only [sourceSnapshotAssignment, image, retire, List.map_append,
              List.map_cons, List.map_nil]
          · simp only [survives, ↓reduceIte, restore, drain]
            have next := ih generation
              (phase.drain (PhaseRuntimeState.restore entry (phase.drain current)))
              (phase.drain (PhaseRuntimeState.restore entry (phase.drain current)))
              (retired ++ [⟨⟨phase.low, generation⟩, (phase.drain current).native⟩])
            rw [List.map_append, List.map_cons, List.map_nil] at next
            exact next
        · simp only [missed, ↓reduceIte]
          exact ih generation (phase.drain current) (phase.drain current) retired
      · simp only [done, ↓reduceIte]
        rfl
  exact settle before.phases before.generation before.entry before.current before.retired

omit [Fintype Player] in
private theorem properBinding_opening
    (material : WitnessedSubmission (serviceGraph setup .concurrent))
    (event : (serviceGraph setup .concurrent).EventId)
    (handle : Handle (serviceGraph setup .concurrent)) (owner : Player) (payload : L.Ty)
    (shape : (serviceGraph setup .concurrent).outputLayout event = .binding owner payload)
    (value : L.Val payload)
    (packet : material.call.packet = .commitment event handle)
    (prepared : PhaseProposal.bindingPreparation material = some (⟨payload, value⟩ : Raw L)) :
    material.call.opening = some (⟨payload, value⟩ : Raw L) := by
  classical
  unfold PhaseProposal.bindingPreparation at prepared
  rw [packet] at prepared
  dsimp only at prepared
  rw [shape] at prepared
  obtain ⟨sampled, typed, same⟩ := Option.map_eq_some_iff.mp prepared
  have sampledEq : sampled = value := eq_of_heq (Raw.mk.inj same).2
  subst sampled
  obtain ⟨raw, opening, decoded⟩ := Option.bind_eq_some_iff.mp typed
  have rawEq : raw = (⟨payload, value⟩ : Raw L) := by
    rcases raw with ⟨ty, data⟩
    unfold Raw.as? at decoded
    split at decoded
    · rename_i sameType
      cases sameType
      simp only [cast_eq, Option.some.injEq] at decoded
      cases decoded
      rfl
    · contradiction
  exact opening.trans (congrArg some rawEq)

omit [Fintype Player] in
private theorem properBinding_calls_eq
    (first second : WitnessedSubmission (serviceGraph setup .concurrent))
    (event : (serviceGraph setup .concurrent).EventId)
    (handle : Handle (serviceGraph setup .concurrent)) (owner : Player) (payload : L.Ty)
    (shape : (serviceGraph setup .concurrent).outputLayout event = .binding owner payload)
    (value : L.Val payload)
    (firstPacket : first.call.packet = .commitment event handle)
    (secondPacket : second.call.packet = .commitment event handle)
    (firstPrepared : PhaseProposal.bindingPreparation first = some (⟨payload, value⟩ : Raw L))
    (secondPrepared : PhaseProposal.bindingPreparation second = some (⟨payload, value⟩ : Raw L)) :
    first.call = second.call := by
  have firstOpening := properBinding_opening setup first event handle owner payload shape value
    firstPacket firstPrepared
  have secondOpening := properBinding_opening setup second event handle owner payload shape value
    secondPacket secondPrepared
  cases firstCall : first.call
  cases secondCall : second.call
  simp only [firstCall, secondCall] at firstPacket secondPacket firstOpening secondOpening ⊢
  congr 1
  · exact firstPacket.trans secondPacket.symm
  · exact firstOpening.trans secondOpening.symm

omit [Fintype Player] in
private theorem sourceSnapshotAssignment_submit
    (target : setup.proposalRecoveryProtocol.History)
    (reference : (nativeApplication).Control)
    (lost : Handle (serviceGraph setup .concurrent) → Option (Raw L))
    (before : PhaseRuntimeState (serviceGraph setup .concurrent))
    (who : Player) (material : WitnessedSubmission (serviceGraph setup .concurrent)) :
    let swap := HiddenSwap.ofPairs
      (sourceSnapshotPairs setup implementation target reference lost before.current.native)
      (sourceHandlePairs setup implementation target reference lost)
    (sourceSnapshotAssignment setup implementation target reference lost before).submit
        who (material.swap swap) =
      sourceSnapshotAssignment setup implementation target reference lost
        (before.submit who material) := by
  classical
  dsimp only
  have native := sourceSnapshot_submit setup implementation target reference lost
    before.current.native who material
  dsimp only at native
  change ({ sourceSnapshotAssignment setup implementation target reference lost before with
    current := ⟨_, before.current.excluded⟩ } :
      PhaseRuntimeState (serviceGraph setup .concurrent)) = _
  change submitStep _ _ _ = sourceSnapshotState setup implementation target reference lost
    (submitStep (material.call.register before.current.native who) who material.call.packet)
    at native
  dsimp only [sourceSnapshotAssignment, sourceSnapshotState]
  rw [native]
  rfl

omit [Fintype Player] in
private theorem sourceSnapshotAssignment_handle_binding
    (target : setup.proposalRecoveryProtocol.History)
    (reference : (nativeApplication).Control)
    (lost : Handle (serviceGraph setup .concurrent) → Option (Raw L))
    (runtime : EventGraphRuntime (serviceGraph setup .concurrent))
    (before after : PhaseRuntimeState (serviceGraph setup .concurrent))
    (message : Message Player (CommitAttemptPacket (serviceGraph setup .concurrent)))
    (event : (serviceGraph setup .concurrent).EventId)
    (handle : Handle (serviceGraph setup .concurrent)) (owner : Player) (payload : L.Ty)
    (shape : (serviceGraph setup .concurrent).outputLayout event = .binding owner payload)
    (old next : L.Val payload)
    (packet : message.payload.packet.call = .commitment event handle)
    (original : before.current.native.candidates.lookup handle =
      .openable (⟨payload, old⟩ : Raw L))
    (registered : reference.execution.application.current.native.candidates.lookup handle =
      .openable (⟨payload, old⟩ : Raw L))
    (meaning : sourceHandleMeaning setup implementation target reference handle =
      some (⟨payload, next⟩ : Raw L))
    (accepted : before.handle runtime message = some after) :
    (sourceSnapshotAssignment setup implementation target reference lost before).handle
        runtime message =
      some (sourceSnapshotAssignment setup implementation target reference lost after) := by
  classical
  unfold PhaseRuntimeState.handle at accepted ⊢
  have gate :
      (message.payload.tokenValid
          (sourceSnapshotAssignment setup implementation target reference lost before).attempt &&
        (sourceSnapshotAssignment setup implementation target reference lost before).allows
          message.payload.packet.call &&
        !(sourceSnapshotAssignment setup implementation target reference lost
            before).current.excludedCall message.payload.packet.call) =
      (message.payload.tokenValid before.attempt && before.allows message.payload.packet.call &&
        !before.current.excludedCall message.payload.packet.call) := rfl
  rw [gate]
  split at accepted
  · rename_i admitted
    rw [ite_eq_left admitted]
    cases nativeStep : EventGraphRuntime.handle runtime before.current.native
        ⟨message.id, message.payload.packet.call⟩ with
    | none => simp only [nativeStep, Option.map_none, reduceCtorEq] at accepted
    | some native =>
      have nativeAccepted : EventGraphRuntime.handle runtime before.current.native
          ⟨message.id, .commitment event handle⟩ = some native := by
        simpa only [packet] using nativeStep
      have replay := sourceSnapshot_handle_binding setup implementation target reference lost
        runtime before.current.native native message.id event handle owner payload shape
        old next original registered meaning nativeAccepted
      change EventGraphRuntime.handle runtime
          (sourceSnapshotState setup implementation target reference lost before.current.native)
          ⟨message.id, .commitment event handle⟩ =
        some (sourceSnapshotState setup implementation target reference lost native) at replay
      have actual : ({ before with current :=
          before.current.inclusionResult message.payload.packet.call native } :
            PhaseRuntimeState (serviceGraph setup .concurrent)).normalize = after := by
        exact Option.some.inj (by simpa only [nativeStep, Option.map_some] using accepted)
      change Option.map _ (EventGraphRuntime.handle runtime
        (sourceSnapshotState setup implementation target reference lost before.current.native)
        ⟨message.id, message.payload.packet.call⟩) = _
      rw [packet, replay, Option.map_some]
      have updated :
          ({ sourceSnapshotAssignment setup implementation target reference lost before with
            current :=
              (sourceSnapshotAssignment setup implementation target reference lost
                  before).current.inclusionResult (.commitment event handle)
                  (sourceSnapshotState setup implementation target reference lost native) } :
                    PhaseRuntimeState (serviceGraph setup .concurrent)) =
          sourceSnapshotAssignment setup implementation target reference lost
            { before with
              current := before.current.inclusionResult (.commitment event handle) native } := rfl
      rw [updated, sourceSnapshotAssignment_normalize]
      simpa only [packet] using congrArg
        (fun state => some
          (sourceSnapshotAssignment setup implementation target reference lost state))
        actual
  · cases accepted

omit [Fintype Player] in
private theorem sourceSnapshotAssignment_handle_opening
    (target : setup.proposalRecoveryProtocol.History)
    (reference : (nativeApplication).Control)
    (lost : Handle (serviceGraph setup .concurrent) → Option (Raw L))
    (runtime : EventGraphRuntime (serviceGraph setup .concurrent))
    (before : PhaseRuntimeState (serviceGraph setup .concurrent))
    (message : Message Player (CommitAttemptPacket (serviceGraph setup .concurrent)))
    (event : (serviceGraph setup .concurrent).EventId)
    (handle : Handle (serviceGraph setup .concurrent)) (raw : Raw L)
    (packet : message.payload.packet.call = .opening event handle raw)
    (fixed : RevealFixed (HiddenSwap.ofPairs
      (sourceSnapshotPairs setup implementation target reference lost before.current.native)
      (sourceHandlePairs setup implementation target reference lost)) before.current.native event) :
    (sourceSnapshotAssignment setup implementation target reference lost before).handle
        runtime message =
      (before.handle runtime message).map
        (sourceSnapshotAssignment setup implementation target reference lost) := by
  classical
  unfold PhaseRuntimeState.handle
  have gate :
      (message.payload.tokenValid
          (sourceSnapshotAssignment setup implementation target reference lost before).attempt &&
        (sourceSnapshotAssignment setup implementation target reference lost before).allows
          message.payload.packet.call &&
        !(sourceSnapshotAssignment setup implementation target reference lost
            before).current.excludedCall message.payload.packet.call) =
      (message.payload.tokenValid before.attempt && before.allows message.payload.packet.call &&
        !before.current.excludedCall message.payload.packet.call) := rfl
  rw [gate]
  split
  · change Option.map _ (EventGraphRuntime.handle runtime
        (sourceSnapshotState setup implementation target reference lost before.current.native)
        ⟨message.id, message.payload.packet.call⟩) = _
    rw [packet, sourceSnapshot_handle_opening setup implementation target reference lost
      runtime before.current.native message.id event handle raw fixed, Option.map_map,
      Option.map_map]
    congr 1
    funext native
    change
      ({ sourceSnapshotAssignment setup implementation target reference lost before with
        current := (sourceSnapshotAssignment setup implementation target reference lost
            before).current.inclusionResult (.opening event handle raw)
            (sourceSnapshotState setup implementation target reference lost native) } :
              PhaseRuntimeState (serviceGraph setup .concurrent)).normalize = _
    have updated :
        ({ sourceSnapshotAssignment setup implementation target reference lost before with
          current := (sourceSnapshotAssignment setup implementation target reference lost
              before).current.inclusionResult (.opening event handle raw)
              (sourceSnapshotState setup implementation target reference lost native) } :
                PhaseRuntimeState (serviceGraph setup .concurrent)) =
        sourceSnapshotAssignment setup implementation target reference lost
          { before with
            current := before.current.inclusionResult (.opening event handle raw) native } := by
      simp only [sourceSnapshotAssignment, RecoveryState.inclusionResult, sourceSnapshotState,
        RecoveryState.publicationFailed_swap]
    rw [updated, sourceSnapshotAssignment_normalize]
    rfl
  · rfl

omit [Fintype Player] in
private theorem sourceSnapshotAssignment_environment
    (target : setup.proposalRecoveryProtocol.History)
    (reference : (nativeApplication).Control)
    (lost : Handle (serviceGraph setup .concurrent) → Option (Raw L))
    (runtime : EventGraphRuntime (serviceGraph setup .concurrent))
    (before : PhaseRuntimeState (serviceGraph setup .concurrent))
    (command : EnvironmentCommand (serviceGraph setup .concurrent)) :
    (sourceSnapshotAssignment setup implementation target reference lost before).environment
        runtime command =
      (before.environment runtime command).map
        (sourceSnapshotAssignment setup implementation target reference lost) := by
  classical
  unfold PhaseRuntimeState.environment
  have allowed : (sourceSnapshotAssignment setup implementation target reference lost
      before).commandAllowed command = before.commandAllowed command := rfl
  rw [allowed]
  split
  · change ((environmentStep runtime
      (sourceSnapshotState setup implementation target reference lost before.current.native)
      command).map _) = _
    rw [sourceSnapshot_environment, PMF.map_comp, PMF.map_comp]
    congr 1
    funext native
    dsimp only [Function.comp_apply]
    have updated :
        ({ sourceSnapshotAssignment setup implementation target reference lost before with
          current :=
            (sourceSnapshotAssignment setup implementation target reference lost
              before).current.environmentResult command
                (sourceSnapshotState setup implementation target reference lost native) } :
                  PhaseRuntimeState (serviceGraph setup .concurrent)) =
        sourceSnapshotAssignment setup implementation target reference lost
          { before with current := before.current.environmentResult command native } := by
      cases command <;> rfl
    rw [updated, sourceSnapshotAssignment_normalize]
  · rw [PMF.pure_map]

omit [Fintype Player] in
private theorem sourceSnapshotAssignment_rejected_binding
    (target : setup.proposalRecoveryProtocol.History)
    (reference : (nativeApplication).Control)
    (lost : Handle (serviceGraph setup .concurrent) → Option (Raw L))
    (runtime : EventGraphRuntime (serviceGraph setup .concurrent))
    (before : PhaseRuntimeState (serviceGraph setup .concurrent))
    (message : Message Player (CommitAttemptPacket (serviceGraph setup .concurrent)))
    (event : (serviceGraph setup .concurrent).EventId)
    (handle : Handle (serviceGraph setup .concurrent))
    (packet : message.payload.packet.call = .commitment event handle)
    (rejected : before.handle runtime message = none) :
    (sourceSnapshotAssignment setup implementation target reference lost before).handle
        runtime message = none := by
  classical
  let swap := HiddenSwap.ofPairs
    (sourceSnapshotPairs setup implementation target reference lost before.current.native)
    (sourceHandlePairs setup implementation target reference lost)
  unfold PhaseRuntimeState.handle at rejected ⊢
  have gate :
      (message.payload.tokenValid
          (sourceSnapshotAssignment setup implementation target reference lost before).attempt &&
        (sourceSnapshotAssignment setup implementation target reference lost before).allows
          message.payload.packet.call &&
        !(sourceSnapshotAssignment setup implementation target reference lost
            before).current.excludedCall message.payload.packet.call) =
      (message.payload.tokenValid before.attempt && before.allows message.payload.packet.call &&
        !before.current.excludedCall message.payload.packet.call) := rfl
  rw [gate]
  split at rejected
  · rename_i admitted
    rw [ite_eq_left admitted]
    have nativeNone : EventGraphRuntime.handle runtime before.current.native
        ⟨message.id, message.payload.packet.call⟩ = none :=
      Option.map_eq_none_iff.mp rejected
    have replay := handle_swap runtime swap before.current.native
      ⟨message.id, message.payload.packet.call⟩
      (by
        intro native actualEvent actualHandle accepted _
        rw [nativeNone] at accepted
        cases accepted)
      (by
        intro actualEvent opening _
        obtain ⟨candidate, raw, impossible⟩ := opening
        rw [packet] at impossible
        cases impossible)
    change Option.map _ (EventGraphRuntime.handle runtime
      (before.current.native.swap swap) ⟨message.id, message.payload.packet.call⟩) = none
    rw [replay, nativeNone, Option.map_none, Option.map_none]
  · rename_i denied
    rw [ite_eq_right denied]

omit [Fintype Player] in
private theorem sourceSnapshotAssignment_public
    (target : setup.proposalRecoveryProtocol.History)
    (reference : (nativeApplication).Control)
    (lost : Handle (serviceGraph setup .concurrent) → Option (Raw L))
    (before : PhaseRuntimeState (serviceGraph setup .concurrent)) :
    (sourceSnapshotAssignment setup implementation target reference lost before).publicView =
      before.publicView := by
  simp only [sourceSnapshotAssignment, sourceSnapshotState, PhaseRuntimeState.publicView,
    State.swap_publicView, List.map_map, Function.comp_def, PhaseRuntimeState.attempt]

private theorem sourceSnapshot_binding_available
    (target : setup.proposalRecoveryProtocol.History)
    (reference : (nativeApplication).Control)
    (lost : Handle (serviceGraph setup .concurrent) → Option (Raw L))
    (left right : (nativeApplication).Execution)
    (application : right.application = sourceSnapshotAssignment setup implementation
      target reference lost left.application)
    (network : left.network = right.network)
    (leftRecall : PhaseCount.CountRecall implementation.runtime implementation.leaks left)
    (rightRecall : PhaseCount.CountRecall implementation.runtime implementation.leaks right)
    (owner : Player) (event : (serviceGraph setup .concurrent).EventId) (serial : Nat)
    (first second : Option (Raw L))
    (evidence : EvidenceRequest (serviceGraph setup .concurrent))
    (bounded : implementation.bounds.AllowsOpening second)
    (member : (⟨some ⟨⟨.commitment event (owner, .prepared serial), first⟩, evidence⟩⟩ :
      (nativeApplication).Action) ∈ PhaseCount.onePacketActions implementation.runtime
        implementation.leaks implementation.bounds owner (left.recall owner)
          (left.observe nativeApplication owner)) :
    (⟨some ⟨⟨.commitment event (owner, .prepared serial), second⟩, .none⟩⟩ :
      (nativeApplication).Action) ∈ PhaseCount.onePacketActions implementation.runtime
        implementation.leaks implementation.bounds owner (right.recall owner)
          (right.observe nativeApplication owner) := by
  classical
  let source : WitnessedSubmission (serviceGraph setup .concurrent) :=
    ⟨⟨.commitment event (owner, .prepared serial), first⟩, evidence⟩
  let replacement : WitnessedSubmission (serviceGraph setup .concurrent) :=
    ⟨⟨.commitment event (owner, .prepared serial), second⟩, .none⟩
  rw [PhaseCount.mem_onePacketActions] at member ⊢
  have permitted : PhaseCount.permits ((nativeApplication).outputs (left.recall owner))
      (PhaseCount.localEnvelope implementation.runtime implementation.leaks owner
        (left.recall owner) (left.observe nativeApplication owner) source) = true := by
    rcases member.2 with impossible | ⟨material, transmitted, allowed⟩
    · cases impossible
    · cases Option.some.inj transmitted
      exact allowed
  have correct := ((PhaseCount.permits_eq_true_iff _ _).mp permitted).2.1
  have call : (PhaseCount.nativeMessage (PhaseCount.localEnvelope implementation.runtime
      implementation.leaks owner (left.recall owner)
        (left.observe nativeApplication owner) source)).payload.call =
      .commitment event (owner, .prepared serial) := PhaseCount.maskPacket_call _ _
  unfold CountCallCorrect at correct
  rw [call] at correct
  have absent := correct.2.1
  have resolved : evidence.resolve owner
      (source.call.candidateAfter owner
        (left.observe nativeApplication owner).application.1.candidates)
      ((ReactiveApplication.ResponseMenu.knownPackets (left.recall owner)
        (left.observe nativeApplication owner)).map PhaseCount.nativeMessage) = none := by
    change (PhaseCount.maskPacket (left.observe nativeApplication owner).application.2
      ⟨source.call.packet, _, _⟩).evidence = none at absent
    unfold PhaseCount.maskPacket at absent
    split at absent <;> split at absent <;> exact absent
  have outputs : (nativeApplication).outputs (left.recall owner) =
      (nativeApplication).outputs (right.recall owner) := by
    rw [← leftRecall.1 owner, ← rightRecall.1 owner, network]
  have serials : (nativeApplication).submissionCount (left.recall owner) =
      (nativeApplication).submissionCount (right.recall owner) := by
    rw [← leftRecall.2.1 owner, ← rightRecall.2.1 owner, network]
  have publicEq : left.application.publicView = right.application.publicView := by
    rw [application, sourceSnapshotAssignment_public]
  have nativePublic : left.application.current.native.publicView =
      right.application.current.native.publicView := by
    rw [application]
    simp only [sourceSnapshotAssignment, sourceSnapshotState, State.swap_publicView]
  have envelope : PhaseCount.localEnvelope implementation.runtime implementation.leaks owner
      (left.recall owner) (left.observe nativeApplication owner) source =
      PhaseCount.localEnvelope implementation.runtime implementation.leaks owner
        (right.recall owner) (right.observe nativeApplication owner) replacement := by
    unfold PhaseCount.localEnvelope
    rw [resolved]
    change (⟨(owner, _), ⟨left.application.publicView.attempt,
      PhaseCount.maskPacket left.application.publicView
        ⟨.commitment event (owner, .prepared serial), none,
          left.application.current.native.publicView.tokenFor
            (.commitment event (owner, .prepared serial))⟩⟩⟩ :
      Message Player (CommitAttemptPacket (serviceGraph setup .concurrent))) = _
    rw [serials, publicEq, nativePublic]
    rfl
  constructor
  · have sourceBound := member.1
    rw [PhaseCount.rawMenu, ReactiveApplication.ResponseMenu.fromSubmissions_mem] at sourceBound
    have sourceBounds := (implementation.bounds.submissions_mem _ _).mp sourceBound
    rw [PhaseCount.rawMenu, ReactiveApplication.ResponseMenu.fromSubmissions_mem]
    apply (implementation.bounds.submissions_mem _ _).mpr
    exact ⟨⟨sourceBounds.1.1, bounded⟩, trivial⟩
  · right
    refine ⟨replacement, rfl, ?_⟩
    rw [← outputs, ← envelope]
    exact permitted

private def sourceSnapshot_binding_trace
    (target : setup.proposalRecoveryProtocol.History)
    (reference : (nativeApplication).Control)
    (lost : Handle (serviceGraph setup .concurrent) → Option (Raw L))
    (left : (nativeApplication).Execution) (right : (nativeApplication).Control)
    (prior : (nativeProtocol).Trace (some right))
    (application : right.execution.application = sourceSnapshotAssignment setup implementation
      target reference lost left.application)
    (network : left.network = right.execution.network)
    (leftRecall : PhaseCount.CountRecall implementation.runtime implementation.leaks left)
    (owner : Player) (acting : right.actor = some owner)
    (event : (serviceGraph setup .concurrent).EventId) (serial : Nat)
    (first second : Option (Raw L))
    (evidence : EvidenceRequest (serviceGraph setup .concurrent))
    (bounded : implementation.bounds.AllowsOpening second)
    (member : (⟨some ⟨⟨.commitment event (owner, .prepared serial), first⟩, evidence⟩⟩ :
      (nativeApplication).Action) ∈ PhaseCount.onePacketActions implementation.runtime
        implementation.leaks implementation.bounds owner (left.recall owner)
          (left.observe nativeApplication owner)) :
    (nativeProtocol).Trace (some {
      right with
      actor := none
      execution := right.execution.respond nativeApplication owner
        ⟨some ⟨⟨.commitment event (owner, .prepared serial), second⟩, .none⟩⟩ }) := by
  classical
  let replacement : (nativeApplication).Action :=
    ⟨some ⟨⟨.commitment event (owner, .prepared serial), second⟩, .none⟩⟩
  have rightRecall := PhaseCount.countRecall_history implementation.runtime implementation.leaks
    ((nativeMenu).toRawTrace nativeInitial implementation.horizon implementation.scheduler prior)
  have available := sourceSnapshot_binding_available setup implementation target reference lost
    left right.execution application network leftRecall rightRecall owner event serial
      first second evidence bounded member
  rcases right with ⟨remaining, actor, execution⟩
  dsimp only at acting
  subst actor
  exact Classical.choose (HiddenSwap.phase_respond_trace_prefix
    implementation.bounds nativeInitial implementation.horizon implementation.scheduler
    remaining execution owner replacement prior available)

private theorem submittedArchived
    (execution : (nativeApplication).Execution)
    (witness : RecoverySourceWitness setup .concurrent implementation.plan execution.application)
    (archived : witness.checkpoint.ArchivedProposals execution.network.inputs)
    (owner : Player) (material : WitnessedSubmission (serviceGraph setup .concurrent)) :
    (witness.submit implementation.runtime implementation.leaks owner
      material).checkpoint.ArchivedProposals
        (execution.respond nativeApplication owner ⟨some material⟩).network.inputs := by
  obtain ⟨weakNext, weakArchived, fuel, path⟩ := witness.respond_archived_source
    implementation.runtime implementation.leaks execution archived owner
      ⟨some material⟩
  have counts := setup.commitRecovery_same_generation_length path _ _ rfl rfl rfl
  dsimp only [CommitRecoveryState.atPoint] at counts
  have firstRank := witness.checkpoint.saved_position
  have lastRank := weakNext.checkpoint.saved_position
  have firstBound := ProtocolState.remaining_le_instructionCount setup.program
    (witness.checkpoint.residual.lift (ProtocolState.entry
      witness.checkpoint.residual.tail witness.checkpoint.source))
  have lastBound := ProtocolState.remaining_le_instructionCount setup.program
    (weakNext.checkpoint.residual.lift (ProtocolState.entry
      weakNext.checkpoint.residual.tail weakNext.checkpoint.source))
  have unchanged :
      (⟨_, weakNext.checkpoint.trace⟩ : setup.commitRecoveryProtocol.History) =
        ⟨_, witness.checkpoint.trace⟩ := by
    apply path.eq_of_trace_length_eq
    change witness.checkpoint.trace.length = weakNext.checkpoint.trace.length
    change instructionCount setup.program - ProtocolState.remaining setup.program
        (witness.checkpoint.residual.lift (ProtocolState.entry
          witness.checkpoint.residual.tail witness.checkpoint.source)) =
        execution.application.attempt.phase at firstRank
    change instructionCount setup.program - ProtocolState.remaining setup.program
        (weakNext.checkpoint.residual.lift (ProtocolState.entry
          weakNext.checkpoint.residual.tail weakNext.checkpoint.source)) =
        execution.application.attempt.phase at lastRank
    omega
  intro observer survives
  let labels := nativeArchiveLabels setup (PhaseProposal.sourceArchive
    (execution.respond nativeApplication owner ⟨some material⟩).network.inputs)
  have sameArchive := congrArg (fun history : setup.commitRecoveryProtocol.History =>
    setup.proposalRecoveryArchive observer ((sourceModel).infoOf observer
      (setup.proposalRecoveryLiftTrace labels history.trace))) unchanged
  exact sameArchive.symm.trans (weakArchived observer survives)

/-- The actual chronological source witness and its retained proposal archive.
Its checkpoint describes the saved entry used by `canonicalSource`. -/
def checkpointSelection (operational : implementation.Operational)
    {state : (nativeProtocol).State} (trace : (nativeProtocol).Trace state) :
    state.elim PUnit (fun control =>
      {witness : RecoverySourceWitness setup .concurrent implementation.plan
          control.execution.application //
        witness.checkpoint.ArchivedProposals control.execution.network.inputs}) := by
  classical
  let witnessFiber := fun state : ((nativeMenu).protocol nativeInitial implementation.horizon
      implementation.scheduler).State =>
    state.elim PUnit (fun control =>
      {witness : RecoverySourceWitness setup .concurrent implementation.plan
          control.execution.application //
        witness.checkpoint.ArchivedProposals control.execution.network.inputs})
  let chooseStep := fun {before after : (nativeProtocol).State}
      (priorTrace : (nativeProtocol).Trace before)
      (joint : Player → Option (nativeApplication).Action)
      (legal : (nativeProtocol).Legal before joint)
      (realized : after ∈ ((nativeProtocol).step before ⟨joint, legal⟩).support)
      (previous : witnessFiber before) => show witnessFiber after from by
      change after ∈ ((nativeApplication).transition nativeInitial implementation.horizon
        implementation.scheduler before joint).support at realized
      cases before with
      | none =>
        have initialized : ∃ draw : State L setup.context,
            draw ∈ setup.initialLaw.support ∧ after = some
              ⟨implementation.horizon, none, ReactiveApplication.Execution.initial nativeApplication
                (PhaseRuntimeState.initial implementation.plan (encodeInputs draw))⟩ := by
          change after ∈ ((nativeInitial).map fun state => some
            (⟨implementation.horizon, none, ReactiveApplication.Execution.initial nativeApplication
              state⟩ : (nativeApplication).Control)).support at realized
          obtain ⟨physical, physicalSupport, rfl⟩ := PMF.support_map .. ▸ realized
          have initialEq : nativeInitial = setup.initialLaw.map
              (fun draw => PhaseRuntimeState.initial implementation.plan (encodeInputs draw)) :=
            rfl
          rw [initialEq] at physicalSupport
          obtain ⟨draw, drawn, rfl⟩ := PMF.support_map .. ▸ physicalSupport
          exact ⟨draw, drawn, rfl⟩
        let draw := Classical.choose initialized
        have drawn := (Classical.choose_spec initialized).1
        have targetEq := (Classical.choose_spec initialized).2
        rw [targetEq]
        exact ⟨RecoverySourceWitness.initialized setup .concurrent implementation.plan draw drawn,
          RecoverySourceWitness.initialized_archivedProposals setup .concurrent
            implementation.plan draw drawn⟩
      | some control =>
        change {witness : RecoverySourceWitness setup .concurrent implementation.plan
            control.execution.application //
          witness.checkpoint.ArchivedProposals control.execution.network.inputs} at previous
        let witness := previous.val
        have archived := previous.property
        rcases control with ⟨remaining, actor, execution⟩
        cases actor with
        | some owner =>
          have offered := legal.2 owner
          cases selected : joint owner with
          | none =>
            simp [selected, ReactiveApplication.ResponseMenu.protocol,
              ReactiveApplication.actor] at offered
          | some action =>
            change after ∈ ((nativeApplication).transition nativeInitial implementation.horizon
              implementation.scheduler (some ⟨remaining, some owner, execution⟩) joint).support
              at realized
            simp only [ReactiveApplication.transition, selected, Option.getD_some] at realized
            cases (PMF.mem_support_pure_iff _ _).mp realized
            rcases action with ⟨transmission⟩
            cases transmission with
            | none => exact previous
            | some material =>
              -- Keep the concrete SAME checkpoint at a callback. An arbitrary
              -- witness of the weaker existential would lose this equation.
              let next := witness.submit implementation.runtime implementation.leaks owner material
              have nextArchived := submittedArchived setup implementation execution
                witness archived owner material
              exact ⟨next, nextArchived⟩
        | none =>
          cases remaining with
          | zero =>
            change after ∈ (PMF.pure (some ⟨0, none, execution⟩)).support at realized
            cases (PMF.mem_support_pure_iff _ _).mp realized
            exact previous
          | succ remaining =>
            have selected : ∃ command : (nativeApplication).Command,
                command ∈ (implementation.scheduler execution.environmentRecall
                  (execution.observeEnvironment nativeApplication)).support ∧
                ∃ next : (nativeApplication).Execution,
                  next ∈ (execution.environmentStep nativeApplication command).support ∧
                  after = some ⟨remaining, command.actor? nativeApplication, next⟩ := by
              obtain ⟨command, chosen, moved⟩ := Set.mem_iUnion₂.mp
                (PMF.support_bind .. ▸ realized)
              obtain ⟨next, reached, same⟩ := PMF.support_map .. ▸ moved
              exact ⟨command, chosen, next, reached, same.symm⟩
            let command := Classical.choose selected
            let next := Classical.choose (Classical.choose_spec selected).2
            have reached := (Classical.choose_spec (Classical.choose_spec selected).2).1
            have targetEq := (Classical.choose_spec (Classical.choose_spec selected).2).2
            have counted : ((nativeMenu).protocol
                (setup.initialLaw.map fun draw => PhaseRuntimeState.initial implementation.plan
                  (encodeInputs draw)) implementation.horizon implementation.scheduler).Trace
                (some ⟨remaining + 1, none, execution⟩) := by
              exact priorTrace
            let continuation := witness.environment_archived_source implementation.runtime
              implementation.leaks implementation.bounds implementation.plan
              operational.maximalPhases implementation.horizon implementation.scheduler
              ⟨remaining + 1, none, execution⟩ counted archived command next reached
            rw [targetEq]
            exact ⟨Classical.choose continuation, (Classical.choose_spec continuation).1⟩
  let rec cofold {state : (nativeProtocol).State} (trace : (nativeProtocol).Trace state) :
      witnessFiber state := match trace with
    | .start => PUnit.unit
    | .extend priorTrace joint legal realized =>
        chooseStep priorTrace joint legal realized (cofold priorTrace)
  exact cofold trace

/-- The closed source annotation selected by the actual chronological native
prefix. Publication labels are read from that prefix's own original archive. -/
def canonicalSource (operational : implementation.Operational)
    (history : (nativeProtocol).History) : setup.proposalRecoveryProtocol.History :=
  match history with
  | ⟨none, _⟩ => setup.proposalRecoveryProtocol.initHistory
  | ⟨some control, trace⟩ =>
    let witness := (checkpointSelection setup implementation operational trace).val
    ⟨_, setup.proposalRecoveryLiftTrace
      (nativeArchiveLabels setup (PhaseProposal.sourceArchive control.execution.network.inputs))
      witness.checkpoint.trace⟩


open Classical in
/-- Follow the supplied literal binding word whenever its current action is
available. Other instructions use the original causal ordinary profile. -/
def sourceBlockWordStrategy (word : SourceProgram.History Player L) :
    ∀ owner, setup.proposalRecoveryModel.BehavioralPolicy owner :=
  fun owner information =>
    if offered : ∃ choice : setup.proposalRecoveryModel.Choice owner information,
        ∃ action ∈ word owner,
          choice.val = some (ProposalRecoveryMove.ordinary ⟨action, false⟩) then
      PMF.pure (Classical.choose offered)
    else sourceUnflaggedStrategy setup values owner information

open Classical in
/-- Static cut and causal completion of the actual current source block.
The historical focal word is read from this native history. Foreign words
remain fixed; each later focal draw uses its updated source information. -/
def sourceForcedBlockJoint (who : Player) (history : (nativeProtocol).History)
    (event : (serviceGraph setup .concurrent).EventId) (payload : L.Ty)
    (entry : setup.proposalRecoveryProtocol.History)
    (foreignWord : SourceProgram.History Player L) (value : L.Val payload) :
    PMF (setup.proposalRecoveryProtocol.History × setup.proposalRecoveryProtocol.History) :=
  match history.state, entry.state with
  | some control, some current =>
    if binding : (serviceGraph setup .concurrent).outputLayout event = .binding who payload then
      let chosen := decodeEventAction setup.program event
        (cast (congrArg EventField.Action binding.symm) (PublicationResult.success value))
      let prior := phaseCommitRecallWord setup.program .concurrent implementation.runtime
        implementation.leaks control.execution.application.attempt.phase event.val
        control.execution.application.generation (control.execution.recall who)
      let word : SourceProgram.History Player L := fun owner =>
        if owner = who then prior ++ chosen.toList else
          (foreignWord owner).drop
            ((ProtocolState.history setup.program current.point owner).length)
      let profile := sourceBlockWordStrategy setup values word
      let before := event.val -
        (instructionCount setup.program - ProtocolState.remaining setup.program current.point)
      (setup.proposalRecoveryModel.runBehavioralFrom profile before entry).bind fun cut =>
        (setup.proposalRecoveryModel.runBehavioralFrom profile
          (sourceCommitFuel setup cut) cut).map fun completed => (cut, completed)
    else PMF.pure (entry, entry)
  | _, _ => PMF.pure (entry, entry)

/-- The actual emitted binding packets and their addressed typed owner word. -/
def issuedLedger
    {Γ Δ : SourceCtx Player L} {O P : Finset VarId}
    (block : SourceProgram.CommitPrefix Γ O Δ P) (low : Nat)
    (control : (nativeApplication).Control) (high : Nat) (owner : Player)
    (word : DecisionView owner Δ) : Prop :=
  ∀ (named : (serviceGraph setup .concurrent).EventId) (valueType : L.Ty)
    (shape : (serviceGraph setup .concurrent).outputLayout named = .binding owner valueType)
    (candidate : Handle (serviceGraph setup .concurrent))
    (message : Message Player (CommitAttemptPacket (serviceGraph setup .concurrent))),
    message ∈ (nativeApplication).outputs (control.execution.recall owner) →
    message.payload.attempt = control.execution.application.attempt →
    message.payload.packet.call = .commitment named candidate →
    low ≤ named.val ∧ named.val < high →
    ∃ (serial : Nat) (opening : Option (Raw L))
      (evidence : EvidenceRequest (serviceGraph setup .concurrent))
      (entry : (nativeApplication).PlayerEntry),
      candidate = (owner, .prepared serial) ∧
      entry ∈ control.execution.recall owner ∧
      entry.emitted = some message ∧
      entry.action = ⟨some ⟨⟨.commitment named (owner, .prepared serial), opening⟩, evidence⟩⟩ ∧
      entry.beforeView.application.1.candidates (.prepared serial) = .fresh ∧
      (opening.bind fun raw => raw.as? valueType).elim .failure PublicationResult.success =
        (phaseRecoveryBindingData setup .concurrent named owner valueType shape
          (CommitRecoveryMove.lift (block.wordAction owner (named.val - low) word))).1

/-- A fixed actual emitted packet determines its remembered raw response.
This uses authentic envelope uniqueness, not equality of alias menus. -/
private theorem recorded_emission_unique
    {control : (nativeApplication).Control}
    (trace : (nativeProtocol).Trace (some control)) (owner : Player)
    (left right : (nativeApplication).PlayerEntry)
    (leftMember : left ∈ control.execution.recall owner)
    (rightMember : right ∈ control.execution.recall owner)
    (message : Message Player (CommitAttemptPacket (serviceGraph setup .concurrent)))
    (leftEmitted : left.emitted = some message) (rightEmitted : right.emitted = some message) :
    left = right := by
  have order := (nativeApplication).emissionOrder_history implementation.scheduler nativeInitial
    implementation.horizon ((nativeMenu).toRawTrace nativeInitial implementation.horizon
      implementation.scheduler trace)
  have outputUnique : ((nativeApplication).outputs (control.execution.recall owner)).Nodup := by
    apply List.Nodup.of_map Message.id
    rw [order owner]
    exact List.nodup_range.map (fun _ _ equal => (Prod.mk.inj equal).2)
  have unique : ∀ (past : List (nativeApplication).PlayerEntry),
      ((nativeApplication).outputs past).Nodup →
      ∀ first ∈ past, ∀ second ∈ past,
        first.emitted = some message → second.emitted = some message → first = second := by
    intro past
    induction past with
    | nil => simp only [List.not_mem_nil, false_implies, implies_true]
    | cons head rest ih =>
        intro distinct first firstMember second secondMember firstSent secondSent
        rcases List.mem_cons.mp firstMember with firstHead | firstTail
        · subst first
          rcases List.mem_cons.mp secondMember with secondHead | secondTail
          · exact secondHead.symm
          · have missing : message ∉ (nativeApplication).outputs rest := by
              exact (show message ∉ (nativeApplication).outputs rest ∧
                ((nativeApplication).outputs rest).Nodup by
                  simpa only [ReactiveApplication.outputs, List.filterMap_cons, firstSent,
                    List.nodup_cons] using distinct).1
            exact False.elim (missing (List.mem_filterMap.mpr
              ⟨second, secondTail, secondSent⟩))
        · rcases List.mem_cons.mp secondMember with secondHead | secondTail
          · subst second
            have missing : message ∉ (nativeApplication).outputs rest := by
              exact (show message ∉ (nativeApplication).outputs rest ∧
                ((nativeApplication).outputs rest).Nodup by
                  simpa only [ReactiveApplication.outputs, List.filterMap_cons, secondSent,
                    List.nodup_cons] using distinct).1
            exact False.elim (missing (List.mem_filterMap.mpr
              ⟨first, firstTail, firstSent⟩))
          · apply ih _ first firstTail second secondTail firstSent secondSent
            cases sent : head.emitted with
            | none => simpa only [ReactiveApplication.outputs, List.filterMap_cons, sent] using
                distinct
            | some packet =>
                exact (show packet ∉ (nativeApplication).outputs rest ∧
                  ((nativeApplication).outputs rest).Nodup by
                    simpa only [ReactiveApplication.outputs, List.filterMap_cons, sent,
                      List.nodup_cons] using distinct).2
  exact unique _ outputUnique left leftMember right rightMember leftEmitted rightEmitted

/-- On an actual raw history the issued cylinder is precisely the equality
of the addressed result readouts with any one supported retained word. -/
theorem issuedLedger_iff_results
    {Γ Δ : SourceCtx Player L} {O P : Finset VarId}
    (block : SourceProgram.CommitPrefix Γ O Δ P) (low : Nat)
    {control : (nativeApplication).Control}
    (trace : (nativeProtocol).Trace (some control)) (high : Nat) (owner : Player)
    (reference word : DecisionView owner Δ)
    (retained : issuedLedger setup implementation block low control high owner reference) :
    issuedLedger setup implementation block low control high owner word ↔
      ∀ (named : (serviceGraph setup .concurrent).EventId) (payload : L.Ty)
        (shape : (serviceGraph setup .concurrent).outputLayout named = .binding owner payload)
        (candidate : Handle (serviceGraph setup .concurrent))
        (message : Message Player (CommitAttemptPacket (serviceGraph setup .concurrent))),
        message ∈ (nativeApplication).outputs (control.execution.recall owner) →
        message.payload.attempt = control.execution.application.attempt →
        message.payload.packet.call = .commitment named candidate →
        low ≤ named.val ∧ named.val < high →
        (phaseRecoveryBindingData setup .concurrent named owner payload shape
          (CommitRecoveryMove.lift (block.wordAction owner (named.val - low) word))).1 =
        (phaseRecoveryBindingData setup .concurrent named owner payload shape
          (CommitRecoveryMove.lift (block.wordAction owner (named.val - low) reference))).1 := by
  constructor
  · intro belongs named payload shape candidate message emitted attempt packet inside
    obtain ⟨serial, opening, evidence, entry, slot, member, sent, action, fresh, result⟩ :=
      belongs named payload shape candidate message emitted attempt packet inside
    obtain ⟨oldSerial, oldOpening, oldEvidence, oldEntry, oldSlot, oldMember, oldSent,
      oldAction, oldFresh, oldResult⟩ :=
      retained named payload shape candidate message emitted attempt packet inside
    have same := recorded_emission_unique setup implementation trace owner entry oldEntry
      member oldMember message sent oldSent
    have raw := congrArg (fun response : (nativeApplication).Action =>
      response.transmission.bind fun material => material.call.opening)
        (action.symm.trans ((congrArg ReactiveApplication.PlayerEntry.action same).trans oldAction))
    change opening = oldOpening at raw
    rw [← result, ← oldResult, raw]
  · intro results named payload shape candidate message emitted attempt packet inside
    obtain ⟨serial, opening, evidence, entry, slot, member, sent, action, fresh, result⟩ :=
      retained named payload shape candidate message emitted attempt packet inside
    exact ⟨serial, opening, evidence, entry, slot, member, sent, action, fresh,
      result.trans
        (results named payload shape candidate message emitted attempt packet inside).symm⟩

/-- The genuine compiler codec turns the retained emitted cylinder into
literal source-action agreement at the addressed owned rows. -/
theorem issuedLedger_iff_actions
    {Γ Δ : SourceCtx Player L} {O P : Finset VarId}
    (block : SourceProgram.CommitPrefix Γ O Δ P) (suffix : SourceProgram Player L Δ P)
    (embedding : OutputEmbedding (inputLayout setup.context) (outputLayout setup.program)
      (block.prepend suffix)) (low : Nat)
    (rank : ∀ index, (embedding.event index).val = low + index.val)
    (actions : ∀ index action, decodeEventAction setup.program (embedding.event index) action =
      decodeEventAction (block.prepend suffix) index
        (cast (congrArg EventField.Action (embedding.layout_eq index)) action))
    {control : (nativeApplication).Control}
    (trace : (nativeProtocol).Trace (some control)) (owner : Player)
    (reference word : DecisionView owner Δ)
    (retained : issuedLedger setup implementation block low control (low + block.length)
      owner reference) :
    issuedLedger setup implementation block low control (low + block.length) owner word ↔
      ∀ (named : (serviceGraph setup .concurrent).EventId) (payload : L.Ty)
        (_shape : (serviceGraph setup .concurrent).outputLayout named = .binding owner payload)
        (candidate : Handle (serviceGraph setup .concurrent))
        (message : Message Player (CommitAttemptPacket (serviceGraph setup .concurrent))),
        message ∈ (nativeApplication).outputs (control.execution.recall owner) →
        message.payload.attempt = control.execution.application.attempt →
        message.payload.packet.call = .commitment named candidate →
        low ≤ named.val ∧ named.val < low + block.length →
        block.wordAction owner (named.val - low) word =
          block.wordAction owner (named.val - low) reference := by
  rw [issuedLedger_iff_results setup implementation block low trace (low + block.length)
    owner reference word retained]
  constructor
  · intro results named payload shape candidate message emitted attempt packet interval
    have inside : named.val - low < block.length := by omega
    let index : Fin (eventCount (block.prepend suffix)) :=
      ⟨named.val - low, by have count := block.eventCount_prepend suffix; omega⟩
    have namedEq : embedding.event index = named := by
      apply Fin.ext
      rw [rank]
      dsimp only [index]
      omega
    have compared := results named payload shape candidate message emitted attempt packet interval
    have layout : (serviceGraph setup .concurrent).outputLayout (embedding.event index) =
        .binding owner payload := namedEq.symm ▸ shape
    apply (phaseCommitWordAction_eq_iff_result setup .concurrent block suffix embedding actions
      owner index inside payload layout word reference).mpr
    simpa only [namedEq] using compared
  · intro same named payload shape candidate message emitted attempt packet interval
    rw [same named payload shape candidate message emitted attempt packet interval]

/-- At a genuine unsent owned callback the actual emitted cylinder fixes
exactly the earlier owned source actions. Pending foreign rows elsewhere in
the static block do not change this owner's conditional query. -/
theorem issuedLedger_iff_prefix_at_request
    {Γ Δ : SourceCtx Player L} {O P : Finset VarId}
    (block : SourceProgram.CommitPrefix Γ O Δ P) (suffix : SourceProgram Player L Δ P)
    (embedding : OutputEmbedding (inputLayout setup.context) (outputLayout setup.program)
      (block.prepend suffix)) (low : Nat)
    (rank : ∀ index, (embedding.event index).val = low + index.val)
    (actions : ∀ index action, decodeEventAction setup.program (embedding.event index) action =
      decodeEventAction (block.prepend suffix) index
        (cast (congrArg EventField.Action (embedding.layout_eq index)) action))
    {control : (nativeApplication).Control}
    (trace : (nativeProtocol).Trace (some control))
    (phase : RuntimePhase (serviceGraph setup .concurrent))
    (installed : control.execution.application.phases.head? = some phase)
    (phaseLow : phase.low = low) (phaseHigh : phase.high = low + block.length)
    (owner : Player) (selected : (serviceGraph setup .concurrent).EventId)
    (selectedPayload : L.Ty)
    (selectedShape : (serviceGraph setup .concurrent).outputLayout selected =
      .binding owner selectedPayload)
    (request : control.execution.application.SeedRequest owner
      ⟨control.execution.application.attempt, selected⟩)
    (selectedInside : low ≤ selected.val ∧ selected.val < low + block.length)
    (unsent : ∀ message ∈ (nativeApplication).outputs (control.execution.recall owner),
      PhaseCount.event? message.payload ≠ some ⟨control.execution.application.attempt, selected⟩)
    (reference word : DecisionView owner Δ)
    (retained : issuedLedger setup implementation block low control (low + block.length)
      owner reference) :
    issuedLedger setup implementation block low control (low + block.length) owner word ↔
      ∀ position < selected.val - low,
        block.wordAction owner position word = block.wordAction owner position reference := by
  let inputs := setup.initialLaw.map encodeInputs
  have actual : ((nativeMenu).protocol (inputs.map (PhaseRuntimeState.initial implementation.plan))
      implementation.horizon implementation.scheduler).Trace (some control) := by
    have initialEq : inputs.map (PhaseRuntimeState.initial implementation.plan) =
        implementation.initial := by
      simp only [inputs, PMF.map_comp, ReservedConcurrentImplementation.initial, Function.comp_def]
    rw [initialEq]
    exact trace
  have raw := (nativeMenu).toRawTrace _ implementation.horizon implementation.scheduler actual
  have ordered := serviceGraph_revealRelaxedOrdered setup .concurrent
  have address : control.execution.application.attempt.phase = low := by
    simp only [PhaseRuntimeState.attempt, installed, Option.map_some, Option.getD_some, phaseLow]
  rw [issuedLedger_iff_actions setup implementation block suffix embedding low rank actions trace
    owner reference word retained]
  constructor
  · intro agrees position bounded
    have blockBound : position < block.length := by omega
    let index : Fin (eventCount (block.prepend suffix)) :=
      ⟨position, by have count := block.eventCount_prepend suffix; omega⟩
    by_cases owns : eventOwner? (block.prepend suffix) index = some owner
    · obtain ⟨other, payload, _member, layout⟩ :=
        block.binding_before_length suffix index blockBound
      have sameOwner : other = owner := by
        have actor := EventGraph.actor?_of_outputLayout_binding
          (toEventGraph (block.prepend suffix)) layout
        rw [eventOwner?_eq_actor, actor] at owns
        exact Option.some.inj owns
      subst other
      have shape : (serviceGraph setup .concurrent).outputLayout (embedding.event index) =
          .binding owner payload := (embedding.layout_eq index).trans layout
      have interval : low ≤ (embedding.event index).val ∧
          (embedding.event index).val < low + block.length := by
        rw [rank]
        dsimp only [index]
        omega
      have inside : embedding.event index ∈ phase.events := by
        apply (phase.mem_events _).mpr
        simpa only [phaseLow, phaseHigh] using interval
      have earlier : (embedding.event index).val < selected.val := by
        rw [rank]
        dsimp only [index]
        omega
      obtain ⟨candidate, owned, accepted, _read⟩ := phase_ready_earlier_binding_read
        implementation.runtime implementation.leaks implementation.bounds implementation.plan
        inputs implementation.horizon implementation.scheduler actual ordered phase installed
        owner selected selectedPayload selectedShape request.2.2.1 request.2.2.2.2
        (embedding.event index) payload shape inside earlier
      have stamped := phaseLiveBindingStamp_history implementation.runtime implementation.leaks
        implementation.plan inputs implementation.horizon implementation.scheduler raw
      rcases stamped (embedding.event index) candidate accepted with old |
          ⟨message, emitted, _sender, packet, attempt⟩
      · rw [address] at old
        omega
      · rw [owned] at emitted
        have same := agrees (embedding.event index) payload shape candidate message emitted
          attempt packet interval
        have offset : (embedding.event index).val - low = position := by
          rw [rank]
          dsimp only [index]
          omega
        simpa only [offset] using same
    · rw [compiledCommitPrefix_wordAction_none_of_unowned block suffix owner index owns word,
        compiledCommitPrefix_wordAction_none_of_unowned block suffix owner index owns reference]
  · intro agrees named payload shape candidate message emitted attempt packet interval
    obtain ⟨serial, opening, evidence, entry, slot, member, sent, action, _fresh, _result⟩ :=
      retained named payload shape candidate message emitted attempt packet interval
    have stamped := phase_recalled_emission_attempt implementation.runtime implementation.leaks
      _ implementation.horizon implementation.scheduler raw owner entry member message sent
    have before : entry.beforeView.application.2.attempt =
        control.execution.application.attempt := stamped.symm.trans attempt
    have earlier := phase_recorded_binding_rank_lt_of_unsent_request implementation.runtime
      implementation.leaks implementation.bounds implementation.plan inputs implementation.horizon
      ordered implementation.scheduler actual owner entry member
      ⟨⟨.commitment named (owner, .prepared serial), opening⟩, evidence⟩
      (by rw [action]) named (owner, .prepared serial) rfl before selected request unsent
    exact agrees (named.val - low) (by omega)

open Classical in
/-- Conditioning the actual retained owner cylinder at its next unsent
binding gives the chronological source kernel at the updated earlier view.
The complete word retains repeated-owner dependence; it is not a table of
independently sampled answers. -/
theorem issuedLedger_owned_word_conditional
    {Γ Δ Ξ : SourceCtx Player L} {O P Q : Finset VarId}
    {name : VarId} {owner : Player} {payload : L.Ty}
    (fresh : name ∉ Δ.map Prod.fst) (guard : SourceGuard L Δ owner name payload)
    (earlier : SourceProgram.CommitPrefix Γ O Δ P)
    (later : SourceProgram.CommitPrefix ((name, .commitment owner payload) :: Δ)
      (insert name P) Ξ Q) (suffix : SourceProgram Player L Ξ Q)
    (embedding : OutputEmbedding (inputLayout setup.context) (outputLayout setup.program)
      ((earlier.append (.commit name owner fresh guard later)).prepend suffix)) (low : Nat)
    (rank : ∀ index, (embedding.event index).val = low + index.val)
    (actions : ∀ index action, decodeEventAction setup.program (embedding.event index) action =
      decodeEventAction ((earlier.append (.commit name owner fresh guard later)).prepend suffix)
        index (cast (congrArg EventField.Action (embedding.layout_eq index)) action))
    {control : (nativeApplication).Control} (trace : (nativeProtocol).Trace (some control))
    (phase : RuntimePhase (serviceGraph setup .concurrent))
    (installed : control.execution.application.phases.head? = some phase)
    (phaseLow : phase.low = low)
    (phaseHigh : phase.high = low + (earlier.append (.commit name owner fresh guard later)).length)
    (selected : (serviceGraph setup .concurrent).EventId)
    (shape : (serviceGraph setup .concurrent).outputLayout selected = .binding owner payload)
    (request : control.execution.application.SeedRequest owner
      ⟨control.execution.application.attempt, selected⟩)
    (selectedInside : low ≤ selected.val ∧
      selected.val < low + (earlier.append (.commit name owner fresh guard later)).length)
    (selectedRank : selected.val - low = earlier.length)
    (unsent : ∀ message ∈ (nativeApplication).outputs (control.execution.recall owner),
      PhaseCount.event? message.payload ≠ some ⟨control.execution.application.attempt, selected⟩)
    (profile : SourceProgram.BehavioralProfile
      (earlier.prepend (.commit name owner fresh guard (later.prepend suffix))))
    (entry : SourceProgram.Config Player L Γ) (reference : DecisionView owner Ξ) :
    let current := earlier.tailProfile (.commit name owner fresh guard (later.prepend suffix))
      profile
    let before := earlier.prefixLaw (.commit name owner fresh guard (later.prepend suffix))
      profile entry
    let complete := before.bind fun config =>
      ((SourceProgram.CommitPrefix.commit name owner fresh guard later).prefixLaw suffix
        current config)
    let prior := complete.map (SourceProgram.Config.view owner)
    let observed := (later.entryView owner reference).back true
    reference ∈ prior.support →
    issuedLedger setup implementation (earlier.append (.commit name owner fresh guard later)) low
      control (low + (earlier.append (.commit name owner fresh guard later)).length)
      owner reference →
    (fiberPosterior prior (fun word => decide (issuedLedger setup implementation
      (earlier.append (.commit name owner fresh guard later)) low control
      (low + (earlier.append (.commit name owner fresh guard later)).length) owner word)) true).map
      ((earlier.append (.commit name owner fresh guard later)).wordAction owner earlier.length) =
      (SourceProgram.commitKernel current observed).map (fun result =>
        some (OwnAction.commit owner name payload result)) := by
  intro current before complete prior observed supported retained
  let beforeView := fun word : DecisionView owner Ξ => (later.entryView owner word).back true
  have possible : observed ∈ (before.map (SourceProgram.Config.view owner)).support := by
    have projected : observed ∈ (prior.map beforeView).support :=
      (PMF.mem_support_map_iff _ _ _).mpr ⟨reference, supported, rfl⟩
    have projection : prior.map beforeView = before.map (SourceProgram.Config.view owner) := by
      simpa only [prior, complete, before, current, beforeView,
        SourceProgram.CommitPrefix.prepend, SourceProgram.CommitPrefix.entryView, decide_true] using
        earlier.prefixLaw_split_entryView
          (.commit name owner fresh guard later) suffix profile entry owner
    exact projection ▸ projected
  have same : fiberPosterior prior (fun word => decide (issuedLedger setup implementation
      (earlier.append (.commit name owner fresh guard later)) low control
      (low + (earlier.append (.commit name owner fresh guard later)).length) owner word)) true =
      fiberPosterior prior beforeView observed := by
    apply fiberPosterior_eq_of_support_fiber
    intro word drawn
    rw [decide_eq_true_eq,
      issuedLedger_iff_prefix_at_request setup implementation
        (earlier.append (.commit name owner fresh guard later)) suffix embedding low rank actions
        trace phase installed phaseLow phaseHigh owner selected payload shape request
        selectedInside unsent reference word retained, selectedRank]
    have compared := earlier.prefixLaw_split_entryView_iff_wordActions
      (.commit name owner fresh guard later) suffix profile entry owner word reference
      drawn supported
    simpa only [SourceProgram.CommitPrefix.entryView, decide_true, beforeView, observed] using
      compared.symm
  rw [same]
  exact earlier.prefixLaw_owned_word_conditional fresh guard later suffix profile entry
    observed possible

open Classical in
/-- The actual foreign issued rectangle conditions only foreign owner words.
Each retained owner marginal keeps its original chronological dependence.
The unused focal ordinary marginal is left unconditioned. -/
theorem issuedLedger_foreign_product
    {Γ Δ : SourceCtx Player L} {O P : Finset VarId}
    (block : SourceProgram.CommitPrefix Γ O Δ P) (suffix : SourceProgram Player L Δ P)
    (profile : SourceProgram.BehavioralProfile (block.prepend suffix))
    (entry : SourceProgram.Config Player L Γ) (low high : Nat)
    (control : (nativeApplication).Control) (focal : Player)
    (present : ∃ final ∈ (block.prefixLaw suffix profile entry).support,
      ∀ owner, owner ≠ focal →
        issuedLedger setup implementation block low control high owner (final.view owner)) :
    fiberPosterior
      ((block.prefixLaw suffix profile entry).map (fun final owner => final.view owner))
      (fun views => decide (∀ owner, owner ≠ focal →
        issuedLedger setup implementation block low control high owner (views owner))) true =
      independentProduct (fun owner => fiberPosterior
        ((block.prefixLaw suffix profile entry).map (SourceProgram.Config.view owner))
        (fun word => decide (owner ≠ focal →
          issuedLedger setup implementation block low control high owner word)) true) := by
  let laws := fun owner =>
    (block.prefixLaw suffix profile entry).map (SourceProgram.Config.view owner)
  let restriction := fun owner => {word | owner ≠ focal →
    issuedLedger setup implementation block low control high owner word}
  have coordinate (owner : Player) : ∃ word ∈ restriction owner, word ∈ (laws owner).support := by
    obtain ⟨final, supported, retained⟩ := present
    exact ⟨final.view owner, retained owner,
      (PMF.mem_support_map_iff _ _ _).mpr ⟨final, supported, rfl⟩⟩
  have rectangle : ∃ views ∈ Set.pi Set.univ restriction,
      views ∈ (independentProduct laws).support := by
    obtain ⟨final, supported, retained⟩ := present
    refine ⟨fun owner => final.view owner, fun owner _ => retained owner, ?_⟩
    rw [← block.prefixLaw_views_product suffix profile entry]
    exact (PMF.mem_support_map_iff _ _ _).mpr ⟨final, supported, rfl⟩
  have marginal (owner : Player) :
      fiberPosterior (laws owner) (fun word => decide (owner ≠ focal →
        issuedLedger setup implementation block low control high owner word)) true =
        (laws owner).filter (restriction owner) (coordinate owner) := by
    have meets : ∃ word ∈ {word | decide (owner ≠ focal →
        issuedLedger setup implementation block low control high owner word) = true},
        word ∈ (laws owner).support := by
      simpa only [Set.mem_ofPred_eq, decide_eq_true_eq, restriction] using coordinate owner
    simpa only [decide_eq_true_eq] using fiberPosterior_eq_filter (laws owner)
      (fun word => decide (owner ≠ focal →
        issuedLedger setup implementation block low control high owner word)) meets
  have total : fiberPosterior (independentProduct laws)
      (fun views => decide (∀ owner, owner ≠ focal →
        issuedLedger setup implementation block low control high owner (views owner))) true =
        (independentProduct laws).filter (Set.pi Set.univ restriction) rectangle := by
    have meets : ∃ views ∈ {views | decide (∀ owner, owner ≠ focal →
        issuedLedger setup implementation block low control high owner (views owner)) = true},
        views ∈ (independentProduct laws).support := by
      obtain ⟨views, belongs, supported⟩ := rectangle
      exact ⟨views, by
        simp only [Set.mem_ofPred_eq, decide_eq_true_eq]
        exact fun owner => belongs owner (Set.mem_univ owner), supported⟩
    have same : {views | decide (∀ owner, owner ≠ focal →
        issuedLedger setup implementation block low control high owner (views owner)) = true} =
        Set.pi Set.univ restriction := by
      ext views
      simp only [Set.mem_ofPred_eq, decide_eq_true_eq, Set.mem_pi, Set.mem_univ,
        forall_true_left, restriction]
    rw [fiberPosterior_eq_filter _ _ meets]
    simp only [same]
  rw [block.prefixLaw_views_product suffix profile entry]
  change fiberPosterior (independentProduct laws) _ true = independentProduct
    (fun owner => fiberPosterior (laws owner) _ true)
  rw [total]
  simp_rw [marginal]
  exact filter_independentProduct laws restriction coordinate

open Classical in
/-- Ordinary complete foreign owner words with the original issued cylinder.
The source entry is pulled from the target itself, without a posterior-support gate. -/
def ordinaryForeignJoint (operational : implementation.Operational) (who : Player)
    (history : (nativeProtocol).History) (target : setup.proposalRecoveryProtocol.History) :
    PMF (SourceProgram.History Player L × Bool) := by
  cases history with
  | mk state trace =>
    cases state with
    | none => exact PMF.pure (fun _ => [], true)
    | some control =>
      let checkpoint := (checkpointSelection setup implementation operational trace).val.checkpoint
      let pulled := target.state.bind fun current =>
        residualEntry? checkpoint.residual.tail checkpoint.residual.lift current.point
      cases _entryEq : pulled with
      | none => exact PMF.pure (fun _ => [], false)
      | some entry =>
        by_cases committing : ProtocolState.atCommit checkpoint.residual.tail
            (ProtocolState.entry checkpoint.residual.tail entry) = true
        · let block := SourceProgram.commitPhase checkpoint.residual.tail
          let embedding := cast (congrArg (fun program => OutputEmbedding
            (inputLayout setup.context) (outputLayout setup.program) program)
              block.reconstruct.symm) checkpoint.embedding
          let wholeViews := fun owner
              (view : ProtocolView owner (block.block.prepend block.suffix)) =>
            checkpoint.views.view owner
              (cast (congrArg (ProtocolView owner) block.reconstruct) view)
          let profile := ordinaryBlockProfile setup .concurrent implementation.plan values
            block.block block.suffix
            embedding wholeViews
            (control.execution.application.entry.excluded,
              control.execution.application.generation, control.execution.application.attempt.phase)
            control.execution.application.publicView
            (PhaseProposal.sourceArchive control.execution.network.inputs)
          exact (block.block.prefixLaw block.suffix profile entry).map fun final =>
            ((fun owner => if owner = who then [] else final.history owner),
              decide (∀ owner, owner ≠ who →
                issuedLedger setup implementation block.block
                  control.execution.application.attempt.phase control
                  (control.execution.application.attempt.phase + block.block.length)
                  owner (final.view owner)))
        · exact PMF.pure (fun _ => [], true)

/-- Original whole-tape posterior at the actual observed environment prefix. -/
def prefixTapeLaw (history : (nativeProtocol).History) :
    PMF (ReservedEpoch.Tape Player implementation.tapeLength) :=
  match history.state with
  | none => implementation.prior
  | some control =>
    ((nativeApplication).schedulerMixture implementation.prior
      (ReservedEpoch.family implementation.runtime implementation.leaks
        (ReservedEpoch.packetCapacity implementation.runtime))).posterior
      control.execution.environmentRecall

open Classical in
/-- The actual unnormalized native reach, original tape, source posterior and
issued-word joint. Zero cylinders contribute zero before any normalization. -/
def annotatedPrefixWeight (operational : implementation.Operational)
    (sourceProfile : ∀ owner, setup.proposalRecoveryModel.BehavioralPolicy owner)
    (nativeProfile : ∀ owner,
      ((nativeMenu).information nativeInitial implementation.horizon
        implementation.scheduler).BehavioralPolicy owner)
    (who : Player) (history : (nativeProtocol).History)
    (tape : ReservedEpoch.Tape Player implementation.tapeLength)
    (target : setup.proposalRecoveryProtocol.History) (word : SourceProgram.History Player L) :
    ℝ≥0∞ :=
  let joint := ordinaryForeignJoint setup values implementation operational who history target
  ((nativeMenu).information nativeInitial implementation.horizon
      implementation.scheduler).historyReachWeight
       nativeProfile history * prefixTapeLaw setup implementation history tape *
    if (∀ owner, owner ≠ who →
        ¬ EventGraphRuntime.PhaseProposal.GeneratedUnusableBindingHistory implementation.runtime
          implementation.leaks implementation.bounds nativeInitial implementation.horizon
          implementation.scheduler owner history) ∧
        history.state.elim True (fun control =>
          who ∉ control.execution.application.current.excluded) then
      setup.proposalRecoveryClosedLaw sourceProfile who
        (canonicalSource setup implementation operational history) target *
        if (joint.map Prod.snd) true = 0 then 0 else
          ((fiberPosterior joint Prod.snd true).map Prod.fst) word
    else 0

open Classical in
private theorem prescribed_source_history_positive
    (scale sourceBad : Set.Icc (0 : ℝ) 1)
    (scalePositive : 0 < scale.val) (scaleBelow : scale.val < 1)
    (badPositive : 0 < sourceBad.val) (badBelow : sourceBad.val < 1)
    (fullValues : ∀ owner key, FullSupport (values owner key))
    (sourceProfile : ∀ owner, setup.proposalRecoveryModel.BehavioralPolicy owner)
    (prescribed : ∀ owner (history : setup.proposalRecoveryProtocol.History),
      ¬ setup.proposalRecoveryProtocol.terminal history.state →
      sourceProfile owner (setup.proposalRecoveryModel.infoOf owner history.trace) =
        setup.proposalRecoveryNormalizedTrembledProfile
          scale.val scale.property.1 scale.property.2
          sourceBad.val sourceBad.property.1 sourceBad.property.2
          scale.val scale.property.1 scale.property.2 values owner
            (setup.proposalRecoveryModel.infoOf owner history.trace))
    (history : setup.proposalRecoveryProtocol.History) :
    0 < setup.proposalRecoveryModel.historyReachWeight sourceProfile history := by
  classical
  let ordinary := setup.proposalRecoveryNormalizedTrembledProfile
    scale.val scale.property.1 scale.property.2
    sourceBad.val sourceBad.property.1 sourceBad.property.2
    scale.val scale.property.1 scale.property.2 values
  have full : ∀ owner (site : setup.proposalRecoveryModel.InformationSite owner)
      (choice : setup.proposalRecoveryModel.Choice owner site.1),
      choice ∈ (ordinary owner site.1).support := by
    intro owner site choice
    change choice ∈ (PMF.map (setup.proposalRecoveryComponentChoice owner site.1).symm
      (setup.proposalRecoveryComponentTrembledLaw owner
        (setup.proposalRecoveryQuery owner site.1)
        scale.val scale.property.1 scale.property.2
        sourceBad.val sourceBad.property.1 sourceBad.property.2
        scale.val scale.property.1 scale.property.2
        (values owner (setup.proposalRecoveryQuery owner site.1)))).support
    refine (PMF.mem_support_map_iff _ _ _).mpr
      ⟨setup.proposalRecoveryComponentChoice owner site.1 choice, ?_,
        (setup.proposalRecoveryComponentChoice owner site.1).symm_apply_apply choice⟩
    exact setup.proposalRecoveryComponentTrembledLaw_fullSupport owner _
      scale.val scalePositive scaleBelow sourceBad.val badPositive badBelow
      scale.val scalePositive scaleBelow _ (fullValues owner _) _
  have positive := setup.proposalRecoveryModel.historyReachWeight_pos_of_fullSupport
    ordinary full history
  have same := setup.proposalRecoveryModel.runBehavioralFrom_congr
    (first := sourceProfile) (second := ordinary) history.trace.length
    setup.proposalRecoveryProtocol.initHistory
    (fun reached _ running owner => prescribed owner reached running)
  change 0 < setup.proposalRecoveryModel.runBehavioralFrom sourceProfile history.trace.length
    setup.proposalRecoveryProtocol.initHistory history
  rw [same]
  exact positive

/-- A positive actual annotation has a genuine closed source tag and an
issued-word cylinder. Reach support excludes the posterior's fallback branch. -/
theorem annotatedPrefixWeight_support (operational : implementation.Operational)
    (sourceProfile : ∀ owner, setup.proposalRecoveryModel.BehavioralPolicy owner)
    (nativeProfile : ∀ owner,
      ((nativeMenu).information nativeInitial implementation.horizon
        implementation.scheduler).BehavioralPolicy owner)
    (who : Player) (history : (nativeProtocol).History)
    (tape : ReservedEpoch.Tape Player implementation.tapeLength)
    (target : setup.proposalRecoveryProtocol.History) (word : SourceProgram.History Player L)
    (canonicalSupported : setup.proposalRecoveryModel.historyReachWeight sourceProfile
      (canonicalSource setup implementation operational history) ≠ 0)
    (positive : annotatedPrefixWeight setup values implementation operational sourceProfile
      nativeProfile who history tape target word ≠ 0) :
    setup.proposalRecoveryClosedKey who target = setup.proposalRecoveryClosedKey who
        (canonicalSource setup implementation operational history) ∧
      setup.proposalRecoveryModel.historyReachWeight sourceProfile target ≠ 0 ∧
      (word, true) ∈ (ordinaryForeignJoint setup values implementation operational
        who history target).support := by
  classical
  let canonical := canonicalSource setup implementation operational history
  let joint := ordinaryForeignJoint setup values implementation operational who history target
  have mass : setup.proposalRecoveryClosedMass sourceProfile who canonical ≠ 0 := by
    apply (PMF.mem_support_iff _ _).mp
    apply (PMF.mem_support_map_iff _ _ _).mpr
    refine ⟨canonical, ?_, rfl⟩
    exact (PMF.mem_support_iff _ _).mpr canonicalSupported
  unfold annotatedPrefixWeight at positive
  dsimp only at positive
  have factors := (mul_ne_zero_iff.mp positive).2
  split at factors
  · have tagged := (mul_ne_zero_iff.mp factors).1
    have issued := (mul_ne_zero_iff.mp factors).2
    have label := (setup.proposalRecoveryClosedLaw_support sourceProfile who canonical target
      mass).mp ((PMF.mem_support_iff _ _).mpr tagged)
    refine ⟨label.1, label.2, ?_⟩
    change (if (joint.map Prod.snd) true = 0 then 0 else
      ((fiberPosterior joint Prod.snd true).map Prod.fst) word) ≠ 0 at issued
    by_cases empty : (joint.map Prod.snd) true = 0
    · rw [ite_eq_left empty] at issued
      exact False.elim (issued rfl)
    · rw [ite_eq_right empty] at issued
      obtain ⟨pair, member, first⟩ := (PMF.mem_support_map_iff _ _ _).mp
        ((PMF.mem_support_iff _ _).mpr issued)
      rw [fiberPosterior_support _ _ _ ((PMF.mem_support_iff _ _).mpr empty)] at member
      have pairEq : pair = (word, true) := Prod.ext first member.1
      exact pairEq ▸ member.2
  · simp only [ne_eq, not_true_eq_false] at factors

open Classical in
/-- The literal public, focal and service projection at a raw prefix. -/
def mechanicalProjection (who : Player) (state : (nativeProtocol).State) :=
  state.map fun control =>
    (control.remaining, control.actor, control.execution.application.publicView,
      control.execution.network.publicView, control.execution.receipts,
      control.execution.observe nativeApplication who,
      (fun owner serial => decide
        (control.execution.application.current.native.candidates.lookup
          (owner, .prepared serial) = .fresh)),
      control.execution.environmentRecall, control.execution.recall who)

/-- Every raw step remains represented, including silent callbacks. -/
def mechanicalWord (who : Player) : ∀ {state : (nativeProtocol).State},
    (nativeProtocol).Trace state → List (Set.range (mechanicalProjection setup implementation who))
  | _, .start => [⟨mechanicalProjection setup implementation who none, none, rfl⟩]
  | target, .extend prior _ _ _ => mechanicalWord who prior ++
      [⟨mechanicalProjection setup implementation who target, target, rfl⟩]

private theorem mechanicalWord_last (who : Player) {state : (nativeProtocol).State}
    (trace : (nativeProtocol).Trace state) :
    (mechanicalWord setup implementation who trace).getLast? =
      some ⟨mechanicalProjection setup implementation who state, state, rfl⟩ := by
  cases trace with
  | start => rfl
  | extend prior joint legal realized =>
      rw [mechanicalWord, List.getLast?_append_of_ne_nil _ (by simp),
        List.getLast?_singleton]

private theorem mechanicalWord_ownPlay (who : Player)
    (left right : (nativeApplication).Control)
    (first : (nativeProtocol).Trace (some left))
    (second : (nativeProtocol).Trace (some right))
    (same : mechanicalWord setup implementation who first =
      mechanicalWord setup implementation who second) :
    ((nativeMenu).information nativeInitial implementation.horizon
      implementation.scheduler).ownPlay who first =
      ((nativeMenu).information nativeInitial implementation.horizon
        implementation.scheduler).ownPlay who second := by
  have last := congrArg List.getLast? same
  rw [mechanicalWord_last, mechanicalWord_last] at last
  have projected := congrArg Subtype.val (Option.some.inj last)
  change some (_, _, _, _, _, _, _, _, left.execution.recall who) =
    some (_, _, _, _, _, _, _, _, right.execution.recall who) at projected
  have recalled : left.execution.recall who = right.execution.recall who :=
    congrArg (fun row => row.2.2.2.2.2.2.2.2) (Option.some.inj projected)
  rw [HiddenSwap.phase_trace_ownPlay implementation.bounds nativeInitial implementation.horizon
      implementation.scheduler left first who,
    HiddenSwap.phase_trace_ownPlay implementation.bounds nativeInitial implementation.horizon
      implementation.scheduler right second who, recalled]

/-- A retained mechanical prefix together with the original whole tape. -/
def MechanicalIndex (who : Player) :=
  Set.range (fun history : (nativeProtocol).History =>
    mechanicalWord setup implementation who history.trace) ×
      ReservedEpoch.Tape Player implementation.tapeLength

open Classical in
/-- The accepting word after one genuinely available proper current SEND.
Its representative is immaterial on ready support by binding-alias invariance. -/
def bindingAdmissionBit (who : Player) (event : (serviceGraph setup .concurrent).EventId)
    (history : (nativeProtocol).History)
    (tape : ReservedEpoch.Tape Player implementation.tapeLength) : Bool :=
  match history.state with
  | none => false
  | some control =>
    if offered : ∃ material : WitnessedSubmission (serviceGraph setup .concurrent),
        (⟨some material⟩ : (nativeApplication).Action) ∈
          (nativeMenu).actions who (control.execution.recall who)
            (control.execution.observe nativeApplication who) ∧
        ∃ (payload : L.Ty) (value : L.Val payload) (serial : Nat),
          (serviceGraph setup .concurrent).outputLayout event = .binding who payload ∧
          material.call.packet = .commitment event (who, .prepared serial) ∧
          PhaseProposal.bindingPreparation material = some ⟨payload, value⟩ then
      let sent := control.execution.respond nativeApplication who
        ⟨some (Classical.choose offered)⟩
      decide (∃ phase ∈ control.execution.application.phases.head?,
        phase.kind = .commitment ∧ ∀ named ∈ phase.events, ∀ owner,
          (serviceGraph setup .concurrent).actor? named = some owner →
          owner ∉ control.execution.application.entry.excluded →
          ReservedEpoch.ownedAcceptanceWord implementation.runtime implementation.leaks
            tape sent owner named)
    else false

open Classical in
/-- Push the one original annotated joint through the actual h-dependent
static cut and causal block. Qualification stays inside the native-history sum. -/
def annotatedForcedBlockWeight (operational : implementation.Operational)
    (sourceProfile : ∀ owner, setup.proposalRecoveryModel.BehavioralPolicy owner)
    (nativeProfile : ∀ owner,
      ((nativeMenu).information nativeInitial implementation.horizon
        implementation.scheduler).BehavioralPolicy owner)
    (who : Player)
    (site : ((nativeMenu).information nativeInitial implementation.horizon
      implementation.scheduler).InformationSite who)
    (index : MechanicalIndex setup implementation who)
    (event : (serviceGraph setup .concurrent).EventId) (payload : L.Ty) (value : L.Val payload)
    (cut completed : setup.proposalRecoveryProtocol.History) : ℝ≥0∞ :=
  ∑' history : ((nativeMenu).information nativeInitial implementation.horizon
      implementation.scheduler).InformationHistory who site.1,
    if mechanicalWord setup implementation who history.val.trace = index.1.val then
      ∑' entry : setup.proposalRecoveryProtocol.History,
        ∑' word : SourceProgram.History Player L,
          annotatedPrefixWeight setup values implementation operational sourceProfile nativeProfile
              who history.val index.2 entry word *
            (if bindingAdmissionBit setup implementation who event history.val index.2
              then 1 else 0) *
            sourceForcedBlockJoint setup values implementation who history.val event payload
              entry word value (cut, completed)
    else 0

open Classical in
private theorem annotatedForcedBlockWeight_anchor
    (operational : implementation.Operational)
    (sourceProfile : ∀ owner, setup.proposalRecoveryModel.BehavioralPolicy owner)
    (nativeProfile : ∀ owner,
      ((nativeMenu).information nativeInitial implementation.horizon
        implementation.scheduler).BehavioralPolicy owner)
    (who : Player)
    (site : ((nativeMenu).information nativeInitial implementation.horizon
      implementation.scheduler).InformationSite who)
    (index : MechanicalIndex setup implementation who)
    (event : (serviceGraph setup .concurrent).EventId) (payload : L.Ty) (value : L.Val payload)
    (cut completed : setup.proposalRecoveryProtocol.History)
    (positive : annotatedForcedBlockWeight setup values implementation operational sourceProfile
      nativeProfile who site index event payload value cut completed ≠ 0) :
    ∃ history : ((nativeMenu).information nativeInitial implementation.horizon
        implementation.scheduler).InformationHistory who site.1,
      mechanicalWord setup implementation who history.val.trace = index.1.val ∧
      ((nativeMenu).information nativeInitial implementation.horizon
        implementation.scheduler).historyReachWeight nativeProfile history.val ≠ 0 ∧
      prefixTapeLaw setup implementation history.val index.2 ≠ 0 ∧
      (∀ owner, owner ≠ who →
        ¬ EventGraphRuntime.PhaseProposal.GeneratedUnusableBindingHistory implementation.runtime
          implementation.leaks implementation.bounds nativeInitial implementation.horizon
          implementation.scheduler owner history.val) ∧
      history.val.state.elim True (fun control =>
        who ∉ control.execution.application.current.excluded) ∧
      bindingAdmissionBit setup implementation who event history.val index.2 = true := by
  classical
  by_contra absent
  apply positive
  unfold annotatedForcedBlockWeight
  apply ENNReal.tsum_eq_zero.mpr
  intro history
  by_cases same : mechanicalWord setup implementation who history.val.trace = index.1.val
  · rw [ite_eq_left same]
    apply ENNReal.tsum_eq_zero.mpr
    intro entry
    apply ENNReal.tsum_eq_zero.mpr
    intro word
    by_contra nonzero
    have first := (mul_ne_zero_iff.mp nonzero).1
    have prefixWeight := (mul_ne_zero_iff.mp first).1
    have gate := (mul_ne_zero_iff.mp first).2
    have admitted : bindingAdmissionBit setup implementation who event history.val index.2 =
        true := by
      by_contra failed
      exact gate (ite_eq_right failed)
    unfold annotatedPrefixWeight at prefixWeight
    dsimp only at prefixWeight
    have initial := (mul_ne_zero_iff.mp prefixWeight).1
    have kept := (mul_ne_zero_iff.mp prefixWeight).2
    split at kept
    · rename_i good
      exact absent ⟨history, same, (mul_ne_zero_iff.mp initial).1,
        (mul_ne_zero_iff.mp initial).2, good.1, good.2, admitted⟩
    · exact kept rfl
  · exact ite_eq_right same

open Classical in
/-- Qualification mass before selecting a proper value or a utility. -/
def qualifiedPrefixMass
    (nativeProfile : ∀ owner,
      ((nativeMenu).information nativeInitial implementation.horizon
        implementation.scheduler).BehavioralPolicy owner)
    (who : Player)
    (site : ((nativeMenu).information nativeInitial implementation.horizon
      implementation.scheduler).InformationSite who)
    (event : (serviceGraph setup .concurrent).EventId) : ℝ≥0∞ :=
  ∑' history : ((nativeMenu).information nativeInitial implementation.horizon
      implementation.scheduler).InformationHistory who site.1,
    ((nativeMenu).information nativeInitial implementation.horizon
      implementation.scheduler).historyReachWeight
         nativeProfile history.val *
      if (∀ owner, owner ≠ who →
          ¬ EventGraphRuntime.PhaseProposal.GeneratedUnusableBindingHistory implementation.runtime
            implementation.leaks implementation.bounds nativeInitial implementation.horizon
            implementation.scheduler owner history.val) ∧
          history.val.state.elim True (fun control =>
            who ∉ control.execution.application.current.excluded) then
        ∑' tape : ReservedEpoch.Tape Player implementation.tapeLength,
          prefixTapeLaw setup implementation history.val tape *
            if bindingAdmissionBit setup implementation who event history.val tape then 1 else 0
      else 0

omit [Fintype Player] in
private theorem pulled_entry_history
    (control : (nativeApplication).Control)
    (checkpoint : RecoverySourceCheckpoint setup .concurrent control.execution.application)
    (point : ProtocolState setup.program)
    (entry : SourceProgram.Config Player L checkpoint.residual.context)
    (pulled : residualEntry? checkpoint.residual.tail checkpoint.residual.lift point = some entry) :
    ProtocolState.history setup.program point = entry.history := by
  have pointEq := (residualEntry?_eq_some_iff checkpoint.origin point entry).mp pulled
  rw [← pointEq, checkpoint.history, ProtocolState.history_entry]

omit [Fintype Player] in
private theorem ordinaryBlockWord_drop
    {Γ Δ : SourceCtx Player L} {O P : Finset VarId}
    (block : SourceProgram.CommitPrefix Γ O Δ P) (suffix : SourceProgram Player L Δ P)
    (profile : SourceProgram.BehavioralProfile (block.prepend suffix))
    (entry : SourceProgram.Config Player L Γ) (owner : Player)
    (finished : SourceProgram.Config Player L Δ)
    (supported : finished ∈ (block.prefixLaw suffix profile entry).support) :
    (finished.history owner).drop (entry.history owner).length =
      (List.range block.length).filterMap (fun index =>
        block.wordAction owner index (finished.view owner)) := by
  rw [block.prefixLaw_wordAction_history suffix profile entry owner finished supported]
  simp


private def mechanicalForeignPolicy (rates : PhaseProposalRates) (owner : Player) :
    (nativeApplication).Policy :=
  phasePolicyDispatch setup .concurrent implementation.runtime implementation.leaks
    (fun owner event payload binding =>
      PhaseCount.phaseOpeningPolicy implementation.runtime implementation.leaks
        implementation.bounds owner event payload binding
        (fun _ _ => mix rates.waiting.val rates.waiting.property.1 rates.waiting.property.2
          (PMF.pure false) (PMF.pure true)))
    (fun owner event payload _binding past view =>
      mix rates.waiting.val rates.waiting.property.1 rates.waiting.property.2
        (PMF.pure ⟨none⟩)
        (PhaseCount.bindingResultEncoder implementation.runtime implementation.leaks
          implementation.bounds owner event payload (fun _ _ => PMF.pure .failure)
          rates.slots.val rates.slots.property.1 rates.slots.property.2 past view)) owner

/-- Packet and fresh-slot atom, with no ordinary value or alias probability. -/
private def foreignMechanicalAtom (rates : PhaseProposalRates)
    (execution : (nativeApplication).Execution) (owner : Player)
    (response : (nativeApplication).Action) : ℝ≥0∞ :=
  let packet := fun action : (nativeApplication).Action =>
    action.transmission.map fun material =>
      (PhaseCount.localEnvelope implementation.runtime implementation.leaks owner
        (execution.recall owner) (execution.observe nativeApplication owner) material).payload
  let atom := ((mechanicalForeignPolicy setup implementation rates owner
    (execution.recall owner) (execution.observe nativeApplication owner)).map packet)
      (packet response)
  atom * match response.transmission with
    | none => 1
    | some material => match material.call.packet with
      | .commitment .. => ENNReal.ofReal (1 - rates.badPreparation.val)
      | _ => 1


private theorem binding_encoder_class_atom (rates : PhaseProposalRates)
    (owner : Player) (event : (serviceGraph setup .concurrent).EventId) (payload : L.Ty)
    (binding : (serviceGraph setup .concurrent).outputLayout event = .binding owner payload)
    (past : List (nativeApplication).PlayerEntry) (view : (nativeApplication).PlayerView)
    (results : List (nativeApplication).PlayerEntry → (nativeApplication).PlayerView →
      PMF (PublicationResult (L.Val payload)))
    (value : L.Val payload) (packet : Option (CommitAttemptPacket (serviceGraph setup .concurrent)))
    (sent : packet ≠ none) :
    let packetOf := fun response : (nativeApplication).Action => response.transmission.map
      (fun material => (PhaseCount.localEnvelope implementation.runtime implementation.leaks
        owner past view material).payload)
    let observe := fun response : (nativeApplication).Action =>
      (response.transmission.bind PhaseProposal.bindingPreparation, packetOf response)
    let encode := fun law => mix rates.waiting.val rates.waiting.property.1
      rates.waiting.property.2 (PMF.pure ⟨none⟩)
      (PhaseCount.bindingResultEncoder implementation.runtime implementation.leaks
        implementation.bounds owner event payload law rates.slots.val rates.slots.property.1
          rates.slots.property.2 past view)
    ((encode results).map observe) (some (⟨payload, value⟩ : Raw L), packet) =
      ((encode (fun _ _ => PMF.pure .failure)).map packetOf) packet *
        results past view (.success value) := by
  classical
  intro packetOf observe encode
  let failure := fun (_ : List (nativeApplication).PlayerEntry)
    (_ : (nativeApplication).PlayerView) => (PMF.pure .failure : PMF (PublicationResult
      (L.Val payload)))
  have silence : ((PMF.pure (⟨none⟩ : (nativeApplication).Action)).map observe)
      (some (⟨payload, value⟩ : Raw L), packet) =
      ((PMF.pure (⟨none⟩ : (nativeApplication).Action)).map packetOf) packet *
        results past view (.success value) := by
    simp [PMF.pure_map, observe, packetOf, sent]
  have fixed (serial : Nat) :
      (((results past view).map (phaseBindingResponse implementation.runtime implementation.leaks
        owner event payload · serial)).map observe) (some (⟨payload, value⟩ : Raw L), packet) =
      (((failure past view).map (phaseBindingResponse implementation.runtime implementation.leaks
        owner event payload · serial)).map packetOf) packet *
          results past view (.success value) := by
    let encoded := phaseBindingResponse implementation.runtime implementation.leaks
      owner event payload
    have output : setup.eventGraph.outputLayout event = .binding owner payload := binding
    have observed (result : PublicationResult (L.Val payload)) :
        observe (encoded result serial) =
          ((match result with
            | .failure => none | .success drawn => some (⟨payload, drawn⟩ : Raw L)),
            packetOf (encoded .failure serial)) := by
      apply Prod.ext
      · cases result <;>
          simp [observe, encoded, phaseBindingResponse, PhaseProposal.bindingPreparation, output]
      · exact PhaseCount.phaseBindingResponse_localPacket implementation.runtime
          implementation.leaks owner event payload past view result .failure serial
    have tested (result : PublicationResult (L.Val payload)) :
        (some (⟨payload, value⟩ : Raw L), packet) = observe (encoded result serial) ↔
          result = .success value ∧ packet = packetOf (encoded .failure serial) := by
      rw [observed]
      cases result <;> simp [Raw.mk.injEq, eq_comm]
    rw [PMF.map_comp, PMF.map_apply]
    simp only [Function.comp_apply]
    dsimp only [encoded] at tested
    rw [tsum_eq_single (.success value)]
    · rw [PMF.map_comp]
      simp only [tested, failure, PMF.pure_map, PMF.pure_apply, true_and, Function.comp_apply]
      split_ifs <;> simp
    · intro other different
      simp only [tested, different, false_and, ite_false]
  have slots :
      ((PhaseCount.phaseBindingSlotPolicy implementation.runtime implementation.leaks
        implementation.bounds owner event payload results past view).map observe)
          (some (⟨payload, value⟩ : Raw L), packet) =
      ((PhaseCount.phaseBindingSlotPolicy implementation.runtime implementation.leaks
        implementation.bounds owner event payload failure past view).map packetOf) packet *
          results past view (.success value) := by
    unfold PhaseCount.phaseBindingSlotPolicy
    split
    · rw [PMF.map_bind, PMF.map_bind, PMF.bind_apply, PMF.bind_apply, ← ENNReal.tsum_mul_right]
      apply tsum_congr
      intro serial
      rw [fixed]
      exact (mul_assoc _ _ _).symm
    · exact silence
  have canonical :
      ((PhaseCount.phaseBindingPolicy implementation.runtime implementation.leaks
        implementation.bounds owner event payload results past view).map observe)
          (some (⟨payload, value⟩ : Raw L), packet) =
      ((PhaseCount.phaseBindingPolicy implementation.runtime implementation.leaks
        implementation.bounds owner event payload failure past view).map packetOf) packet *
          results past view (.success value) := by
    unfold PhaseCount.phaseBindingPolicy
    split
    · exact silence
    · split
      · exact fixed _
      · exact silence
  dsimp only [encode]
  rw [mix_map, mix_map, mix_apply, mix_apply, silence]
  unfold PhaseCount.bindingResultEncoder
  rw [mix_map, mix_map, mix_apply, mix_apply, slots, canonical]
  ring

/-- At the actual counted callback a proper foreign binding separates its
mechanical packet, ordinary typed draw and input-specific raw alias atom. -/
theorem foreign_binding_response_atom
    (operational : implementation.Operational)
    (fullValues : ∀ owner key, FullSupport (values owner key))
    (rates : PhaseProposalRates) (waitPositive : 0 < rates.waiting.val)
    (waitBelow : rates.waiting.val < 1) (slotPositive : 0 < rates.slots.val)
    (badPositive : 0 < rates.badPreparation.val) (badBelow : rates.badPreparation.val < 1)
    (remaining : Nat) (owner : Player) (execution : (nativeApplication).Execution)
    (trace : (nativeProtocol).Trace (some ⟨remaining, some owner, execution⟩))
    (event : (serviceGraph setup .concurrent).EventId) (payload : L.Ty)
    (binding : (serviceGraph setup .concurrent).outputLayout event = .binding owner payload)
    (request : execution.application.SeedRequest owner ⟨execution.application.attempt, event⟩)
    (key : setup.ProposalRecoveryComponent owner)
    (queried : phaseProposalQuery? setup .concurrent implementation.runtime implementation.leaks
      implementation.plan owner event (execution.recall owner)
        (execution.observe nativeApplication owner) = some key)
    (response : PhaseProposal.Response implementation.runtime implementation.leaks
      implementation.bounds
      owner (execution.recall owner) (execution.observe nativeApplication owner))
    (material : WitnessedSubmission (serviceGraph setup .concurrent))
    (transmitted : response.val.transmission = some material)
    (value : L.Val payload)
    (prepared : PhaseProposal.bindingPreparation material = some (⟨payload, value⟩ : Raw L))
    (serial : Nat) (packet : material.call.packet = .commitment event (owner, .prepared serial)) :
    phaseProposalReferenceResponses setup .concurrent implementation.runtime implementation.leaks
        implementation.bounds implementation.plan values rates owner (execution.recall owner)
          (execution.observe nativeApplication owner) response =
      foreignMechanicalAtom setup implementation rates execution owner response.val *
        ((values owner key).map (fun choice => phaseRecoveryDomainValue setup .concurrent event
          owner payload binding choice.val.val)) value *
        (PMF.splitKernel
          (PhaseProposal.projectResponse implementation.runtime implementation.leaks
            implementation.bounds owner (execution.recall owner)
              (execution.observe nativeApplication owner))
          (PhaseProposal.canonicalResponse implementation.runtime implementation.leaks
            implementation.bounds owner (execution.recall owner)
              (execution.observe nativeApplication owner))
          (PhaseProposal.project_canonicalResponse implementation.runtime implementation.leaks
            implementation.bounds owner (execution.recall owner)
              (execution.observe nativeApplication owner))
          rates.aliases.val rates.aliases.property.1 rates.aliases.property.2
          (PhaseProposal.projectResponse implementation.runtime implementation.leaks
            implementation.bounds owner (execution.recall owner)
              (execution.observe nativeApplication owner) response)) response := by
  classical
  let past := execution.recall owner
  let view := execution.observe nativeApplication owner
  let packetOf := fun action : (nativeApplication).Action => action.transmission.map
    (fun material => (PhaseCount.localEnvelope implementation.runtime implementation.leaks
      owner past view material).payload)
  let observe := fun action : (nativeApplication).Action =>
    (action.transmission.bind PhaseProposal.bindingPreparation, packetOf action)
  let results := phaseProposalBindingResults setup .concurrent implementation.runtime
    implementation.leaks implementation.plan values rates owner event payload binding
  let encoded := fun law => mix rates.waiting.val rates.waiting.property.1
    rates.waiting.property.2 (PMF.pure (⟨none⟩ : (nativeApplication).Action))
    (PhaseCount.bindingResultEncoder implementation.runtime implementation.leaks
      implementation.bounds owner event payload law rates.slots.val rates.slots.property.1
        rates.slots.property.2 past view)
  have initial : (setup.initialLaw.map encodeInputs).map
      (PhaseRuntimeState.initial implementation.plan) = nativeInitial := by
    rw [PMF.map_comp]
    rfl
  obtain ⟨_draw, native⟩ := phaseNativeInvariant_history implementation.runtime implementation.leaks
    implementation.plan (setup.initialLaw.map encodeInputs) implementation.horizon
      implementation.scheduler (control := ⟨remaining, some owner, execution⟩) (by
        rw [initial]
        exact (nativeMenu).toRawTrace nativeInitial implementation.horizon implementation.scheduler
          trace)
  have base : phaseProposalBasePolicy setup .concurrent implementation.runtime implementation.leaks
      implementation.bounds implementation.plan values rates owner past view = encoded results := by
    unfold phaseProposalBasePolicy
    rw [phasePolicyDispatch_binding setup .concurrent implementation.runtime implementation.leaks
      _ _ execution native owner event payload binding request]
  have mechanical : mechanicalForeignPolicy setup implementation rates owner past view =
      encoded (fun _ _ => PMF.pure .failure) := by
    unfold mechanicalForeignPolicy
    rw [phasePolicyDispatch_binding setup .concurrent implementation.runtime implementation.leaks
      _ _ execution native owner event payload binding request]
  have classLaw :
      (phaseProposalBaseClasses setup .concurrent implementation.runtime implementation.leaks
        implementation.bounds implementation.plan values rates owner past view).map Subtype.val =
      (phaseProposalBasePolicy setup .concurrent implementation.runtime implementation.leaks
        implementation.bounds implementation.plan values rates owner past view).map observe := by
    rw [phaseProposalBaseClasses, PMF.map_comp,
      ← phaseProposalBaseResponses_map_val setup .concurrent implementation.runtime
        implementation.leaks implementation.bounds implementation.plan values rates owner past view,
      PMF.map_comp]
    rfl
  have classAtom : phaseProposalBaseClasses setup .concurrent implementation.runtime
      implementation.leaks implementation.bounds implementation.plan values rates owner past view
        (PhaseProposal.projectResponse implementation.runtime implementation.leaks
          implementation.bounds owner past view response) =
      ((encoded (fun _ _ => PMF.pure .failure)).map packetOf) (packetOf response.val) *
        results past view (.success value) := by
    rw [← pmf_map_apply_of_injective _ Subtype.val_injective
      (PhaseProposal.projectResponse implementation.runtime implementation.leaks
        implementation.bounds owner past view response), classLaw, base]
    change ((encoded results).map observe) (observe response.val) = _
    have selected : observe response.val =
        (some (⟨payload, value⟩ : Raw L), packetOf response.val) := by
      simp only [observe, transmitted, Option.bind_some, prepared]
    rw [selected]
    exact binding_encoder_class_atom setup implementation rates owner event payload binding
      past view
      results value (packetOf response.val) (by simp [packetOf, transmitted])
  have proper : results past view (.success value) =
      ENNReal.ofReal (1 - rates.badPreparation.val) *
        ((values owner key).map (fun choice => phaseRecoveryDomainValue setup .concurrent event
          owner payload binding choice.val.val)) value := by
    dsimp only [results, phaseProposalBindingResults]
    rw [queried, mix_apply]
    have mapped : ((values owner key).map (fun choice => PublicationResult.success
        (phaseRecoveryDomainValue setup .concurrent event owner payload binding choice.val.val)))
          (.success value) =
        ((values owner key).map (fun choice => phaseRecoveryDomainValue setup .concurrent event
          owner payload binding choice.val.val)) value := by
      have composed := congrArg (fun law : PMF (PublicationResult (L.Val payload)) =>
        law (.success value)) (PMF.map_comp
          (fun choice : setup.CommitRecoveryValueChoice owner key.1 =>
            phaseRecoveryDomainValue setup .concurrent event owner payload binding choice.val.val)
          (values owner key) PublicationResult.success)
      exact composed.symm.trans (pmf_map_apply_of_injective _
        (fun _ _ same => PublicationResult.success.inj same) value)
    rw [mapped]
    simp
  unfold phaseProposalReferenceResponses PhaseProposal.splitResponseLaw
  rw [phaseProposalReferenceClasses_eq_of_counted setup .concurrent implementation.runtime
    implementation.leaks implementation.bounds implementation.plan operational.completePending
    operational.outputValues operational.maximalPhases values fullValues rates waitPositive
    waitBelow
    slotPositive badPositive badBelow implementation.horizon implementation.scheduler remaining
    owner
    execution trace]
  rw [bind_apply_of_unique_branch _ _ response
    (PhaseProposal.projectResponse implementation.runtime implementation.leaks implementation.bounds
      owner past view response) (fun chosen _ supported =>
        (PMF.splitKernel_supported _ _ _ _ _ _ chosen response supported).symm)]
  rw [classAtom, proper]
  change _ = (((mechanicalForeignPolicy setup implementation rates owner past view).map packetOf)
    (packetOf response.val) *
      (match response.val.transmission with
      | none => 1
      | some material => match material.call.packet with
        | .commitment .. => ENNReal.ofReal (1 - rates.badPreparation.val)
        | _ => 1)) * _ * _
  rw [mechanical, transmitted]
  dsimp only
  rw [packet]
  ring

private def mechanicalStepAtom (rates : PhaseProposalRates) (who : Player)
    (tape : ReservedEpoch.Tape Player implementation.tapeLength)
    (before after : (nativeProtocol).State)
      (joint : Player → Option (nativeApplication).Action) :
    ℝ≥0∞ :=
  match before with
  | none => 1
  | some control => match control.actor with
    | some owner =>
      if owner = who then 1 else
        match joint owner with
        | none => 0
        | some response => foreignMechanicalAtom setup implementation rates
            control.execution owner response
    | none =>
      if control.remaining = 0 then 1 else
        match after with
        | none => 0
        | some later => match later.execution.environmentRecall.getLast? with
          | none => 0
          | some recorded =>
            ReservedEpoch.family implementation.runtime implementation.leaks
              (ReservedEpoch.packetCapacity implementation.runtime) tape
              control.execution.environmentRecall
              (control.execution.observeEnvironment nativeApplication) recorded.command

/-- Product of original fixed-tape command atoms and foreign mechanical atoms.
Initializer and Nature probabilities remain in the source transition mass. -/
private def mechanicalPathAtom (rates : PhaseProposalRates) (who : Player)
    (tape : ReservedEpoch.Tape Player implementation.tapeLength) :
    ∀ {state : (nativeProtocol).State}, (nativeProtocol).Trace state → ℝ≥0∞
  | _, .start => 1
  | after, @Trace.extend _ _ before _ prior joint _ _ =>
      mechanicalPathAtom rates who tape prior *
        mechanicalStepAtom setup implementation rates who tape before after joint

open Classical in
/-- Explicit original tape, focal own-play, and mechanical atom product.
A supported qualified mechanical anchor selects the product, never a mass quotient. -/
def mechanicalCoefficient (rates : PhaseProposalRates)
    (nativeProfile : ∀ owner,
      ((nativeMenu).information nativeInitial implementation.horizon
        implementation.scheduler).BehavioralPolicy owner)
    (who : Player)
    (site : ((nativeMenu).information nativeInitial implementation.horizon
      implementation.scheduler).InformationSite who)
    (event : (serviceGraph setup .concurrent).EventId)
    (index : MechanicalIndex setup implementation who) : ℝ≥0∞ :=
  if present : ∃ history : ((nativeMenu).information nativeInitial implementation.horizon
        implementation.scheduler).InformationHistory who site.1,
      mechanicalWord setup implementation who history.val.trace = index.1.val ∧
      ((nativeMenu).information nativeInitial implementation.horizon
      implementation.scheduler).historyReachWeight
         nativeProfile history.val ≠ 0 ∧
      prefixTapeLaw setup implementation history.val index.2 ≠ 0 ∧
      (∀ owner, owner ≠ who →
        ¬ EventGraphRuntime.PhaseProposal.GeneratedUnusableBindingHistory implementation.runtime
          implementation.leaks implementation.bounds nativeInitial implementation.horizon
          implementation.scheduler owner history.val) ∧
      history.val.state.elim True (fun control =>
        who ∉ control.execution.application.current.excluded) ∧
      bindingAdmissionBit setup implementation who event history.val index.2 = true then
    let history := (Classical.choose present).val
    implementation.prior index.2 *
      ENNReal.ofReal (((nativeMenu).information nativeInitial implementation.horizon
        implementation.scheduler).ownPlayReachProbability (nativeProfile who)
          (((nativeMenu).information nativeInitial implementation.horizon
            implementation.scheduler).ownPlay who history.trace)) *
      mechanicalPathAtom setup implementation rates who index.2 history.trace
  else 0

end NativeCheckpoint
end Vegas.PhaseProposalQualifiedBinding
