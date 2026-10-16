/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.CompiledCommitStepRecall
import Vegas.Game.CompiledCommitHead
import Vegas.Source.CommitRecoveryBlockPath

/-! # Complete source signal recall along actual completed commitment blocks -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

/-- Actual completed binding blocks extend genuine initialized source traces
with the same entire observed signal recall whenever their physical public and
focal observations and their prior remembered source observations agree.
The real original missing scan and the final retry or exhaustion are retained. -/
theorem decoded_commit_block_source_traces
    (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode) (who : Player)
    {Γ Δ : SourceCtx Player L} {O P : Finset VarId}
    (block : SourceProgram.CommitPrefix Γ O Δ P) :
    ∀ (suffix : SourceProgram Player L Δ P)
      (embedding : OutputEmbedding (inputLayout setup.context) (outputLayout setup.program)
        (block.prepend suffix))
      (lift : ProtocolState (block.prepend suffix) → ProtocolState setup.program)
      (_origin : ProtocolSuffix setup.program (block.prepend suffix) lift)
      (_ranks : ∀ point, ProtocolState.remaining setup.program (lift point) =
        ProtocolState.remaining (block.prepend suffix) point)
      (_actors : ∀ point, ProtocolState.actor setup.program (lift point) =
        ProtocolState.actor (block.prepend suffix) point)
      (_menus : ∀ point player, ProtocolView.recoveryAvailable player setup.program
        (ProtocolState.observe player setup.program (lift point)) =
        ProtocolView.recoveryAvailable player (block.prepend suffix)
          (ProtocolState.observe player (block.prepend suffix) point))
      (_steps : ∀ point owners joint, ProtocolState.recoveryStep setup.program (lift point) owners
          joint =
        (ProtocolState.recoveryStep (block.prepend suffix) point owners joint).map
          (fun result => (lift result.1, result.2)))
      (first second : EventGraphRuntime.State ((toEventGraph setup.program).withMode mode))
      (_firstValid : first.BindingInvariant) (_secondValid : second.BindingInvariant)
      (firstEntry secondEntry : SourceProgram.Config Player L Γ)
      (left right : CommitRecoveryState setup.program)
      (_entry : firstEntry.view who = secondEntry.view who)
      (_publicView : first.publicView = second.publicView)
      (_observed : ((toEventGraph setup.program).withMode mode).playerObserve who first.config =
        ((toEventGraph setup.program).withMode mode).playerObserve who second.config)
      (_firstCompleted : ∀ index : Fin (eventCount (block.prepend suffix)),
        index.val < block.length → embedding.event index ∈ first.config.cut.completed)
      (_secondCompleted : ∀ index : Fin (eventCount (block.prepend suffix)),
        index.val < block.length → embedding.event index ∈ second.config.cut.completed)
      (_saved : ProtocolState.observe who setup.program left.saved =
        ProtocolState.observe who setup.program right.saved)
      (_excluded : left.excluded = right.excluded)
      (_entryExcluded : left.entryExcluded = right.entryExcluded)
      (_generation : left.generation = right.generation)
      (_firstAtEntry : left.point = lift (ProtocolState.entry (block.prepend suffix) firstEntry))
      (_secondAtEntry : right.point = lift (ProtocolState.entry (block.prepend suffix) secondEntry))
      (_firstCommitting : ProtocolState.atCommit setup.program left.saved = true)
      (_secondCommitting : ProtocolState.atCommit setup.program right.saved = true)
      (_firstEndpoint : ProtocolState.commitEnd setup.program left.saved ≤ instructionCount suffix)
      (_secondEndpoint : ProtocolState.commitEnd setup.program right.saved ≤
        instructionCount suffix)
      (_positive : 0 < block.length)
      (firstTrace : setup.commitRecoveryProtocol.Trace (some left))
      (secondTrace : setup.commitRecoveryProtocol.Trace (some right))
      (_prior : setup.commitRecoverySignals.infoOf who firstTrace =
        setup.commitRecoverySignals.infoOf who secondTrace),
      let leftDecoded := decodeCommitAttempt setup.program mode block suffix embedding first
        firstEntry left.excluded
      let rightDecoded := decodeCommitAttempt setup.program mode block suffix embedding second
        secondEntry right.excluded
      let leftRaw := left.install
        (lift (block.liftPoint suffix (ProtocolState.entry suffix leftDecoded.1)), leftDecoded.2.1)
        (fun _ member => leftDecoded.2.2.excluded_subset member)
      let rightRaw := right.install
        (lift (block.liftPoint suffix (ProtocolState.entry suffix rightDecoded.1)),
          rightDecoded.2.1)
        (fun _ member => rightDecoded.2.2.excluded_subset member)
      ∃ (leftTrace : setup.commitRecoveryProtocol.Trace (some leftRaw.close))
        (rightTrace : setup.commitRecoveryProtocol.Trace (some rightRaw.close)),
        ∃ (leftFuel rightFuel : Nat),
        setup.commitRecoveryProtocol.ReachesWithin leftFuel
          ⟨some left, firstTrace⟩ ⟨some leftRaw.close, leftTrace⟩ ∧
        setup.commitRecoveryProtocol.ReachesWithin rightFuel
          ⟨some right, secondTrace⟩ ⟨some rightRaw.close, rightTrace⟩ ∧
        setup.commitRecoverySignals.infoOf who leftTrace =
          setup.commitRecoverySignals.infoOf who rightTrace := by
  induction block with
  | nil =>
      intro suffix embedding lift origin ranks actors menus steps first second firstValid
        secondValid
        firstEntry secondEntry left right entry publicView observed firstCompleted secondCompleted
        saved excluded entryExcluded generation firstAtEntry secondAtEntry firstCommitting
        secondCommitting firstEndpoint secondEndpoint positive
      exact (Nat.not_lt_zero _ positive).elim
  | @commit Γ O Δ P name owner payload fresh guard rest ih =>
      intro suffix embedding lift origin ranks actors menus steps first second firstValid
        secondValid
        firstEntry secondEntry left right entry publicView observed firstCompleted secondCompleted
        saved excluded entryExcluded generation firstAtEntry secondAtEntry firstCommitting
        secondCommitting firstEndpoint secondEndpoint positive firstTrace secondTrace prior
      let tail := rest.prepend suffix
      let head : SourceProgram.CommitPrefix Γ O ((name, .commitment owner payload) :: Γ)
        (insert name O) := .commit name owner fresh guard .nil
      let firstHead := decodeCommitAttempt setup.program mode head tail embedding first firstEntry
        left.excluded
      let secondHead := decodeCommitAttempt setup.program mode head tail embedding second
        secondEntry right.excluded
      let leftHead := left.install
        (lift (Sum.inr (ProtocolState.entry tail firstHead.1)), firstHead.2.1)
        (fun _ member => firstHead.2.2.excluded_subset member)
      let rightHead := right.install
        (lift (Sum.inr (ProtocolState.entry tail secondHead.1)), secondHead.2.1)
        (fun _ member => secondHead.2.2.excluded_subset member)
      have firstHeadCompleted := firstCompleted ⟨0, Nat.zero_lt_succ _⟩ (Nat.zero_lt_succ _)
      have secondHeadCompleted := secondCompleted ⟨0, Nat.zero_lt_succ _⟩ (Nat.zero_lt_succ _)
      obtain ⟨firstNextTrace, secondNextTrace, firstFuel, secondFuel, firstPath, secondPath,
        nextSignals⟩ :=
        decoded_commit_source_traces setup mode
        fresh guard tail embedding lift origin first second firstValid secondValid firstEntry
        secondEntry left right who entry publicView observed firstHeadCompleted secondHeadCompleted
        saved excluded entryExcluded generation firstAtEntry secondAtEntry ranks actors menus steps
        firstTrace secondTrace prior
      by_cases remaining : 0 < rest.length
      · have firstUnfinished : ProtocolState.commitEnd setup.program leftHead.saved <
            ProtocolState.remaining setup.program leftHead.point := by
          change ProtocolState.commitEnd setup.program left.saved <
            ProtocolState.remaining setup.program (lift (Sum.inr (ProtocolState.entry tail _)))
          rw [ranks]
          simp only [SourceProgram.CommitPrefix.prepend, ProtocolState.remaining, Sum.elim_inr,
            ProtocolState.remaining_entry, tail,
            SourceProgram.CommitPrefix.instructionCount_prepend]
          omega
        have secondUnfinished : ProtocolState.commitEnd setup.program rightHead.saved <
            ProtocolState.remaining setup.program rightHead.point := by
          change ProtocolState.commitEnd setup.program right.saved <
            ProtocolState.remaining setup.program (lift (Sum.inr (ProtocolState.entry tail _)))
          rw [ranks]
          simp only [SourceProgram.CommitPrefix.prepend, ProtocolState.remaining, Sum.elim_inr,
            ProtocolState.remaining_entry, tail,
            SourceProgram.CommitPrefix.instructionCount_prepend]
          omega
        have firstNoClose := leftHead.close_eq_self_of_remaining_gt firstCommitting firstUnfinished
        have secondNoClose := rightHead.close_eq_self_of_remaining_gt secondCommitting
          secondUnfinished
        have currentSignals := congrArg Prod.fst nextSignals
        rw [setup.commitRecoverySignals_current, setup.commitRecoverySignals_current]
          at currentSignals
        have nextPrivate := congrArg Prod.fst currentSignals
        change some (ProtocolState.observe who setup.program leftHead.close.point) =
          some (ProtocolState.observe who setup.program rightHead.close.point) at nextPrivate
        have currentViews := Option.some.inj nextPrivate
        rw [firstNoClose, secondNoClose] at currentViews
        have localViews := origin.observe_reflect who _ _ currentViews
        have tailViews := Sum.inr.inj localViews
        change ProtocolState.observe who tail (ProtocolState.entry tail firstHead.1) =
          ProtocolState.observe who tail (ProtocolState.entry tail secondHead.1) at tailViews
        have nextEntry : firstHead.1.view who = secondHead.1.view who := by
          have views := congrArg (ProtocolView.entryView who tail) tailViews
          simpa only [ProtocolView.entryView_observe_entry] using views
        have nextExcluded := congrArg (fun item => item.2.1) currentSignals
        change leftHead.close.excluded = rightHead.close.excluded at nextExcluded
        let tailEmbedding := embedding.tail tail
          (by simp only [SourceProgram.CommitPrefix.prepend, eventCount, tail]) (fun _ => rfl)
        have firstRemaining : ∀ index : Fin (eventCount tail), index.val < rest.length →
            tailEmbedding.event index ∈ first.config.cut.completed := by
          intro index earlier
          apply firstCompleted (Fin.succ index)
          change index.val + 1 < rest.length + 1
          omega
        have secondRemaining : ∀ index : Fin (eventCount tail), index.val < rest.length →
            tailEmbedding.event index ∈ second.config.cut.completed := by
          intro index earlier
          apply secondCompleted (Fin.succ index)
          change index.val + 1 < rest.length + 1
          omega
        have continuation := ih suffix tailEmbedding (fun point => lift (Sum.inr point))
          (.commitTail fresh guard tail origin)
          (fun point => ranks (Sum.inr point)) (fun point => actors (Sum.inr point))
          (fun point player => menus (Sum.inr point) player)
          (fun point owners joint => by
            simpa only [SourceProgram.CommitPrefix.prepend, ProtocolState.recoveryStep,
              Sum.elim_inr, PMF.map_comp,
              Function.comp_def] using steps (Sum.inr point) owners joint)
          first second firstValid secondValid firstHead.1 secondHead.1 leftHead.close
          rightHead.close
          nextEntry publicView observed firstRemaining secondRemaining
          (by rw [firstNoClose, secondNoClose]; exact saved) nextExcluded
          (by rw [firstNoClose, secondNoClose]; exact entryExcluded)
          (by rw [firstNoClose, secondNoClose]; exact generation)
          (by rw [firstNoClose]; rfl) (by rw [secondNoClose]; rfl)
          (by rw [firstNoClose]; exact firstCommitting)
          (by rw [secondNoClose]; exact secondCommitting)
          (by rw [firstNoClose]; exact firstEndpoint)
          (by rw [secondNoClose]; exact secondEndpoint)
          remaining firstNextTrace secondNextTrace nextSignals
        generalize firstStartEq :
          (⟨some leftHead.close, firstNextTrace⟩ : setup.commitRecoveryProtocol.History) =
            firstStart at continuation
        generalize secondStartEq :
          (⟨some rightHead.close, secondNextTrace⟩ : setup.commitRecoveryProtocol.History) =
            secondStart at continuation
        rw [firstNoClose, secondNoClose] at continuation
        rw [firstStartEq] at firstPath
        rw [secondStartEq] at secondPath
        let firstTail := decodeCommitAttempt setup.program mode rest suffix tailEmbedding first
          firstHead.1 firstHead.2.1
        let secondTail := decodeCommitAttempt setup.program mode rest suffix tailEmbedding second
          secondHead.1 secondHead.2.1
        let firstWhole := decodeCommitAttempt setup.program mode
          (.commit name owner fresh guard rest) suffix embedding first firstEntry left.excluded
        let secondWhole := decodeCommitAttempt setup.program mode
          (.commit name owner fresh guard rest) suffix embedding second secondEntry right.excluded
        let firstPartial : { result : ProtocolState setup.program × Finset Player //
            left.excluded ⊆ result.2 } :=
          ⟨(lift (Sum.inr (rest.liftPoint suffix (ProtocolState.entry suffix firstTail.1))),
            firstTail.2.1), fun _ member => firstTail.2.2.excluded_subset
              (firstHead.2.2.excluded_subset member)⟩
        let secondPartial : { result : ProtocolState setup.program × Finset Player //
            right.excluded ⊆ result.2 } :=
          ⟨(lift (Sum.inr (rest.liftPoint suffix (ProtocolState.entry suffix secondTail.1))),
            secondTail.2.1), fun _ member => secondTail.2.2.excluded_subset
              (secondHead.2.2.excluded_subset member)⟩
        let firstComplete : { result : ProtocolState setup.program × Finset Player //
            left.excluded ⊆ result.2 } :=
          ⟨(lift (Sum.inr (rest.liftPoint suffix (ProtocolState.entry suffix firstWhole.1))),
            firstWhole.2.1), fun _ member => firstWhole.2.2.excluded_subset member⟩
        let secondComplete : { result : ProtocolState setup.program × Finset Player //
            right.excluded ⊆ result.2 } :=
          ⟨(lift (Sum.inr (rest.liftPoint suffix (ProtocolState.entry suffix secondWhole.1))),
            secondWhole.2.1), fun _ member => secondWhole.2.2.excluded_subset member⟩
        let leftFinal := left.install firstPartial.1 firstPartial.2
        let rightFinal := right.install secondPartial.1 secondPartial.2
        let leftComplete := left.install firstComplete.1 firstComplete.2
        let rightComplete := right.install secondComplete.1 secondComplete.2
        change ∃ (leftTrace : setup.commitRecoveryProtocol.Trace (some leftFinal.close))
          (rightTrace : setup.commitRecoveryProtocol.Trace (some rightFinal.close)),
          ∃ (leftFuel rightFuel : Nat),
          setup.commitRecoveryProtocol.ReachesWithin leftFuel
            firstStart ⟨some leftFinal.close, leftTrace⟩ ∧
          setup.commitRecoveryProtocol.ReachesWithin rightFuel
            secondStart ⟨some rightFinal.close, rightTrace⟩ ∧
          setup.commitRecoverySignals.infoOf who leftTrace =
            setup.commitRecoverySignals.infoOf who rightTrace at continuation
        have firstDecoded := decodeCommitAttempt_commit_tail setup.program mode fresh guard rest
          suffix embedding first firstEntry left.excluded
        have secondDecoded := decodeCommitAttempt_commit_tail setup.program mode fresh guard rest
          suffix embedding second secondEntry right.excluded
        have firstTagged : firstPartial = firstComplete := Subtype.ext
          (Prod.ext (congrArg (fun config => lift
            (Sum.inr (rest.liftPoint suffix (ProtocolState.entry suffix config)))) firstDecoded.1)
              firstDecoded.2)
        have secondTagged : secondPartial = secondComplete := Subtype.ext
          (Prod.ext (congrArg (fun config => lift
            (Sum.inr (rest.liftPoint suffix (ProtocolState.entry suffix config)))) secondDecoded.1)
              secondDecoded.2)
        have firstFinish : leftFinal.close = leftComplete.close :=
          congrArg (fun value : { result : ProtocolState setup.program × Finset Player //
            left.excluded ⊆ result.2 } => (left.install value.1 value.2).close) firstTagged
        have secondFinish : rightFinal.close = rightComplete.close :=
          congrArg (fun value : { result : ProtocolState setup.program × Finset Player //
            right.excluded ⊆ result.2 } => (right.install value.1 value.2).close) secondTagged
        rw [firstFinish, secondFinish] at continuation
        obtain ⟨leftTrace, rightTrace, leftFuel, rightFuel, leftPath, rightPath, same⟩ :=
          continuation
        exact ⟨leftTrace, rightTrace, firstFuel + leftFuel, secondFuel + rightFuel,
          firstPath.trans leftPath, secondPath.trans rightPath, same⟩
      · cases rest with
        | nil =>
            exact ⟨firstNextTrace, secondNextTrace, firstFuel, secondFuel, firstPath,
              secondPath, nextSignals⟩
        | commit => simp only [SourceProgram.CommitPrefix.length] at remaining; omega

end Vegas
