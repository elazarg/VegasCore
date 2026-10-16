/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.CommitPrefixWord
import Vegas.Game.RecoveryBindingWordPrediction
import Vegas.Game.PhaseBindingResponseFactor
import Vegas.Pending.PhaseBindingWordKernel
import Vegas.Source.CommitRecoveryLift

/-! # Complete-word realization of actual canonical and slot callbacks

The word is conditioned on the actual owned prefix. Its next addressed result
passes through the physical encoder, independently of the original omission
draw. This identifies a whole raw callback law, without a raw-noise tier.
-/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Protocol
  GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]

omit [DecidableEq Player] [Fintype Player] [IExpr.ResultTypes L] in
private theorem lift_underlying_of_nonmissing
    (choice : Option (CommitRecoveryMove Player L))
    (nonmissing : CommitRecoveryMove.missed choice = false) :
    CommitRecoveryMove.lift (CommitRecoveryMove.underlying choice) = choice := by
  cases choice with
  | none => rfl
  | some move =>
      cases move with
      | mk action missing =>
          change missing = false at nonmissing
          cases nonmissing
          rfl

/-- A complete-word kernel retains the ORIGINAL omission marginal before physical encoding. -/
theorem word_response_law {Word : Type}
    (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
    (runtime : EventGraphRuntime (serviceGraph setup mode))
    (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))
    (bounds : MessageBounds (serviceGraph setup mode))
    (wellFormed : setup.WellFormed)
    (assessment : setup.commitRecoveryModel.BehavioralAssessment)
    (who : Player) (event : (serviceGraph setup mode).EventId) (payload : L.Ty)
    (binding : (serviceGraph setup mode).outputLayout event = .binding who payload)
    (serial : Nat) (past : List (phaseApplication runtime leaks).PlayerEntry)
    (view : (phaseApplication runtime leaks).PlayerView)
    (slotWeight : ℝ) (slotNonnegative : 0 ≤ slotWeight) (slotBounded : slotWeight ≤ 1)
    (prior : PMF Word) (read : Word → Option (OwnAction Player L))
    (predicts : prior.map read =
      (setup.commitRecoveryNonmissingProfile assessment.strategy who
        (setup.commitRecoveryClearInformation wellFormed who
          (phaseSourceView? setup mode runtime leaks who event view))).map
            (fun choice => CommitRecoveryMove.underlying choice.1)) :
    let source := assessment.strategy who (setup.commitRecoveryClearInformation wellFormed who
      (phaseSourceView? setup mode runtime leaks who event view))
    mix slotWeight slotNonnegative slotBounded
        (phaseRecoverySlotPolicy setup mode runtime leaks bounds wellFormed assessment who event
          payload binding past view)
        (phaseRecoveryBindingLaw setup mode runtime leaks wellFormed assessment who event payload
          binding serial (phaseSourceView? setup mode runtime leaks who event view)) =
      prior.bind fun word => PhaseCount.phaseBindingWordResponse runtime leaks bounds who event
        payload (source.map (fun choice => CommitRecoveryMove.missed choice.1)) serial slotWeight
          slotNonnegative slotBounded
          (phaseRecoveryBindingData setup mode event who payload binding
            (CommitRecoveryMove.lift (read word))).1 past view := by
  intro source
  let data := fun choice => phaseRecoveryBindingData setup mode event who payload binding choice
  let send := fun result => mix slotWeight slotNonnegative slotBounded
    (PhaseCount.phaseBindingSlotPolicy runtime leaks bounds who event payload
      (fun _ _ => PMF.pure result) past view)
    (PMF.pure (phaseBindingResponse runtime leaks who event payload result serial))
  rw [phaseRecoveryBindingResponse_factor setup mode runtime leaks bounds wellFormed assessment
    who event payload binding serial past view slotWeight slotNonnegative slotBounded]
  change (source.map (fun choice => CommitRecoveryMove.missed choice.1)).bind _ = _
  simp only [PhaseCount.phaseBindingWordResponse]
  conv_rhs => rw [PMF.bind_comm]
  apply bind_congr_on_support _
  intro missing present
  cases missing with
  | true =>
      change PMF.pure _ = prior.bind (fun _ => PMF.pure _)
      exact (PMF.bind_const _ _).symm
  | false =>
      change (((setup.commitRecoveryNonmissingProfile assessment.strategy who
        (setup.commitRecoveryClearInformation wellFormed who
          (phaseSourceView? setup mode runtime leaks who event view))).map
            (fun choice => data choice.1)).map Prod.fst).bind send =
        prior.bind (fun word => send (data (CommitRecoveryMove.lift (read word))).1)
      calc
        _ = (setup.commitRecoveryNonmissingProfile assessment.strategy who
            (setup.commitRecoveryClearInformation wellFormed who
              (phaseSourceView? setup mode runtime leaks who event view))).bind
                (fun choice => send (data choice.1).1) := by
          rw [PMF.bind_map, PMF.bind_map]
          rfl
        _ = (setup.commitRecoveryNonmissingProfile assessment.strategy who
            (setup.commitRecoveryClearInformation wellFormed who
              (phaseSourceView? setup mode runtime leaks who event view))).bind
                (fun choice => send (data
                  (CommitRecoveryMove.lift (CommitRecoveryMove.underlying choice.1))).1) := by
          apply bind_congr_on_support _
          intro choice supported
          have nonmissing := (mem_support_fiberPosterior present supported).1
          rw [lift_underlying_of_nonmissing choice.1 nonmissing]
        _ = _ := by
          have moved := congrArg (fun law : PMF (Option (OwnAction Player L)) =>
            law.bind fun action => send (data (CommitRecoveryMove.lift action)).1) predicts
          simpa only [PMF.bind_map, Function.comp_def] using moved.symm

/-- The actual initialized callback admits a complete-word implementation of its entire
canonical and slot response law, with the original omission marginal retained. -/
theorem RecoverySourceCheckpoint.binding_word_response_of_ready
    {setup : Setup (Player := Player) (L := L)} {mode : ExecutionMode}
    (runtime : EventGraphRuntime (serviceGraph setup mode))
    (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))
    (execution : (phaseApplication runtime leaks).Execution)
    (checkpoint : RecoverySourceCheckpoint setup mode execution.application)
    (wellFormed : setup.WellFormed)
    (assessment : setup.commitRecoveryModel.BehavioralAssessment)
    (mixed : assessment.IsFullyMixed)
    {Δ Ξ : SourceCtx Player L} {P Q : Finset VarId} {name : VarId} {owner : Player}
    {payload : L.Ty} (fresh : name ∉ Δ.map Prod.fst)
    (guard : SourceGuard L Δ owner name payload)
    (later : SourceProgram.CommitPrefix ((name, .commitment owner payload) :: Δ)
      (insert name P) Ξ Q)
    (suffix : SourceProgram Player L Ξ Q)
    (earlier : SourceProgram.CommitPrefix checkpoint.residual.context checkpoint.residual.names Δ P)
    (reconstruct : earlier.prepend (.commit name owner fresh guard (later.prepend suffix)) =
      checkpoint.residual.tail)
    (clear : execution.application.entry.excluded = ∅)
    (stored : execution.application.StoredCheckpoint)
    (selected : Fin (eventCount checkpoint.residual.tail))
    (atEnd : selected.val = earlier.length)
    (ready : execution.application.current.native.config.cut.Ready
      (checkpoint.embedding.event selected))
    (acting : (serviceGraph setup mode).actor? (checkpoint.embedding.event selected) = some owner)
    (notPublication : ¬ ((serviceGraph setup mode).outputLayout
      (checkpoint.embedding.event selected)).IsPublication)
    (valid : execution.application.current.native.BindingInvariant) {inputs}
    (reachable : execution.application.current.native.config.Reachable inputs)
    (retained : execution.application.HistoryCheckpoint)
    (saved : execution.application.entry.native.config.cut.IsPrefix
      execution.application.attempt.phase)
    (bounds : MessageBounds (serviceGraph setup mode))
    (binding : (serviceGraph setup mode).outputLayout (checkpoint.embedding.event selected) =
      .binding owner payload)
    (serial : Nat) (slotWeight : ℝ) (slotNonnegative : 0 ≤ slotWeight)
    (slotBounded : slotWeight ≤ 1) :
    ∃ residual : SourceProgram.BehavioralProfile checkpoint.residual.tail,
      let typed := cast (congrArg SourceProgram.BehavioralProfile reconstruct.symm) residual
      let embedding := cast (congrArg
        (fun program => OutputEmbedding (inputLayout setup.context) (outputLayout setup.program)
          program) reconstruct.symm) checkpoint.embedding
      let filled := fillCommitPrefix setup.program earlier
        (.commit name owner fresh guard (later.prepend suffix)) embedding
        execution.application.current.native.config.store checkpoint.source
      let current := earlier.tailProfile
        (.commit name owner fresh guard (later.prepend suffix)) typed
      let before := earlier.prefixLaw
        (.commit name owner fresh guard (later.prepend suffix)) typed checkpoint.source
      let complete := before.bind (fun config =>
        ((SourceProgram.CommitPrefix.commit name owner fresh guard later).prefixLaw suffix
          current config))
      let beforeView := fun view : DecisionView owner Ξ =>
        (later.entryView owner view).back true
      let wordAction := (earlier.append (.commit name owner fresh guard later)).wordAction
        owner earlier.length
      (filled.view owner ∈ (before.map (SourceProgram.Config.view owner)).support) ∧
        mix slotWeight slotNonnegative slotBounded
          (phaseRecoverySlotPolicy setup mode runtime leaks bounds wellFormed assessment owner
            (checkpoint.embedding.event selected) payload binding (execution.recall owner)
            (execution.observe (phaseApplication runtime leaks) owner))
          (phaseRecoveryBindingLaw setup mode runtime leaks wellFormed assessment owner
            (checkpoint.embedding.event selected) payload binding serial
            (phaseSourceView? setup mode runtime leaks owner (checkpoint.embedding.event selected)
              (execution.observe (phaseApplication runtime leaks) owner))) =
        (fiberPosterior (complete.map (SourceProgram.Config.view owner)) beforeView
          (filled.view owner)).bind
          (fun word => PhaseCount.phaseBindingWordResponse runtime leaks bounds owner
            (checkpoint.embedding.event selected) payload
            ((assessment.strategy owner (setup.commitRecoveryClearInformation wellFormed owner
              (phaseSourceView? setup mode runtime leaks owner (checkpoint.embedding.event selected)
                (execution.observe (phaseApplication runtime leaks) owner)))).map
                  (fun choice => CommitRecoveryMove.missed choice.1)) serial slotWeight
            slotNonnegative slotBounded
            (phaseRecoveryBindingData setup mode (checkpoint.embedding.event selected) owner
              payload binding (CommitRecoveryMove.lift (wordAction word))).1
            (execution.recall owner)
            (execution.observe (phaseApplication runtime leaks) owner)) := by
  obtain ⟨residual, predicted⟩ := checkpoint.binding_owned_word_prediction_of_ready runtime leaks
    execution wellFormed assessment mixed fresh guard later suffix earlier reconstruct clear
    stored selected atEnd ready acting notPublication valid reachable retained saved
  refine ⟨residual, ?_⟩
  intro typed embedding filled current before complete beforeView wordAction
  obtain ⟨present, predictsOwned⟩ := predicted
  refine ⟨present, ?_⟩
  exact word_response_law setup mode runtime leaks bounds wellFormed assessment owner
    (checkpoint.embedding.event selected) payload binding serial (execution.recall owner)
    (execution.observe (phaseApplication runtime leaks) owner) slotWeight slotNonnegative
    slotBounded (fiberPosterior (complete.map (SourceProgram.Config.view owner)) beforeView
      (filled.view owner)) wordAction predictsOwned

end Vegas
