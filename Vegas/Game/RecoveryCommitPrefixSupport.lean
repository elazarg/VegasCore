/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.RecoverySourceBoundary
import Vegas.Game.CommitRecoveryNonmissingSource
import Vegas.Source.CommitRecoveryCommitStep

/-! # Positive source prefix laws along actual clear recovery attempts -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

private theorem commitKernel_supported
    (setup : Setup (Player := Player) (L := L)) (wellFormed : setup.WellFormed)
    (assessment : setup.commitRecoveryModel.BehavioralAssessment)
    (mixed : assessment.IsFullyMixed)
    {Γ : SourceCtx Player L} {O : Finset VarId} {name : VarId} {owner : Player}
    {payload : L.Ty} {fresh : name ∉ Γ.map Prod.fst}
    (guard : SourceGuard L Γ owner name payload)
    (tail : SourceProgram Player L ((name, .commitment owner payload) :: Γ) (insert name O))
    (profile : SourceProgram.BehavioralProfile (.commit name owner fresh guard tail))
    (lift : ProtocolState (.commit name owner fresh guard tail) → ProtocolState setup.program)
    (ranks : ∀ point, ProtocolState.remaining setup.program (lift point) =
      ProtocolState.remaining (.commit name owner fresh guard tail) point)
    (actors : ∀ point, ProtocolState.actor setup.program (lift point) =
      ProtocolState.actor (.commit name owner fresh guard tail) point)
    (menus : ∀ point who, ProtocolView.recoveryAvailable who setup.program
      (ProtocolState.observe who setup.program (lift point)) =
      ProtocolView.recoveryAvailable who (.commit name owner fresh guard tail)
        (ProtocolState.observe who (.commit name owner fresh guard tail) point))
    (raw : ∀ who point, (profile who).protocolAction (.commit name owner fresh guard tail)
      (ProtocolState.observe who (.commit name owner fresh guard tail) point) =
      (setup.commitRecoveryNonmissingProfile assessment.strategy who
        (setup.commitRecoveryClearInformation wellFormed who
          (some (ProtocolState.observe who setup.program (lift point))))).map
        (fun choice => CommitRecoveryMove.underlying choice.1))
    (entry : Config Player L Γ) (state : CommitRecoveryState setup.program)
    (trace : setup.commitRecoveryProtocol.Trace (some state))
    (atEntry : state.point = lift (.inl entry)) (clear : state.excluded = ∅)
    (result : PublicationResult (L.Val payload)) :
    result ∈ (commitKernel profile (entry.view owner)).support := by
  classical
  let info := setup.commitRecoveryClearInformation wellFormed owner
    (some (ProtocolState.observe owner setup.program (lift (.inl entry))))
  have observed : setup.commitRecoveryModel.infoOf owner trace = info := by
    simpa only [SourceProgram.Setup.commitRecoveryPrivate, Option.map_some, atEntry, info] using
      setup.commitRecoveryClearInformation_observed wellFormed owner trace clear
  have acting : ProtocolState.actor setup.program state.point = some owner := by
    rw [atEntry, actors]
    rfl
  have running : ¬ setup.commitRecoveryProtocol.terminal (some state) := by
    intro stopped
    have zero := (ProtocolState.remaining_zero_iff_terminal setup.program state.point).mpr stopped
    rw [atEntry, ranks] at zero
    change instructionCount tail + 1 = 0 at zero
    omega
  let move : CommitRecoveryMove Player L := ⟨.commit owner name payload result, false⟩
  let chosen : setup.commitRecoveryModel.Choice owner info := ⟨some move, by
    change setup.commitRecoveryMenu owner info (some move)
    constructor
    · unfold SourceProgram.Setup.commitRecoveryActive
      rw [setup.commitRecoveryClearInformation_current,
        setup.commitRecoveryClearInformation_excluded]
      exact ⟨by simpa only [ProtocolState.actor_observe_eq, ← atEntry] using acting,
        Finset.notMem_empty _⟩
    · rw [setup.commitRecoveryClearInformation_current]
      change move ∈ ProtocolView.recoveryAvailable owner setup.program
        (ProtocolState.observe owner setup.program (lift (.inl entry)))
      rw [menus]
      refine ⟨⟨result, ?_, rfl⟩, ?_⟩
      · cases result <;> trivial
      · intro impossible
        cases impossible⟩
  have allSupported : ∀ choice : setup.commitRecoveryModel.Choice owner info,
      choice ∈ (assessment.strategy owner info).support := by
    rw [← observed]
    exact fun choice => mixed.support_at_history ⟨_, trace⟩ running owner choice
  have original := allSupported chosen
  have present := setup.commitRecovery_nonmissing_present assessment mixed ⟨_, trace⟩
    running owner
  rw [observed] at present
  have conditioned : chosen ∈
      (setup.commitRecoveryNonmissingProfile assessment.strategy owner info).support := by
    rw [SourceProgram.Setup.commitRecoveryNonmissingProfile, fiberPosterior_support _ _ _ present]
    exact ⟨rfl, original⟩
  have sampled : some (OwnAction.commit owner name payload result) ∈
      ((profile owner).protocolAction (.commit name owner fresh guard tail)
        (ProtocolState.observe owner (.commit name owner fresh guard tail)
          (.inl entry))).support := by
    rw [raw]
    exact (PMF.mem_support_map_iff _ _ _).mpr ⟨chosen, conditioned, rfl⟩
  simp only [BehavioralPolicy.protocolAction, ProtocolState.observe, Sum.elim_inl,
    dite_true] at sampled
  obtain ⟨choice, supported, same⟩ := (PMF.mem_support_map_iff _ _ _).mp sampled
  have equal : choice = result := by
    simpa only [Option.some.injEq, OwnAction.commit.injEq, heq_eq_eq, true_and] using same
  exact equal ▸ supported

private theorem attempt_supported
    (setup : Setup (Player := Player) (L := L)) (wellFormed : setup.WellFormed)
    (assessment : setup.commitRecoveryModel.BehavioralAssessment)
    (mixed : assessment.IsFullyMixed)
    {Γ Δ : SourceCtx Player L} {O P : Finset VarId} (block : SourceProgram.CommitPrefix Γ O Δ P) :
    ∀ (suffix : SourceProgram Player L Δ P)
      (profile : SourceProgram.BehavioralProfile (block.prepend suffix))
      (lift : ProtocolState (block.prepend suffix) → ProtocolState setup.program)
      (_ranks : ∀ point, ProtocolState.remaining setup.program (lift point) =
        ProtocolState.remaining (block.prepend suffix) point)
      (_actors : ∀ point, ProtocolState.actor setup.program (lift point) =
        ProtocolState.actor (block.prepend suffix) point)
      (_menus : ∀ point who, ProtocolView.recoveryAvailable who setup.program
        (ProtocolState.observe who setup.program (lift point)) =
        ProtocolView.recoveryAvailable who (block.prepend suffix)
          (ProtocolState.observe who (block.prepend suffix) point))
      (_steps : ∀ point excluded joint,
        ProtocolState.recoveryStep setup.program (lift point) excluded joint =
        (ProtocolState.recoveryStep (block.prepend suffix) point excluded joint).map
          (fun result => (lift result.1, result.2)))
      (_raw : ∀ who point, (profile who).protocolAction (block.prepend suffix)
        (ProtocolState.observe who (block.prepend suffix) point) =
        (setup.commitRecoveryNonmissingProfile assessment.strategy who
          (setup.commitRecoveryClearInformation wellFormed who
            (some (ProtocolState.observe who setup.program (lift point))))).map
          (fun choice => CommitRecoveryMove.underlying choice.1))
      (entry : Config Player L Γ) (state : CommitRecoveryState setup.program)
      (_trace : setup.commitRecoveryProtocol.Trace (some state))
      (_atEntry : state.point = lift (ProtocolState.entry (block.prepend suffix) entry))
      (_clear : state.excluded = ∅) (final : Config Player L Δ),
      block.Attempt entry ∅ final ∅ → final ∈ (block.prefixLaw suffix profile entry).support := by
  induction block with
  | nil =>
      intro suffix profile lift ranks actors menus steps raw entry state trace atEntry clear final
        attempt
      cases attempt
      exact (PMF.mem_support_pure_iff _ _).mpr rfl
  | commit name owner fresh guard rest ih =>
      intro suffix profile lift ranks actors menus steps raw entry state trace atEntry clear final
        attempt
      cases attempt with
      | excluded inactive later => exact (Finset.notMem_empty owner inactive).elim
      | active active result missed missingFailure later =>
          have notMissed : missed = false := by
            cases missed with
            | false => rfl
            | true =>
                have impossible := later.excluded_subset (Finset.mem_insert_self owner ∅)
                exact (Finset.notMem_empty owner impossible).elim
          subst missed
          have drawn := commitKernel_supported setup wellFormed assessment mixed guard
            (rest.prepend suffix) profile lift ranks actors menus raw entry state trace atEntry
            clear result
          obtain ⟨monotone, nextLegal, nextReached⟩ := lifted_commit_successor setup.program
            (setup.initialConfig setup.initialLaw.support_nonempty.choose) guard
            (rest.prepend suffix) lift ranks actors menus steps entry state atEntry result false
            (by intro impossible; cases impossible)
          have next : (SourceProgram.commitRecoveryProtocol setup.program
              (setup.initialConfig setup.initialLaw.support_nonempty.choose)).Successor _ state :=
            ⟨_, nextLegal, nextReached⟩
          have activeState : owner ∉ state.excluded := by
            rw [clear]
            exact Finset.notMem_empty _
          simp only [activeState, ↓reduceIte, excludeCommit, Bool.false_eq_true,
            ↓reduceIte] at monotone next
          let target := (state.install
            (lift (.inr (ProtocolState.entry (rest.prepend suffix)
              (commitSuccessor name guard entry result))), state.excluded) monotone).close
          obtain ⟨nextTrace, _fuel, _prefix⟩ := setup.recoveryTrace_of_reaches _ trace
            (.tail .refl next)
          have targetPoint : target.point = lift (.inr
              (ProtocolState.entry (rest.prepend suffix)
                (commitSuccessor name guard entry result))) := by
            apply CommitRecoveryState.close_point_of_no_new_failure
            simp only [CommitRecoveryState.NewFailure, CommitRecoveryState.install, clear,
              Finset.empty_sdiff, Finset.not_nonempty_empty, not_false_eq_true]
          have targetClear : target.excluded = ∅ := by
            exact (CommitRecoveryState.close_excluded _).trans clear
          apply (PMF.mem_support_bind_iff ..).mpr
          refine ⟨result, drawn, ?_⟩
          apply ih suffix (afterCommit profile) (fun point => lift (.inr point))
            (fun point => ranks (.inr point)) (fun point => actors (.inr point))
            (fun point who => menus (.inr point) who) ?_
            (fun who point => raw who (.inr point))
            (commitSuccessor name guard entry result) target nextTrace targetPoint targetClear
            final later
          intro point excluded joint
          have same := steps (.inr point) excluded joint
          simpa only [CommitPrefix.prepend, ProtocolState.recoveryStep, Sum.elim_inr,
            PMF.map_comp, Function.comp_def] using same

/-- Every no-exclusion source attempt from the actual saved checkpoint has
positive mass in the chronological nonmissing law. Failed typed results remain
available; full mixing is used only at genuine initialized auxiliary histories. -/
theorem RecoverySourceCheckpoint.attempt_mem_prefixLaw
    {setup : Setup (Player := Player) (L := L)} {mode : ExecutionMode}
    {state : EventGraphRuntime.PhaseRuntimeState (serviceGraph setup mode)}
    (checkpoint : RecoverySourceCheckpoint setup mode state)
    (savedClear : state.entry.excluded = ∅) (wellFormed : setup.WellFormed)
    (assessment : setup.commitRecoveryModel.BehavioralAssessment)
    (mixed : assessment.IsFullyMixed)
    (residual : SourceProgram.BehavioralProfile checkpoint.residual.tail)
    (raw : ∀ owner point, (residual owner).protocolAction checkpoint.residual.tail
      (ProtocolState.observe owner checkpoint.residual.tail point) =
      (setup.commitRecoveryNonmissingProfile assessment.strategy owner
        (setup.commitRecoveryClearInformation wellFormed owner
          (some (ProtocolState.observe owner setup.program
            (checkpoint.residual.lift point))))).map
        (fun choice => CommitRecoveryMove.underlying choice.1))
    {Δ : SourceCtx Player L} {P : Finset VarId}
    (earlier : SourceProgram.CommitPrefix checkpoint.residual.context checkpoint.residual.names Δ P)
    (suffix : SourceProgram Player L Δ P)
    (reconstruct : earlier.prepend suffix = checkpoint.residual.tail)
    (final : Config Player L Δ) (attempt : earlier.Attempt checkpoint.source ∅ final ∅) :
    final ∈ (earlier.prefixLaw suffix
      (cast (congrArg SourceProgram.BehavioralProfile reconstruct.symm) residual)
        checkpoint.source).support := by
  rcases checkpoint with ⟨⟨Γ, O, program, lift⟩, entry, refs, registry, embedding, before,
    compiled, terminalAlignment, agrees, guards, failures, unique, ranks, actors, commits, owners,
    endpoints, automatic, histories, memories, steps, menus, readout, initialized, views,
    savedHistory, origin⟩
  dsimp only at *
  change SourceProgram.Config Player L Γ at entry
  change SourceProgram.CommitPrefix Γ O Δ P at earlier
  change earlier.prepend suffix = program at reconstruct
  subst program
  let first := CommitRecoveryState.atPoint
    (lift (ProtocolState.entry (earlier.prepend suffix) entry)) ∅ state.generation
  have actual : Nonempty (setup.commitRecoveryProtocol.Trace (some first)) := by
    rw [savedClear] at initialized
    exact initialized
  obtain ⟨trace⟩ := actual
  exact attempt_supported setup wellFormed assessment mixed earlier suffix residual lift ranks
    actors (fun point who => menus who point) steps raw entry first trace rfl rfl final attempt

end Vegas
