/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.PhaseProposalDomainReadout
import Vegas.Game.PhaseProposalReference

/-! # Full ordinary value support at every genuine physical binding query -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]

omit [Fintype Player] in
private theorem normalized_current (setup : Setup (Player := Player) (L := L)) (who : Player)
    (information : setup.commitRecoveryModel.InfoState who) :
    (setup.commitRecoveryErasedInformation who
        (setup.commitRecoveryNoMissInformation who information)).1.1.1 =
      information.1.1.1.map (ProtocolView.eraseHistory who setup.program) := by
  have kept : (setup.commitRecoveryNoMissInformation who information).1.1.1 =
      information.1.1.1 := by
    unfold Setup.commitRecoveryNoMissInformation
    split
    · exact (setup.commitRecoveryWithAttemptExclusions_controls who
        (setup.commitRecoveryAttemptStart who information)
        (setup.commitRecoverySavedExclusions who information) information).1
    · rfl
  change ((setup.commitRecoveryNoMissInformation who information).1.1.1.map _) = _
  rw [kept]

omit [Fintype Player] in
/-- Source menu normalization preserves activity: a genuine available move
remains available. This uses the actual source decision, not a fabricated key. -/
private theorem normalized_active (setup : Setup (Player := Player) (L := L)) (who : Player)
    (information : setup.commitRecoveryModel.InfoState who)
    (decision : setup.commitRecoveryModel.IsDecisionInfo who information) :
    setup.commitRecoveryActive who
      (setup.commitRecoveryErasedInformation who
        (setup.commitRecoveryNoMissInformation who information)).1.1 := by
  obtain ⟨_site, _running, move, legal⟩ := decision
  have retained : setup.commitRecoveryModel.menu who
      (setup.commitRecoveryErasedInformation who
        (setup.commitRecoveryNoMissInformation who information)) (some move) := by
    rw [setup.commitRecoveryErasedInformation_menu, setup.commitRecoveryNoMissInformation_menu]
    exact legal
  exact retained.1

/-- Positive ordinary source tables cover every native typed payload at each
genuine requested binding, even after earlier exclusions or accepted failures.
All decoder/activity premises are derived from the actual query and source
history; this theorem supplies no posterior or payoff comparison. -/
theorem phaseProposalDomainValues_fullSupport_of_binding
    (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
    (runtime : EventGraphRuntime (serviceGraph setup mode))
    (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))
    (complete : leaks = MessageNetwork.completePendingObservation)
    (plan : RuntimePhasePlan (serviceGraph setup mode))
    (maximal : plan.phases.IsChain fun first last =>
      first.kind ≠ last.kind ∨ first.kind = .sample)
    (values : ∀ who (key : setup.ProposalRecoveryComponent who),
      PMF (setup.CommitRecoveryValueChoice who key.1))
    (full : ∀ who key, FullSupport (values who key))
    (horizon : Nat) (scheduler : (phaseApplication runtime leaks).Scheduler) {control}
    (trace : ((phaseApplication runtime leaks).protocol
      (setup.initialLaw.map fun draw => PhaseRuntimeState.initial plan (encodeInputs draw))
      horizon scheduler).Trace (some control))
    (who : Player) (active : control.actor = some who)
    (event : (serviceGraph setup mode).EventId) (payload : L.Ty)
    (binding : (serviceGraph setup mode).outputLayout event = .binding who payload)
    (request : control.execution.application.SeedRequest who
      ⟨control.execution.application.attempt, event⟩) :
    ∃ key : setup.ProposalRecoveryComponent who,
      phaseProposalQuery? setup mode runtime leaks plan who event
          (control.execution.recall who)
          (control.execution.observe (phaseApplication runtime leaks) who) = some key ∧
      FullSupport ((values who key).map fun choice =>
        phaseRecoveryDomainValue setup mode event who payload binding choice.val.val) := by
  obtain ⟨current, sourceTrace, _actor, _rank, decision, queried⟩ :=
    phaseProposalQuery?_genuine_base setup mode runtime leaks complete plan maximal horizon
      scheduler trace who active event payload binding request
  let key : setup.ProposalRecoveryComponent who :=
    (setup.commitRecoveryErasedInformation who
      (setup.commitRecoveryNoMissInformation who
        (setup.commitRecoveryModel.infoOf who sourceTrace)),
      PhaseProposal.sourceArchive control.execution.network.inputs)
  refine ⟨key, queried, ?_⟩
  have acting := normalized_active setup who _ decision
  have baseQuery := queried
  unfold phaseProposalQuery? at baseQuery
  obtain ⟨source, sourcePresent, keyEq⟩ := Option.map_eq_some_iff.mp baseQuery
  have typedQuery := sourcePresent
  unfold phaseVirtualSourceQuery? at typedQuery
  obtain ⟨typed, typedPresent, sourceEq⟩ := Option.map_eq_some_iff.mp typedQuery
  have decodedQuery := typedPresent
  dsimp only [phaseVirtualSourceView?, ReactiveApplication.Execution.observe, phaseApplication,
    PhaseRuntimeState.playerView, State.playerView] at decodedQuery
  rw [dite_eq_left rfl] at decodedQuery
  obtain ⟨view, decoded, viewEq⟩ := Option.map_eq_some_iff.mp decodedQuery
  have typedCurrent : key.1.1.1.1 =
      some (ProtocolView.virtualBindings who (setup.context.map Prod.fst).toFinset setup.program
        (ProtocolView.eraseHistory who setup.program view)) := by
    have first := congrArg Prod.fst keyEq
    rw [← first, ← sourceEq, normalized_current]
    simp only [Setup.commitRecoveryErasedRead, Option.map_some, ← viewEq,
      ProtocolView.virtualBindings_eraseHistory,
      ProtocolView.eraseHistory_virtualBindings]
  change decodeEventView? setup.program
      (ContextRefs.initial setup.context (outputLayout setup.program))
      (outputEmbedding setup.program).ref who event
      ((serviceGraph setup mode).playerStore who
        control.execution.application.current.native.config.store) [] = some view at decoded
  have erasedDecoded : decodeEventView? setup.program
      (ContextRefs.initial setup.context (outputLayout setup.program))
      (outputEmbedding setup.program).ref who event
      ((serviceGraph setup mode).playerStore who
        control.execution.application.current.native.config.store) [] =
        some (ProtocolView.eraseHistory who setup.program view) := by
    rw [decodeEventView?_eraseHistory (past := []), decoded, Option.map_some]
  exact phaseRecoveryDomainValue_fullSupport setup mode
    (ContextRefs.initial setup.context (outputLayout setup.program))
    (outputEmbedding setup.program).ref who event payload binding _ [] _ erasedDecoded key.1
      typedCurrent acting (values who key) (full who key)

/-- The independent bad-preparation atom and the full ordinary typed table
cover the complete declared result type at every genuine binding query. -/
theorem phaseProposalBindingResults_fullSupport_of_binding
    (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
    (runtime : EventGraphRuntime (serviceGraph setup mode))
    (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))
    (complete : leaks = MessageNetwork.completePendingObservation)
    (plan : RuntimePhasePlan (serviceGraph setup mode))
    (maximal : plan.phases.IsChain fun first last =>
      first.kind ≠ last.kind ∨ first.kind = .sample)
    (values : ∀ who (key : setup.ProposalRecoveryComponent who),
      PMF (setup.CommitRecoveryValueChoice who key.1))
    (full : ∀ who key, FullSupport (values who key))
    (rates : PhaseProposalRates) (badPositive : 0 < rates.badPreparation.val)
    (badBelow : rates.badPreparation.val < 1)
    (horizon : Nat) (scheduler : (phaseApplication runtime leaks).Scheduler) {control}
    (trace : ((phaseApplication runtime leaks).protocol
      (setup.initialLaw.map fun draw => PhaseRuntimeState.initial plan (encodeInputs draw))
      horizon scheduler).Trace (some control))
    (who : Player) (active : control.actor = some who)
    (event : (serviceGraph setup mode).EventId) (payload : L.Ty)
    (binding : (serviceGraph setup mode).outputLayout event = .binding who payload)
    (request : control.execution.application.SeedRequest who
      ⟨control.execution.application.attempt, event⟩) :
    FullSupport (phaseProposalBindingResults setup mode runtime leaks plan values rates who event
      payload binding (control.execution.recall who)
        (control.execution.observe (phaseApplication runtime leaks) who)) := by
  obtain ⟨key, queried, ordinary⟩ := phaseProposalDomainValues_fullSupport_of_binding setup mode
    runtime leaks complete plan maximal values full horizon scheduler trace who active event payload
      binding request
  intro result
  unfold phaseProposalBindingResults
  rw [queried]
  cases result with
  | failure =>
      exact mem_support_mix_left _ _ _ badPositive ((PMF.mem_support_pure_iff _ _).mpr rfl)
  | success value =>
      apply mem_support_mix_right _ _ _ badBelow
      obtain ⟨choice, supported, same⟩ := (PMF.mem_support_map_iff _ _ _).mp (ordinary value)
      exact (PMF.mem_support_map_iff _ _ _).mpr
        ⟨choice, supported, congrArg PublicationResult.success same⟩

end Vegas
