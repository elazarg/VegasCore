/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseProposalGenuineReference
import Vegas.Game.PhaseProposalUnflagged

/-! # Actual unflagged binding responses retain ordinary typed draws -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
  (runtime : EventGraphRuntime (serviceGraph setup mode))
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))
  (bounds : MessageBounds (serviceGraph setup mode))
  (plan : RuntimePhasePlan (serviceGraph setup mode))

local notation "app" => phaseApplication runtime leaks

/-- Canonicalizing an actual packet class preserves its entire effective
typed preparation law. It need not preserve private evidence-request syntax. -/
theorem phaseProposalUnflaggedPolicy_preparation_law
    (values : ∀ who (key : setup.ProposalRecoveryComponent who),
      PMF (setup.CommitRecoveryValueChoice who key.1))
    (who : Player) (past : List (app).PlayerEntry) (view : (app).PlayerView) :
    (phaseProposalUnflaggedPolicy setup mode runtime leaks bounds plan values who past view).map
        (fun response => response.transmission.bind (PhaseProposal.bindingPreparation)) =
      (phaseProposalBasePolicy setup mode runtime leaks bounds plan values PhaseProposalRates.zero
        who past view).map
          (fun response => response.transmission.bind (PhaseProposal.bindingPreparation)) := by
  have projected := congrArg (fun law : PMF
      (PhaseProposal.ResponseClass runtime leaks bounds who past view) =>
        law.map (fun chosen => chosen.val.1))
    (phaseProposalUnflaggedResponses_project setup mode runtime leaks bounds plan values who
      past view)
  rw [← phaseProposalBaseResponses_map_val setup mode runtime leaks bounds plan values
    PhaseProposalRates.zero who past view]
  simpa only [phaseProposalUnflaggedPolicy, phaseProposalBaseClasses, PMF.map_comp,
    Function.comp_def, PhaseProposal.projectResponse, PhaseProposal.responseClass] using projected

/-- At an actual fresh unspent binding with a computed query, the encoder
preserves any ordinary value law, including a fixed table coordinate. -/
theorem phaseProposalUnflaggedBinding_preparation_law_of_query
    (covered : bounds.CoversOutputValues)
    (values : ∀ who (key : setup.ProposalRecoveryComponent who),
      PMF (setup.CommitRecoveryValueChoice who key.1))
    (horizon : Nat) (scheduler : (app).Scheduler)
    (capacity : horizon ≤ bounds.candidateCount) (remaining : Nat) (who : Player)
    (execution : (app).Execution)
    (trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (setup.initialLaw.map fun draw => PhaseRuntimeState.initial plan (encodeInputs draw))
      horizon scheduler).Trace (some ⟨remaining, some who, execution⟩))
    (event : (serviceGraph setup mode).EventId) (payload : L.Ty)
    (binding : (serviceGraph setup mode).outputLayout event = .binding who payload)
    (request : execution.application.SeedRequest who ⟨execution.application.attempt, event⟩)
    (unsent : ∀ message ∈ (app).outputs (execution.recall who),
      PhaseCount.event? message.payload ≠ some ⟨execution.application.attempt, event⟩)
    (key : setup.ProposalRecoveryComponent who)
    (queried : phaseProposalQuery? setup mode runtime leaks plan who event (execution.recall who)
      (execution.observe app who) = some key) :
    (phaseProposalUnflaggedPolicy setup mode runtime leaks bounds plan values who
      (execution.recall who) (execution.observe app who)).map
        (fun response => response.transmission.bind (PhaseProposal.bindingPreparation)) =
      (values who key).map (fun choice => some (⟨payload,
        phaseRecoveryDomainValue setup mode event who payload binding
          choice.val.val⟩ : Raw L)) := by
  classical
  let inputs := setup.initialLaw.map encodeInputs
  have counted : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace
        (some ⟨remaining, some who, execution⟩) := by
    dsimp only [inputs]
    rw [PMF.map_comp]
    exact trace
  have bounded := covered event
  rw [binding] at bounded
  let results := phaseProposalBindingResults setup mode runtime leaks plan values
    PhaseProposalRates.zero who event payload binding
  obtain ⟨serial, _below, bindingLaw, _storedLaw⟩ :=
    PhaseCount.phaseBindingPolicy_of_history runtime
    leaks bounds who event payload binding results (PhaseCount.onePacketMenu runtime leaks bounds)
      plan inputs horizon scheduler capacity ⟨remaining, some who, execution⟩ counted rfl request
        unsent bounded
  have native := (phaseNativeInvariant_history runtime leaks plan inputs horizon scheduler
    ((PhaseCount.onePacketMenu runtime leaks bounds).toRawTrace _ horizon scheduler counted))
  obtain ⟨draw, invariant⟩ := native
  have dispatch : phaseProposalBasePolicy setup mode runtime leaks bounds plan values
      PhaseProposalRates.zero who (execution.recall who) (execution.observe app who) =
        PhaseCount.phaseBindingPolicy runtime leaks bounds who event payload results
          (execution.recall who) (execution.observe app who) := by
    unfold phaseProposalBasePolicy
    rw [phasePolicyDispatch_binding setup mode runtime leaks _ _ execution invariant who event
      payload binding request]
    simp only [PhaseProposalRates.zero, PhaseCount.bindingResultEncoder, mix_zero]
    rfl
  rw [phaseProposalUnflaggedPolicy_preparation_law, dispatch, bindingLaw, PMF.map_comp]
  dsimp only [results, phaseProposalBindingResults]
  rw [queried]
  simp only [PhaseProposalRates.zero, mix_zero, PMF.map_comp, Function.comp_def,
    phaseBindingResponse, PhaseProposal.bindingPreparation, binding, Option.bind_some,
    Raw.as?_mk, Option.map_some]

/-- At a genuine fresh unspent binding, zero future flags preserve every
ordinary value draw and emit a usable typed preparation. A guard may reject
that value later; guard debt is not removed or classified as a rare flag. -/
theorem phaseProposalUnflaggedBinding_preparation_law
    (complete : leaks = MessageNetwork.completePendingObservation)
    (covered : bounds.CoversOutputValues)
    (maximal : plan.phases.IsChain fun first last =>
      first.kind ≠ last.kind ∨ first.kind = .sample)
    (values : ∀ who (key : setup.ProposalRecoveryComponent who),
      PMF (setup.CommitRecoveryValueChoice who key.1))
    (fullValues : ∀ who key, FullSupport (values who key))
    (horizon : Nat) (scheduler : (app).Scheduler)
    (capacity : horizon ≤ bounds.candidateCount) (remaining : Nat) (who : Player)
    (execution : (app).Execution)
    (trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (setup.initialLaw.map fun draw => PhaseRuntimeState.initial plan (encodeInputs draw))
      horizon scheduler).Trace (some ⟨remaining, some who, execution⟩))
    (event : (serviceGraph setup mode).EventId) (payload : L.Ty)
    (binding : (serviceGraph setup mode).outputLayout event = .binding who payload)
    (request : execution.application.SeedRequest who ⟨execution.application.attempt, event⟩)
    (unsent : ∀ message ∈ (app).outputs (execution.recall who),
      PhaseCount.event? message.payload ≠ some ⟨execution.application.attempt, event⟩) :
    ∃ key : setup.ProposalRecoveryComponent who,
      phaseProposalQuery? setup mode runtime leaks plan who event (execution.recall who)
          (execution.observe app who) = some key ∧
      (phaseProposalUnflaggedPolicy setup mode runtime leaks bounds plan values who
        (execution.recall who) (execution.observe app who)).map
          (fun response => response.transmission.bind (PhaseProposal.bindingPreparation)) =
        (values who key).map (fun choice => some (⟨payload,
          phaseRecoveryDomainValue setup mode event who payload binding
            choice.val.val⟩ : Raw L)) := by
  have raw := (PhaseCount.onePacketMenu runtime leaks bounds).toRawTrace _ horizon scheduler trace
  obtain ⟨key, queried, _ordinary⟩ := phaseProposalDomainValues_fullSupport_of_binding setup mode
    runtime leaks complete plan maximal values fullValues horizon scheduler raw who rfl event
      payload binding request
  exact ⟨key, queried, phaseProposalUnflaggedBinding_preparation_law_of_query setup mode runtime
    leaks bounds plan covered values horizon scheduler capacity remaining who execution trace
      event payload binding request unsent key queried⟩

/-- Every supported response at a fresh unspent binding carries a typed usable
preparation. The value remains an unrestricted ordinary source draw. -/
theorem phaseProposalUnflaggedBinding_supported_usable
    (complete : leaks = MessageNetwork.completePendingObservation)
    (covered : bounds.CoversOutputValues)
    (maximal : plan.phases.IsChain fun first last =>
      first.kind ≠ last.kind ∨ first.kind = .sample)
    (values : ∀ who (key : setup.ProposalRecoveryComponent who),
      PMF (setup.CommitRecoveryValueChoice who key.1))
    (fullValues : ∀ who key, FullSupport (values who key))
    (horizon : Nat) (scheduler : (app).Scheduler)
    (capacity : horizon ≤ bounds.candidateCount) (remaining : Nat) (who : Player)
    (execution : (app).Execution)
    (trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (setup.initialLaw.map fun draw => PhaseRuntimeState.initial plan (encodeInputs draw))
      horizon scheduler).Trace (some ⟨remaining, some who, execution⟩))
    (event : (serviceGraph setup mode).EventId) (payload : L.Ty)
    (binding : (serviceGraph setup mode).outputLayout event = .binding who payload)
    (request : execution.application.SeedRequest who ⟨execution.application.attempt, event⟩)
    (unsent : ∀ message ∈ (app).outputs (execution.recall who),
      PhaseCount.event? message.payload ≠ some ⟨execution.application.attempt, event⟩)
    (response : (app).Action)
    (supported : response ∈ (phaseProposalUnflaggedPolicy setup mode runtime leaks bounds plan
      values who (execution.recall who) (execution.observe app who)).support) :
    ∃ (material : WitnessedSubmission (serviceGraph setup mode)) (value : L.Val payload),
      response.transmission = some material ∧
        PhaseProposal.bindingPreparation material = some (⟨payload, value⟩ : Raw L) := by
  obtain ⟨key, _queried, law⟩ := phaseProposalUnflaggedBinding_preparation_law setup mode runtime
    leaks bounds plan complete covered maximal values fullValues horizon scheduler capacity
      remaining who execution trace event payload binding request unsent
  have observed := (PMF.mem_support_map_iff
    (fun action : (app).Action => action.transmission.bind PhaseProposal.bindingPreparation)
    _ _).mpr ⟨response, supported, rfl⟩
  rw [law] at observed
  obtain ⟨choice, _positive, same⟩ := (PMF.mem_support_map_iff _ _ _).mp observed
  cases emitted : response.transmission with
  | none => simp only [emitted, Option.bind_none] at same; cases same
  | some material =>
      refine ⟨material, phaseRecoveryDomainValue setup mode event who payload binding
        choice.val.val, rfl, ?_⟩
      simpa only [emitted, Option.bind_some] using same.symm

end Vegas
