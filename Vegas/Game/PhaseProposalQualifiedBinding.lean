/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseProposalCurrentBindingGain
import Vegas.Pending.PhaseAttemptReceiptSnapshot
import Vegas.Game.PhaseProposalOrdinaryBindingCheckpoint
import Vegas.Game.ReservedEpochStoppedFootprint
import Vegas.Game.ProposalRecoveryFutureFlags
import Vegas.Source.ProposalRecoveryPreparationRepairMoves
import Interaction.ReactiveLocalContinuation
import GameTheoryExtensions.Analysis.Protocol.StoppedTerminalBound
import GameTheory.Math.Probability.FiniteSampling
import Vegas.Game.ProposalRecoveryPublicClassConstancy
import Vegas.Game.PhaseProposalNativeSourceInformation
import Vegas.Game.ProposalRecoveryPools
import Vegas.Game.PhaseProposalAttemptArchive
import GameTheory.Protocol.Predraw
import Interaction.ReactiveAnchoredStopped
import Interaction.ReactiveSchedulerStoppedSeed
import Interaction.ReactiveSchedulerFinishSeed
import Interaction.ReactiveRawRoundTrace
import Interaction.ReactiveTerminalEvaluation
import Vegas.Game.ConcurrentRawSequentialPreservation
import Vegas.Pending.ReservedEpochService
import GameTheoryExtensions.Math.Probability.PresentConditional

/-! # Qualified binding payoffs at the original native information

The current response is a literal counted-menu atom. The first exit from its
original attempt retains the completed physical image before normalization.
The terminal continuation starts at that same stopped history, retaining both
the original initializer and the scheduler's accumulated observations.
-/

noncomputable section

namespace Vegas.PhaseProposalQualifiedBinding

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
  (runtime : EventGraphRuntime (serviceGraph setup mode))
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))
  (bounds : MessageBounds (serviceGraph setup mode))
  (plan : RuntimePhasePlan (serviceGraph setup mode))
  {tapeLength : Nat} (prior : PMF (ReservedEpoch.Tape Player tapeLength))

local notation "app" => phaseApplication runtime leaks
local notation "menu" => PhaseCount.onePacketMenu runtime leaks bounds
local notation "horizon" => ReservedEpoch.executionHorizon runtime
local notation "scheduler" => ReactiveApplication.SchedulerImplementation.scheduler
  (ReservedEpoch.implementation runtime leaks (ReservedEpoch.packetCapacity runtime) prior)

variable (values : ∀ who (key : setup.ProposalRecoveryComponent who),
  PMF (setup.CommitRecoveryValueChoice who key.1))

section AliasSampling

local notation "initial" =>
  PMF.map (PhaseRuntimeState.initial plan) (PMF.map encodeInputs setup.initialLaw)

/-- Expand the original response aliases after the ordinary response class.
No support totalization is applied to a table-conditioned value law. -/
def baseAliasPolicy (rates : PhaseProposalRates) (who : Player) : (app).Policy :=
  fun past view =>
    (PhaseProposal.splitResponseLaw runtime leaks bounds who past view
      (phaseProposalBaseClasses setup mode runtime leaks bounds plan values rates who past view)
      rates.aliases.val rates.aliases.property.1 rates.aliases.property.2).map Subtype.val

/-- Zero alias and response flags are precisely the original unflagged policy,
including at inputs where every response is forced to be silent. -/
theorem baseAliasPolicy_zero (who : Player) :
    baseAliasPolicy setup mode runtime leaks bounds plan values PhaseProposalRates.zero who =
      phaseProposalUnflaggedPolicy setup mode runtime leaks bounds plan values who := by
  funext past view
  unfold baseAliasPolicy PhaseProposal.splitResponseLaw phaseProposalUnflaggedPolicy
    phaseProposalUnflaggedResponses
  apply congrArg (PMF.map Subtype.val)
  rw [← PMF.bind_pure_comp]
  apply congrArg (PMF.bind _)
  funext chosen
  exact mix_zero _ _

/-- The concrete counted native policy with the original alias expansion. -/
def baseAliasStrategy (serviceScheduler : (app).Scheduler) (rates : PhaseProposalRates) :
    ∀ who, ((menu).information initial horizon serviceScheduler).BehavioralPolicy who :=
  fun who => (menu).restrictPolicy initial horizon serviceScheduler who
    (baseAliasPolicy setup mode runtime leaks bounds plan values rates who)

open Classical in
/-- The finite table covers every query at an actual native information and
every played enriched-source query. -/
def querySites (serviceScheduler : (app).Scheduler)
    [Fintype ((menu).protocol initial horizon serviceScheduler).History]
    [Fintype setup.proposalRecoveryProtocol.History] :
    Finset ((who : Player) × setup.ProposalRecoveryComponent who) :=
  Finset.univ.biUnion fun who =>
    ((Finset.univ : Finset
      (((menu).protocol initial horizon serviceScheduler).History ×
        (serviceGraph setup mode).EventId)).biUnion fun pair =>
      ((((menu).information initial horizon serviceScheduler).infoOf who pair.1.trace).bind
        fun input =>
          phaseProposalQuery? setup mode runtime leaks plan who pair.2
            input.1 input.2).toFinset).image
          (Sigma.mk who) ∪
    (setup.proposalRecoveryDomainSites who).image (Sigma.mk who)

/-- Evaluate an ordinary value table without changing any other native coin. -/
def tableValues
    (table : ∀ index : (who : Player) × setup.ProposalRecoveryComponent who,
      setup.CommitRecoveryValueChoice index.1 index.2.1)
    (who : Player) (key : setup.ProposalRecoveryComponent who) :
    PMF (setup.CommitRecoveryValueChoice who key.1) :=
  PMF.pure (table ⟨who, key⟩)

open Classical in
/-- Independently sample the finite image of the actual queries. The fallback
is used only outside that image. -/
def sampledValues (serviceScheduler : (app).Scheduler)
    [Fintype ((menu).protocol initial horizon serviceScheduler).History]
    [Fintype setup.proposalRecoveryProtocol.History] :
    PMF (∀ index : (who : Player) × setup.ProposalRecoveryComponent who,
      setup.CommitRecoveryValueChoice index.1 index.2.1) :=
  FiniteAssignment.sampleOn (fun index => values index.1 index.2)
    (querySites setup mode runtime leaks bounds plan serviceScheduler)
    (fun index => Classical.choice (setup.commitRecoveryValueChoice_nonempty index.1 index.2.1))

/-- Run the actual stopped native kernel under a shared ordinary value table. -/
def sampledStopped (serviceScheduler : (app).Scheduler)
    [Fintype ((menu).protocol initial horizon serviceScheduler).History]
    [Fintype setup.proposalRecoveryProtocol.History] (rates : PhaseProposalRates)
    (stopped : ((menu).protocol initial horizon serviceScheduler).History → Prop)
    (start : ((menu).protocol initial horizon serviceScheduler).History) :
    PMF ((menu).protocol initial horizon serviceScheduler).History :=
  (sampledValues setup mode runtime leaks bounds plan values serviceScheduler).bind fun table =>
    ((menu).information initial horizon serviceScheduler).runBehavioralUntil
      ((menu).bounded initial horizon serviceScheduler).wellFoundedHistories
      (baseAliasStrategy setup mode runtime leaks bounds plan
        (tableValues setup table) serviceScheduler rates) stopped start

/-- At an actual unsent binding, the entire raw response law factors through
the queried ordinary value. Every conditional response retains its actual
menu evidence and its typed preparation. -/
theorem baseAliasPolicy_binding_kernel
    (covered : bounds.CoversOutputValues) (serviceScheduler : (app).Scheduler)
    (capacity : horizon ≤ bounds.candidateCount) (remaining : Nat) (who : Player)
    (execution : (app).Execution)
    (trace : ((menu).protocol initial horizon serviceScheduler).Trace
      (some ⟨remaining, some who, execution⟩))
    (event : (serviceGraph setup mode).EventId) (payload : L.Ty)
    (binding : (serviceGraph setup mode).outputLayout event = .binding who payload)
    (request : execution.application.SeedRequest who ⟨execution.application.attempt, event⟩)
    (unsent : ∀ message ∈ (app).outputs (execution.recall who),
      PhaseCount.event? message.payload ≠ some ⟨execution.application.attempt, event⟩)
    (key : setup.ProposalRecoveryComponent who)
    (queried : phaseProposalQuery? setup mode runtime leaks plan who event
      (execution.recall who) (execution.observe app who) = some key) :
    ∃ kernel : setup.CommitRecoveryValueChoice who key.1 → PMF (app).Action,
      (∀ ordinary : ∀ owner (site : setup.ProposalRecoveryComponent owner),
          PMF (setup.CommitRecoveryValueChoice owner site.1),
        baseAliasPolicy setup mode runtime leaks bounds plan ordinary PhaseProposalRates.zero who
            (execution.recall who) (execution.observe app who) =
          (ordinary who key).bind kernel) ∧
      ∀ value response, response ∈ (kernel value).support →
        response ∈ PhaseCount.onePacketActions runtime leaks bounds who
          (execution.recall who) (execution.observe app who) ∧
        ∃ material, response.transmission = some material ∧
          PhaseProposal.bindingPreparation material = some (⟨payload,
            phaseRecoveryDomainValue setup mode event who payload binding value.val.val⟩ :
              Raw L) := by
  classical
  let past := execution.recall who
  let view := execution.observe app who
  have queriedHere : phaseProposalQuery? setup mode runtime leaks plan who event past view =
      some key := queried
  let fallback := fun index : (owner : Player) × setup.ProposalRecoveryComponent owner =>
    Classical.choice (setup.commitRecoveryValueChoice_nonempty index.1 index.2.1)
  let point := fun value : setup.CommitRecoveryValueChoice who key.1 =>
    tableValues setup (FiniteAssignment.setOne fallback ⟨⟨who, key⟩, value⟩)
  have atKey (value : setup.CommitRecoveryValueChoice who key.1) :
      point value who key = PMF.pure value := by
    exact congrArg PMF.pure
      (FiniteAssignment.setOne_same fallback (i := ⟨who, key⟩) value)
  obtain ⟨_draw, native⟩ := phaseNativeInvariant_history runtime leaks plan
    (setup.initialLaw.map encodeInputs) horizon serviceScheduler
      ((menu).toRawTrace initial horizon serviceScheduler trace)
  have dispatch (ordinary : ∀ owner (site : setup.ProposalRecoveryComponent owner),
      PMF (setup.CommitRecoveryValueChoice owner site.1)) :
      phaseProposalBasePolicy setup mode runtime leaks bounds plan ordinary PhaseProposalRates.zero
        who past view =
      PhaseCount.phaseBindingPolicy runtime leaks bounds who event payload
        (phaseProposalBindingResults setup mode runtime leaks plan ordinary PhaseProposalRates.zero
          who event payload binding) past view := by
    unfold phaseProposalBasePolicy
    rw [phasePolicyDispatch_binding setup mode runtime leaks _ _ execution native who event
      payload binding request]
    simp only [PhaseProposalRates.zero, PhaseCount.bindingResultEncoder, mix_zero]
    rfl
  have rawLinear (ordinary : ∀ owner (site : setup.ProposalRecoveryComponent owner),
      PMF (setup.CommitRecoveryValueChoice owner site.1)) :
      phaseProposalBasePolicy setup mode runtime leaks bounds plan ordinary PhaseProposalRates.zero
        who past view =
      (ordinary who key).bind fun value => phaseProposalBasePolicy setup mode runtime leaks bounds
        plan (point value) PhaseProposalRates.zero who past view := by
    simp_rw [dispatch]
    unfold PhaseCount.phaseBindingPolicy
    split
    · exact (PMF.bind_const _ _).symm
    · split
      · simp only [phaseProposalBindingResults, queriedHere, PhaseProposalRates.zero, mix_zero,
          atKey, PMF.pure_map, PMF.map_comp, Function.comp_def]
        exact (PMF.bind_pure_comp _ _).symm
      · exact (PMF.bind_const _ _).symm
  have responsesLinear (ordinary : ∀ owner (site : setup.ProposalRecoveryComponent owner),
      PMF (setup.CommitRecoveryValueChoice owner site.1)) :
      phaseProposalBaseResponses setup mode runtime leaks bounds plan ordinary
        PhaseProposalRates.zero
        who past view =
      (ordinary who key).bind fun value => phaseProposalBaseResponses setup mode runtime leaks
        bounds plan (point value) PhaseProposalRates.zero who past view := by
    apply pmf_map_injective Subtype.val_injective
    rw [phaseProposalBaseResponses_map_val, PMF.map_bind]
    simp_rw [phaseProposalBaseResponses_map_val]
    exact rawLinear ordinary
  let kernel := fun value => baseAliasPolicy setup mode runtime leaks bounds plan (point value)
    PhaseProposalRates.zero who past view
  refine ⟨kernel, ?_, ?_⟩
  · intro ordinary
    simp only [kernel, baseAliasPolicy_zero, phaseProposalUnflaggedPolicy,
      phaseProposalUnflaggedResponses, phaseProposalBaseClasses]
    rw [responsesLinear ordinary]
    simp only [PMF.map_bind]
    rfl
  · intro value response supported
    refine ⟨?_, ?_⟩
    · exact phaseProposalUnflaggedPolicy_covered setup mode runtime leaks bounds plan (point value)
        who past view response (by simpa only [kernel, baseAliasPolicy_zero] using supported)
    have prepared := phaseProposalUnflaggedBinding_preparation_law_of_query setup mode runtime
      leaks bounds plan covered (point value) horizon serviceScheduler capacity remaining who
      execution (by rw [PMF.map_comp] at trace; exact trace) event payload binding request unsent
        key queried
    rw [atKey, PMF.pure_map] at prepared
    have projected := (PMF.mem_support_map_iff
      (fun action : (app).Action => action.transmission.bind PhaseProposal.bindingPreparation)
        _ _).mpr ⟨response, (by simpa only [kernel, baseAliasPolicy_zero] using supported), rfl⟩
    rw [prepared, PMF.mem_support_pure_iff] at projected
    cases emitted : response.transmission with
    | none => simp only [emitted, Option.bind_none] at projected; cases projected
    | some material =>
        exact ⟨material, rfl, by simpa only [emitted, Option.bind_some] using projected⟩

section Sampling

local notation "SE" schedule:max => ReactiveApplication.ResponseMenu.protocol
  (PhaseCount.onePacketMenu runtime leaks bounds) initial horizon schedule
local notation "SN" schedule:max => ReactiveApplication.ResponseMenu.information
  (PhaseCount.onePacketMenu runtime leaks bounds) initial horizon schedule

private theorem binding_step_kernel
    (serviceScheduler : (phaseApplication runtime leaks).Scheduler)
    (covered : bounds.CoversOutputValues) (capacity : horizon ≤ bounds.candidateCount)
    (control : (app).Control) (trace : (SE serviceScheduler).Trace (some control))
    (who : Player) (active : control.actor = some who)
    (event : (serviceGraph setup mode).EventId) (payload : L.Ty)
    (binding : (serviceGraph setup mode).outputLayout event = .binding who payload)
    (request : control.execution.application.SeedRequest who
      ⟨control.execution.application.attempt, event⟩)
    (unsent : ∀ message ∈ (app).outputs (control.execution.recall who),
      PhaseCount.event? message.payload ≠ some ⟨control.execution.application.attempt, event⟩)
    (key : setup.ProposalRecoveryComponent who)
    (queried : phaseProposalQuery? setup mode runtime leaks plan who event
      (control.execution.recall who) (control.execution.observe app who) = some key) :
    ∃ nextLaw : setup.CommitRecoveryValueChoice who key.1 → PMF (SE serviceScheduler).History,
      (∀ table, (SN serviceScheduler).runBehavioralFrom
        (baseAliasStrategy setup mode runtime leaks bounds plan (tableValues setup table)
          serviceScheduler PhaseProposalRates.zero) 1 ⟨some control, trace⟩ =
        nextLaw (table ⟨who, key⟩)) ∧
      (SN serviceScheduler).runBehavioralFrom
          (baseAliasStrategy setup mode runtime leaks bounds plan values serviceScheduler
            PhaseProposalRates.zero) 1 ⟨some control, trace⟩ = (values who key).bind nextLaw ∧
      ∀ value next, next ∈ (nextLaw value).support →
        ∃ ending, next.state = some ending ∧ TracePrefix trace next.trace ∧
          (SE serviceScheduler).HistorySuccessor next ⟨some control, trace⟩ ∧
          ∃ entry ∈ ending.execution.recall who, ∃ material candidate,
            entry.action.transmission = some material ∧
            material.call.packet = .commitment event candidate ∧
            (⟨some material⟩ : (app).Action) ∈ PhaseCount.onePacketActions runtime leaks bounds who
              (control.execution.recall who) (control.execution.observe app who) ∧
            phaseProposalQuery? setup mode runtime leaks plan who event
              (control.execution.recall who) entry.beforeView = some key := by
  classical
  let profile := fun table => baseAliasStrategy setup mode runtime leaks bounds plan
    (tableValues setup table) serviceScheduler PhaseProposalRates.zero
  let baseline := baseAliasStrategy setup mode runtime leaks bounds plan values serviceScheduler
    PhaseProposalRates.zero
  let selected : (owner : Player) × setup.ProposalRecoveryComponent owner := ⟨who, key⟩
  have controlEq : control = ⟨control.remaining, some who, control.execution⟩ := by
    cases control
    cases active
    rfl
  have activeTrace : (SE serviceScheduler).Trace
      (some ⟨control.remaining, some who, control.execution⟩) := controlEq ▸ trace
  have terminal : ¬ (SE serviceScheduler).terminal (some control) := by
    change ¬ (control.remaining = 0 ∧ control.actor = none)
    rintro ⟨_, inactive⟩
    rw [active] at inactive
    cases inactive
  obtain ⟨kernel, linear, kernelFacts⟩ := baseAliasPolicy_binding_kernel setup mode runtime
    leaks bounds plan covered serviceScheduler capacity control.remaining who control.execution
      activeTrace event payload binding request unsent key queried
  have info (owner : Player) : (SN serviceScheduler).infoOf owner trace =
      if owner = who then some (control.execution.recall who,
        control.execution.observe app who) else none := by
    change ((menu).signals initial horizon serviceScheduler).infoOf owner trace = _
    rw [(menu).info]
    simp only [ReactiveApplication.observe, active, Option.some.injEq]
    by_cases own : owner = who
    · subst owner
      rw [ite_eq_left rfl]
    · rw [ite_eq_right (Ne.symm own), ite_eq_right own]
  have singleStep (first second : ∀ owner, (SN serviceScheduler).BehavioralPolicy owner)
      (agree : ∀ owner, first owner ((SN serviceScheduler).infoOf owner trace) =
        second owner ((SN serviceScheduler).infoOf owner trace)) :
      (SN serviceScheduler).runBehavioralFrom first 1 ⟨some control, trace⟩ =
        (SN serviceScheduler).runBehavioralFrom second 1 ⟨some control, trace⟩ := by
    rw [(SN serviceScheduler).runBehavioralFrom_one_localStep,
      (SN serviceScheduler).runBehavioralFrom_one_localStep]
    have currentLaws : (fun owner => first owner ((SN serviceScheduler).infoOf owner trace)) =
        (fun owner => second owner ((SN serviceScheduler).infoOf owner trace)) :=
      funext agree
    rw [currentLaws]
  let alternatives := fun value => (menu).restrictPolicy initial horizon serviceScheduler
    who (fun _ _ => kernel value)
  let pointProfile := fun value => Profile.update
    (sig := (SN serviceScheduler).behavioralSignature)
    baseline who (alternatives value)
  let nextLaw := fun value => (SN serviceScheduler).runBehavioralFrom (pointProfile value) 1
    ⟨some control, trace⟩
  have currentChoice (table) : profile table who ((SN serviceScheduler).infoOf who trace) =
      alternatives (table selected) ((SN serviceScheduler).infoOf who trace) := by
    rw [info who, ite_eq_left rfl]
    apply (menu).restrictPolicy_eq_of_law_eq
    simpa only [tableValues, PMF.pure_bind] using linear (tableValues setup table)
  have tableStep (table) : (SN serviceScheduler).runBehavioralFrom (profile table) 1
      ⟨some control, trace⟩ = nextLaw (table selected) := by
    dsimp only [nextLaw]
    apply singleStep
    intro owner
    by_cases own : owner = who
    · subst owner
      simpa only [pointProfile, Profile.update_same] using currentChoice table
    · dsimp only [pointProfile]
      rw [Profile.update_of_ne _ _ own, info owner, ite_eq_right own]
      simp only [profile, baseline, baseAliasStrategy,
        ReactiveApplication.ResponseMenu.restrictPolicy]
  have choiceMix : baseline who ((SN serviceScheduler).infoOf who trace) =
      (values who key).bind (fun value =>
        alternatives value ((SN serviceScheduler).infoOf who trace)) := by
    rw [info who, ite_eq_left rfl]
    dsimp only [baseline, baseAliasStrategy, alternatives]
    apply pmf_map_injective Subtype.val_injective
    rw [(menu).restrictPolicy_map_val initial horizon serviceScheduler who _ _ _
      (by intro response supported
          rw [baseAliasPolicy_zero] at supported
          exact phaseProposalUnflaggedPolicy_covered setup mode runtime leaks bounds plan
            values who _ _ response supported), PMF.map_bind]
    rw [linear values, PMF.map_bind]
    apply bind_congr_on_support
    intro value _
    symm
    exact (menu).restrictPolicy_map_val initial horizon serviceScheduler who
      (fun _ _ => kernel value) (control.execution.recall who)
      (control.execution.observe app who)
      (fun response supported => (kernelFacts value response supported).1)
  have chooserMix : (SN serviceScheduler).behavioralJoint baseline trace terminal =
      (values who key).bind (fun value =>
        (SN serviceScheduler).behavioralJoint (pointProfile value) trace terminal) := by
    rw [← (SN serviceScheduler).behavioralJoint_update_bind baseline who (values who key)
      alternatives]
    apply (SN serviceScheduler).behavioralJoint_congr
    intro owner
    by_cases own : owner = who
    · subst owner
      simpa only [Profile.update_same] using choiceMix
    · simp only [Profile.update_of_ne _ _ own]
  have stepMix : (SN serviceScheduler).runBehavioralFrom baseline 1 ⟨some control, trace⟩ =
      (values who key).bind nextLaw := by
    dsimp only [nextLaw]
    rw [(SN serviceScheduler).runBehavioralFrom_succ_of_not_terminal _ 0 terminal,
      chooserMix,
      PMF.bind_bind]
    apply bind_congr_on_support
    intro value _
    rw [(SN serviceScheduler).runBehavioralFrom_succ_of_not_terminal _ 0 terminal]
    simp only [InformationModel.runBehavioralFrom, ExecutionProtocol.runRandomizedFor_zero]
  refine ⟨nextLaw, tableStep, stepMix, ?_⟩
  intro value next reached
  have nextStep := (SN serviceScheduler).mem_support_runBehavioralFrom_one (pointProfile value)
    terminal reached
  dsimp only [nextLaw] at reached
  have tracePrefix : TracePrefix trace next.trace := by
    rw [(SN serviceScheduler).runBehavioralFrom_one_localStep,
      PMF.mem_support_bind_iff] at reached
    obtain ⟨choices, _, moved⟩ := reached
    simp only [InformationModel.localStep, dite_eq_right terminal,
      PMF.mem_support_bindOnSupport_iff] at moved
    obtain ⟨target, actual, exactNext⟩ := moved
    cases (PMF.mem_support_pure_iff _ _).mp exactNext
    exact .extend .refl _ _ actual
  have decoded : (menu).decodeProfile initial horizon serviceScheduler
      (pointProfile value) who (control.execution.recall who)
        (control.execution.observe app who) = kernel value := by
    simp only [ReactiveApplication.ResponseMenu.decodeProfile, pointProfile,
      Profile.update_same, alternatives]
    change (((menu).embedPolicy initial horizon serviceScheduler who
      ((menu).restrictPolicy initial horizon serviceScheduler who
        (fun _ _ => kernel value))) (some (control.execution.recall who,
        control.execution.observe app who))).map _ = _
    rw [(menu).embed_restrictPolicy initial horizon serviceScheduler who _ _ _
      (fun response supported => (kernelFacts value response supported).1)]
    simp only [ReactiveApplication.encodePolicy, PMF.map_comp, Function.comp_def,
      Option.getD_some]
    exact PMF.map_id _
  have projected : next.state ∈ ((nextLaw value).map History.state).support :=
    (PMF.mem_support_map_iff _ _ _).mpr ⟨next, reached, rfl⟩
  dsimp only [nextLaw] at projected
  rw [(menu).run_one_response initial horizon serviceScheduler (pointProfile value)
    ⟨some control, trace⟩ who control.remaining control.execution
      (congrArg some controlEq), decoded] at projected
  obtain ⟨response, drawn, nextState⟩ := (PMF.mem_support_map_iff _ _ _).mp projected
  obtain ⟨offered, material, transmitted, _prepared⟩ := kernelFacts value response drawn
  have responseEq : response = ⟨some material⟩ := by
    cases response
    exact congrArg ReactiveApplication.Action.mk transmitted
  obtain ⟨serial, _preparation, _evidence, materialEq, _bounded, _freshSlot⟩ :=
    PhaseCount.onePacket_binding_shape runtime leaks bounds plan
      (serviceGraph_revealRelaxedOrdered setup mode) (setup.initialLaw.map encodeInputs)
      horizon serviceScheduler control.remaining who control.execution activeTrace
      event payload binding request material (responseEq ▸ offered)
  refine ⟨_, nextState.symm, tracePrefix, nextStep.1, ?_⟩
  rw [responseEq]
  simp only [ReactiveApplication.Execution.respond]
  refine ⟨_, List.mem_append_right _ (List.mem_singleton_self _), material,
    (who, .prepared serial), rfl, ?_, responseEq ▸ offered, queried⟩
  rw [materialEq]

/-- Predrawing ordinary values preserves the complete native history law up
to the first exit from the original commitment attempt. Values stored before
the starting history remain literal; the table supplies only new SENDs. -/
theorem sampled_base_stopped_marginal
    (serviceScheduler : (phaseApplication runtime leaks).Scheduler)
    [Fintype (SE serviceScheduler).History] [Fintype setup.proposalRecoveryProtocol.History]
    (complete : leaks = MessageNetwork.completePendingObservation)
    (covered : bounds.CoversOutputValues)
    (maximal : plan.phases.IsChain fun first last =>
      first.kind ≠ last.kind ∨ first.kind = .sample)
    (capacity : horizon ≤ bounds.candidateCount)
    (origin : (app).Control) (originTrace : (SE serviceScheduler).Trace (some origin))
    (phase : RuntimePhase (serviceGraph setup mode))
    (installed : phase ∈ origin.execution.application.phases.head?)
    (commitment : phase.kind = .commitment) :
    sampledStopped setup mode runtime leaks bounds plan values serviceScheduler
        PhaseProposalRates.zero
        (fun stop : (SE serviceScheduler).History => match stop.state with
          | some ending => ending.execution.application.attempt ≠
              origin.execution.application.attempt
          | none => False) ⟨some origin, originTrace⟩ =
      (SN serviceScheduler).runBehavioralUntil
        ((menu).bounded initial horizon serviceScheduler).wellFoundedHistories
        (baseAliasStrategy setup mode runtime leaks bounds plan values serviceScheduler
          PhaseProposalRates.zero)
        (fun stop : (SE serviceScheduler).History => match stop.state with
          | some ending => ending.execution.application.attempt ≠
              origin.execution.application.attempt
          | none => False) ⟨some origin, originTrace⟩ := by
  classical
  let sites := querySites setup mode runtime leaks bounds plan serviceScheduler
  let fallback := fun index : (owner : Player) × setup.ProposalRecoveryComponent owner =>
    Classical.choice (setup.commitRecoveryValueChoice_nonempty index.1 index.2.1)
  let original := fun index : (owner : Player) × setup.ProposalRecoveryComponent owner =>
    values index.1 index.2
  let profile := fun table => baseAliasStrategy setup mode runtime leaks bounds plan
    (tableValues setup table) serviceScheduler PhaseProposalRates.zero
  let baseline := baseAliasStrategy setup mode runtime leaks bounds plan values serviceScheduler
    PhaseProposalRates.zero
  let halt := fun stop : (SE serviceScheduler).History => match stop.state with
    | some ending => ending.execution.application.attempt ≠ origin.execution.application.attempt
    | none => False
  let certificate := ((menu).bounded initial horizon serviceScheduler).wellFoundedHistories
  let finished := fun policies => (SN serviceScheduler).runBehavioralUntil certificate policies halt
  let consumed := fun (history : (SE serviceScheduler).History)
      (index : (owner : Player) × setup.ProposalRecoveryComponent owner) =>
    ∀ control, history.state = some control →
      ∃ (entry : (app).PlayerEntry), entry ∈ control.execution.recall index.1 ∧
      ∃ (material : WitnessedSubmission (serviceGraph setup mode))
        (event : (serviceGraph setup mode).EventId) (candidate : Handle (serviceGraph setup mode))
        (payload : L.Ty) (oldPast : List (app).PlayerEntry),
        entry.action.transmission = some material ∧
        material.call.packet = .commitment event candidate ∧
        (serviceGraph setup mode).outputLayout event = .binding index.1 payload ∧
        phaseProposalQuery? setup mode runtime leaks plan index.1 event oldPast entry.beforeView =
          some index.2
  have residual : ∀ history : (SE serviceScheduler).History, ∀ control,
      history.state = some control → TracePrefix originTrace history.trace →
      ∀ (laws : ∀ index : (owner : Player) × setup.ProposalRecoveryComponent owner,
          PMF (setup.CommitRecoveryValueChoice index.1 index.2.1))
        (used : Finset ((owner : Player) × setup.ProposalRecoveryComponent owner)),
      (∀ index, index ∉ used → laws index = original index) →
      (∀ index ∈ used, consumed history index) →
      (FiniteAssignment.sampleOn laws sites fallback).bind (fun table =>
        finished (profile table) history) = finished baseline history := by
    intro history
    induction history using certificate.induction with
    | _ history ih =>
      intro control stateEq kept laws used untouched recorded
      by_cases stopped : halt history
      · have atStop (policies) : finished policies history = PMF.pure history :=
          (SN serviceScheduler).runBehavioralUntil_of_stopped certificate policies stopped
        simp_rw [atStop]
        exact PMF.bind_const _ _
      by_cases terminal : (SE serviceScheduler).terminal history.state
      · have atTerminal (policies) : finished policies history = PMF.pure history :=
          (SN serviceScheduler).runBehavioralUntil_of_terminal certificate policies terminal
        simp_rw [atTerminal]
        exact PMF.bind_const _ _
      rcases history with ⟨state, trace⟩
      dsimp only at stateEq
      subst state
      have same : origin.execution.application.attempt = control.execution.application.attempt := by
        exact (not_ne_iff.mp stopped).symm
      have metadata := phaseProposal_same_attempt_archive_metadata setup mode runtime leaks bounds
        plan horizon serviceScheduler origin control originTrace trace kept same
      have currentPhase : phase ∈ control.execution.application.phases.head? := by
        rwa [metadata.1]
      have retained (next : (SE serviceScheduler).History)
          (tracePrefix : TracePrefix trace next.trace) :
          ∀ index ∈ used, consumed next index := by
        intro index member ending endingEq
        obtain ⟨entry, present, rest⟩ := recorded index member control rfl
        have recalls := (app).reaches_recall_prefix initial horizon serviceScheduler
          ((menu).reaches_raw initial horizon serviceScheduler tracePrefix.reachesWithin)
          control ending rfl endingEq index.1
        exact ⟨entry, recalls.subset present, rest⟩
      have unchanged (stepLaw : PMF (SE serviceScheduler).History)
          (pointwise : ∀ table, (SN serviceScheduler).runBehavioralFrom (profile table) 1
            ⟨some control, trace⟩ = stepLaw)
          (ordinary : (SN serviceScheduler).runBehavioralFrom baseline 1
            ⟨some control, trace⟩ = stepLaw) :
          (FiniteAssignment.sampleOn laws sites fallback).bind (fun table =>
            finished (profile table) ⟨some control, trace⟩) =
          finished baseline ⟨some control, trace⟩ := by
        simp_rw [finished,
          (SN serviceScheduler).runBehavioralUntil_of_running certificate _ stopped terminal,
          pointwise]
        rw [PMF.bind_comm]
        rw [ordinary]
        apply bind_congr_on_support
        intro next reached
        have nextStep := (SN serviceScheduler).mem_support_runBehavioralFrom_one baseline terminal
          (ordinary.symm ▸ reached)
        have tracePrefix : TracePrefix trace next.trace := by
          have actualReached := ordinary.symm ▸ reached
          rw [(SN serviceScheduler).runBehavioralFrom_one_localStep,
            PMF.mem_support_bind_iff] at actualReached
          obtain ⟨choices, _, moved⟩ := actualReached
          simp only [InformationModel.localStep, dite_eq_right terminal,
            PMF.mem_support_bindOnSupport_iff] at moved
          obtain ⟨target, actual, exactNext⟩ := moved
          cases (PMF.mem_support_pure_iff _ _).mp exactNext
          exact .extend .refl _ _ actual
        have rawStep := nextStep.1
        obtain ⟨joint, legal, realized⟩ := rawStep
        have moved := realized
        change next.state ∈ ((app).transition initial horizon serviceScheduler
          (some control) joint).support at moved
        obtain ⟨ending, endingEq, _⟩ := (app).transition_recall_prefix initial horizon
          serviceScheduler control next.state joint moved
        exact ih next nextStep.1 ending endingEq (kept.trans tracePrefix) laws used untouched
          (retained next tracePrefix)
      have singleStep (first second : ∀ owner, (SN serviceScheduler).BehavioralPolicy owner)
          (agree : ∀ owner, first owner ((SN serviceScheduler).infoOf owner trace) =
            second owner ((SN serviceScheduler).infoOf owner trace)) :
          (SN serviceScheduler).runBehavioralFrom first 1 ⟨some control, trace⟩ =
            (SN serviceScheduler).runBehavioralFrom second 1 ⟨some control, trace⟩ := by
        rw [(SN serviceScheduler).runBehavioralFrom_one_localStep,
          (SN serviceScheduler).runBehavioralFrom_one_localStep]
        have currentLaws : (fun owner => first owner ((SN serviceScheduler).infoOf owner trace)) =
            (fun owner => second owner ((SN serviceScheduler).infoOf owner trace)) :=
          funext agree
        rw [currentLaws]
      cases active : control.actor with
      | none =>
        apply unchanged ((SN serviceScheduler).runBehavioralFrom baseline 1
          ⟨some control, trace⟩) _ rfl
        intro table
        apply singleStep
        intro owner
        have observed := (menu).info initial horizon serviceScheduler owner trace
        change (SN serviceScheduler).infoOf owner trace = _ at observed
        simp only [ReactiveApplication.observe, active, reduceCtorEq, ↓reduceIte] at observed
        rw [observed]
        simp only [profile, baseline, baseAliasStrategy,
          ReactiveApplication.ResponseMenu.restrictPolicy]
      | some who =>
        have controlEq : control = ⟨control.remaining, some who, control.execution⟩ := by
          cases control
          cases active
          rfl
        have info (owner : Player) : (SN serviceScheduler).infoOf owner trace =
            if owner = who then some (control.execution.recall who,
              control.execution.observe app who) else none := by
          change ((menu).signals initial horizon serviceScheduler).infoOf owner trace = _
          rw [(menu).info]
          simp only [ReactiveApplication.observe, active, Option.some.injEq]
          by_cases own : owner = who
          · subst owner
            rw [ite_eq_left rfl]
          · rw [ite_eq_right (Ne.symm own), ite_eq_right own]
        by_cases eligible : ∃ coordinate, control.execution.application.SeedRequest who coordinate ∧
            ∀ message ∈ (app).outputs (control.execution.recall who),
              PhaseCount.event? message.payload ≠ some coordinate
        · obtain ⟨coordinate, request, unsent⟩ := eligible
          obtain ⟨current, present, inside⟩ := request.2.1
          have currentEq : current = phase := by
            rw [Option.mem_def] at present currentPhase
            exact Option.some.inj (present.symm.trans currentPhase)
          subst current
          have limits := (phase.mem_events coordinate.event).mp inside
          have field := phase.fields coordinate.event limits.1 limits.2
          rw [commitment] at field
          obtain ⟨owner, payload, binding⟩ := field
          have typed :=
            ((serviceGraph setup mode).nodes coordinate.event).output_public_or_binding_of_actor
              who request.2.2.2.1
          have ownerEq : owner = who := by
            rcases typed with publicField | ⟨kind, ownField⟩
            · rw [binding] at publicField
              cases publicField
            · cases binding.symm.trans ownField
              rfl
          subst owner
          have coordinateEq : coordinate =
              ⟨control.execution.application.attempt, coordinate.event⟩ := by
            cases coordinate with
            | mk attempt event =>
                exact congrArg (fun nextAttempt => CommitAttemptEvent.mk nextAttempt event)
                  request.1
          rw [coordinateEq] at request unsent
          have activeTrace : (SE serviceScheduler).Trace
              (some ⟨control.remaining, some who, control.execution⟩) := by
            exact controlEq ▸ trace
          obtain ⟨key, queried⟩ : ∃ key, phaseProposalQuery? setup mode runtime leaks plan who
              coordinate.event (control.execution.recall who) (control.execution.observe app who) =
                some key := by
            have raw := (menu).toRawTrace initial horizon serviceScheduler activeTrace
            rw [PMF.map_comp] at raw
            obtain ⟨_source, _sourceTrace, _acting, _rank, _decision, query⟩ :=
              phaseProposalQuery?_genuine_base setup mode runtime leaks complete plan maximal
                horizon serviceScheduler raw who rfl coordinate.event payload binding request
            exact ⟨_, query⟩
          obtain ⟨nextLaw, tableStep, stepMix, nextFacts⟩ := binding_step_kernel setup mode runtime
            leaks bounds plan values serviceScheduler covered capacity control trace who active
              coordinate.event payload binding request unsent key queried
          let selected : (owner : Player) × setup.ProposalRecoveryComponent owner := ⟨who, key⟩
          change (∀ table, (SN serviceScheduler).runBehavioralFrom (profile table) 1
            ⟨some control, trace⟩ = nextLaw (table selected)) at tableStep
          change (SN serviceScheduler).runBehavioralFrom baseline 1 ⟨some control, trace⟩ =
            (values who key).bind nextLaw at stepMix
          have inSites : selected ∈ sites := by
            apply Finset.mem_biUnion.mpr
            refine ⟨who, Finset.mem_univ _, ?_⟩
            apply Finset.mem_union_left
            apply Finset.mem_image.mpr
            refine ⟨key, ?_, rfl⟩
            apply Finset.mem_biUnion.mpr
            refine ⟨(⟨some control, trace⟩, coordinate.event), Finset.mem_univ _, ?_⟩
            simp only [info who, ite_true, Option.bind_some, queried, Option.mem_toFinset,
              Option.mem_def]
          have fresh : selected ∉ used := by
            intro member
            obtain ⟨entry, present, material, event, candidate, oldPayload, oldPast,
              oldSent, oldNamed, oldBinding, oldQuery⟩ := recorded selected member control rfl
            let value := Classical.choice (setup.commitRecoveryValueChoice_nonempty who key.1)
            obtain ⟨next, positive⟩ := (nextLaw value).support_nonempty
            obtain ⟨_ending, _state, _prefix, _step, _entry, _present, currentMaterial,
              _candidate, _sent, _named, offered, _query⟩ := nextFacts value next positive
            have different := phaseProposalQuery_ne_of_recalled_binding_send setup mode runtime
              leaks bounds plan maximal horizon serviceScheduler control.remaining who
              control.execution activeTrace entry present material oldSent event candidate oldNamed
                oldPayload oldBinding coordinate.event payload binding request currentMaterial
                offered oldPast key key oldQuery queried
            exact different rfl
          let committed := fun value => Function.update laws selected (PMF.pure value)
          have committedAt (value) : committed value selected = PMF.pure value :=
            Function.update_self _ _ _
          have factor := FiniteAssignment.sampleOn_factor_of_mem laws sites fallback inSites
            committed committedAt (fun value index different => Function.update_of_ne different _ _)
          rw [factor, PMF.bind_bind, untouched selected fresh]
          rw [show finished baseline ⟨some control, trace⟩ =
              (values who key).bind (fun value => (nextLaw value).bind (finished baseline)) by
            dsimp only [finished]
            rw [(SN serviceScheduler).runBehavioralUntil_of_running certificate _ stopped terminal,
              stepMix, PMF.bind_bind]]
          apply bind_congr_on_support
          intro value _
          have fixed (table) (positive : table ∈
              (FiniteAssignment.sampleOn (committed value) sites fallback).support) :
              table selected = value := by
            have projected := (PMF.mem_support_map_iff (fun table => table selected) _ _).mpr
              ⟨table, positive, rfl⟩
            rw [FiniteAssignment.sampleOn_map_eval_of_mem _ _ _ inSites, committedAt,
              PMF.mem_support_pure_iff] at projected
            exact projected
          calc
            _ = (FiniteAssignment.sampleOn (committed value) sites fallback).bind
                (fun table => (nextLaw value).bind (finished (profile table))) := by
              apply bind_congr_on_support
              intro table positive
              dsimp only [finished]
              rw [(SN serviceScheduler).runBehavioralUntil_of_running certificate _ stopped
                  terminal,
                tableStep, fixed table positive]
            _ = (nextLaw value).bind (fun next =>
                (FiniteAssignment.sampleOn (committed value) sites fallback).bind
                  (fun table => finished (profile table) next)) := PMF.bind_comm _ _ _
            _ = _ := by
              apply bind_congr_on_support
              intro next reached
              obtain ⟨ending, endingEq, tracePrefix, nextStep, entry, present, material,
                candidate, sent, named, _offered, queried⟩ := nextFacts value next reached
              refine ih next nextStep ending endingEq (kept.trans tracePrefix)
                (committed value) (insert selected used) ?_ ?_
              · intro index notUsed
                have different : index ≠ selected := fun equal =>
                  notUsed (Finset.mem_insert.mpr (Or.inl equal))
                dsimp only [committed]
                rw [Function.update_of_ne different]
                exact untouched index (fun member => notUsed (Finset.mem_insert_of_mem member))
              · intro index member
                rcases Finset.mem_insert.mp member with equal | old
                · subst index
                  intro current currentEq
                  cases Option.some.inj (currentEq.symm.trans endingEq)
                  exact ⟨entry, present, material, coordinate.event, candidate, payload,
                    control.execution.recall who, sent, named, binding, queried⟩
                · exact retained next tracePrefix index old
        · have onlyWait := PhaseCount.onePacketActions_eq_singleton_of_no_unsent runtime leaks
            bounds plan (serviceGraph_revealRelaxedOrdered setup mode)
            (setup.initialLaw.map encodeInputs) horizon serviceScheduler control.remaining who
            control.execution (controlEq ▸ trace) eligible
          have rawWait (ordinary : ∀ owner (site : setup.ProposalRecoveryComponent owner),
              PMF (setup.CommitRecoveryValueChoice owner site.1)) :
              baseAliasPolicy setup mode runtime leaks bounds plan ordinary PhaseProposalRates.zero
                who (control.execution.recall who) (control.execution.observe app who) =
              PMF.pure ⟨none⟩ := by
            rw [baseAliasPolicy_zero]
            apply phaseProposalUnflaggedPolicy_forced_wait
            intro response offered
            exact Finset.mem_singleton.mp (onlyWait ▸ offered)
          apply unchanged ((SN serviceScheduler).runBehavioralFrom baseline 1
            ⟨some control, trace⟩) _ rfl
          intro table
          apply singleStep
          intro owner
          rw [info owner]
          by_cases own : owner = who
          · subst owner
            rw [ite_eq_left rfl]
            apply (menu).restrictPolicy_eq_of_law_eq
            rw [rawWait, rawWait]
          · rw [ite_eq_right own]
            simp only [profile, baseline, baseAliasStrategy,
              ReactiveApplication.ResponseMenu.restrictPolicy]
  exact residual ⟨some origin, originTrace⟩ origin rfl .refl original ∅
    (by intro index _; rfl) (by simp)

end Sampling

end AliasSampling

local notation "initial" =>
  setup.initialLaw.map (fun draw => PhaseRuntimeState.initial plan (encodeInputs draw))
local notation "E" => ReactiveApplication.ResponseMenu.protocol
  (PhaseCount.onePacketMenu runtime leaks bounds) initial horizon scheduler
local notation "N" => ReactiveApplication.ResponseMenu.information
  (PhaseCount.onePacketMenu runtime leaks bounds) initial horizon scheduler

/-- Zero future flags use the original ordinary value table. -/
def unflaggedStrategy : ∀ who, (N).BehavioralPolicy who :=
  fun who => (menu).restrictPolicy initial horizon scheduler who
    (phaseProposalUnflaggedPolicy setup mode runtime leaks bounds plan values who)

local notation "plain" => unflaggedStrategy setup mode runtime leaks bounds plan prior values

open Classical in
/-- One actual response, with the chosen atom committed at this history's
actual information. Subsequent play is defined separately. -/
def currentStep (who : Player) (history : (E).History)
    (choice : (N).Choice who ((N).infoOf who history.trace)) : PMF (E).History :=
  (N).runBehavioralFrom
    (Profile.update (sig := (N).behavioralSignature) plain who
      ((plain who).commit ((N).infoOf who history.trace) choice)) 1 history

/-- The literal atom has exactly its native physical response image. -/
theorem currentStep_state (who : Player) (history : (E).History)
    (choice : (N).Choice who ((N).infoOf who history.trace))
    (remaining : Nat) (execution : (app).Execution)
    (current : history.state = some ⟨remaining, some who, execution⟩)
    (response : (app).Action) (selected : choice.1 = some response) :
    (currentStep setup mode runtime leaks bounds plan prior values who history choice).map
      History.state = PMF.pure (some ⟨remaining, none, execution.respond app who response⟩) := by
  exact (menu).run_commit_response initial horizon scheduler plain history who remaining
    execution current choice response selected

/-- The first exit compares namespaces to the original current history. -/
def attemptExit (start stop : (E).History) : Prop :=
  match start.state, stop.state with
  | some before, some after =>
      after.execution.application.attempt ≠ before.execution.application.attempt
  | _, _ => False

/-- Retain the first attempt exit and finish from that same full history. -/
def stoppedFinish (who : Player) (history : (E).History)
    (choice : (N).Choice who ((N).infoOf who history.trace)) :
    PMF ((E).History × (E).History) :=
  (currentStep setup mode runtime leaks bounds plan prior values who history choice).bind
    fun after =>
      ((N).runBehavioralUntil ((menu).bounded initial horizon scheduler).wellFoundedHistories plain
        (attemptExit setup mode runtime leaks bounds plan prior history) after).bind fun stop =>
          ((N).runBehavioralTerminalFrom
            ((menu).bounded initial horizon scheduler).wellFoundedHistories plain stop).map
              fun terminal => (stop, terminal)

/-- Erasing the recorded exit gives exactly the original postresponse terminal
law. In particular stopping does not redraw a tape or an initial input. -/
theorem stoppedFinish_terminal (who : Player) (history : (E).History)
    (choice : (N).Choice who ((N).infoOf who history.trace)) :
    (stoppedFinish setup mode runtime leaks bounds plan prior values who history choice).map
        Prod.snd =
      (currentStep setup mode runtime leaks bounds plan prior values who history choice).bind
        ((N).runBehavioralTerminalFrom
          ((menu).bounded initial horizon scheduler).wellFoundedHistories plain) := by
  unfold stoppedFinish
  rw [PMF.map_bind]
  apply bind_congr_on_support
  intro after _
  rw [PMF.map_bind]
  calc
    _ = ((N).runBehavioralUntil
        ((menu).bounded initial horizon scheduler).wellFoundedHistories plain
        (attemptExit setup mode runtime leaks bounds plan prior history) after).bind
          ((N).runBehavioralTerminalFrom
            ((menu).bounded initial horizon scheduler).wellFoundedHistories plain) := by
      apply bind_congr_on_support
      intro stop _
      calc
        _ = ((N).runBehavioralTerminalFrom
            ((menu).bounded initial horizon scheduler).wellFoundedHistories plain stop).map id :=
          PMF.map_comp _ _ _
        _ = _ := PMF.map_id _
    _ = _ := ((N).runBehavioralTerminalFrom_eq_bind_runBehavioralUntil
      ((menu).bounded initial horizon scheduler).wellFoundedHistories plain
      (attemptExit setup mode runtime leaks bounds plan prior history) after).symm

/-- The stopped experiment's terminal physical marginal is the actual native
finish after the literal current response, under the original scheduler. -/
theorem stoppedFinish_state (who : Player) (history : (E).History)
    (choice : (N).Choice who ((N).infoOf who history.trace))
    (remaining : Nat) (execution : (app).Execution)
    (current : history.state = some ⟨remaining, some who, execution⟩)
    (response : (app).Action) (selected : choice.1 = some response) :
    (stoppedFinish setup mode runtime leaks bounds plan prior values who history choice).map
        (fun result => result.2.state) =
      (app).finish initial horizon scheduler
        ((menu).decodeProfile initial horizon scheduler plain)
        (some ⟨remaining, none, execution.respond app who response⟩) := by
  calc
    _ = ((stoppedFinish setup mode runtime leaks bounds plan prior values who history choice).map
        Prod.snd).map History.state := (PMF.map_comp _ _ _).symm
    _ = _ := by
      rw [stoppedFinish_terminal]
      have finish := phaseProposal_response_kernel_finish setup mode runtime leaks bounds plan prior
      rw [PMF.map_comp] at finish
      exact finish plain
        (fun _ => currentStep setup mode runtime leaks bounds plan prior values who history choice)
        remaining who execution response
        (currentStep_state setup mode runtime leaks bounds plan prior values who history choice
          remaining execution current response selected)

/-- Disintegrating the same terminal marginal uses the scheduler posterior
at the original callback, including all its earlier environment observations. -/
theorem stoppedFinish_seed_marginal (who : Player) (history : (E).History)
    (choice : (N).Choice who ((N).infoOf who history.trace))
    (remaining : Nat) (execution : (app).Execution)
    (current : history.state = some ⟨remaining, some who, execution⟩)
    (response : (app).Action) (selected : choice.1 = some response) :
    (stoppedFinish setup mode runtime leaks bounds plan prior values who history choice).map
        (fun result => result.2.state) =
      (((app).schedulerMixture prior
        (ReservedEpoch.family runtime leaks (ReservedEpoch.packetCapacity runtime))).posterior
          execution.environmentRecall).bind fun tape =>
        (app).finish initial horizon
          (ReservedEpoch.family runtime leaks (ReservedEpoch.packetCapacity runtime) tape)
          ((menu).decodeProfile initial horizon scheduler plain)
          (some ⟨remaining, none, execution.respond app who response⟩) := by
  rw [stoppedFinish_state setup mode runtime leaks bounds plan prior values who history choice
    remaining execution current response selected]
  simpa only [PMF.pure_bind, PMF.map_comp, Function.comp_def] using
    (phaseProposal_current_finish_seed_marginal setup mode runtime leaks plan prior
      ((menu).decodeProfile initial horizon scheduler plain) remaining who execution
      (PMF.pure response))

omit values in
/-- Admission is read from the original drained closing image, before any
retry or exhausted checkpoint restoration. Only entry-active owners are tested;
guard acceptance at publication is not part of this gate. -/
def originalAdmissionGate (start stop : (E).History) : Prop :=
  ∃ (origin before ending : (app).Control)
      (phase : RuntimePhase (serviceGraph setup mode))
      (priorTrace : (E).Trace (some before))
      (joint : Player → Option (app).Action)
      (legal : (E).Legal (some before) joint)
      (realized : some ending ∈ ((app).transition initial horizon scheduler
        (some before) joint).support)
      (raw : RecoveryState (serviceGraph setup mode)),
    start.state = some origin ∧
    stop = ⟨some ending, priorTrace.extend joint legal realized⟩ ∧
    TracePrefix start.trace priorTrace ∧
    phase ∈ origin.execution.application.phases.head? ∧
    phase ∈ before.execution.application.phases.head? ∧
    phase.kind = .commitment ∧
    before.execution.application.attempt = origin.execution.application.attempt ∧
    ending.execution.application.attempt ≠ origin.execution.application.attempt ∧
    PhaseClosingEffect runtime leaks before.execution ending.execution raw ∧
    ending.execution.application =
      ({ before.execution.application with current := raw } :
        PhaseRuntimeState (serviceGraph setup mode)).normalize ∧
    phase.Finished (phase.drain raw) ∧
    ∀ event ∈ phase.events, ∀ owner,
      (serviceGraph setup mode).actor? event = some owner →
      owner ∉ origin.execution.application.entry.excluded →
      (phase.drain raw).native.accepted (.inr event) ≠ none

omit values in
/-- All entry-active admissions force a genuinely clean original closing
image. An admitted unusable value is still an admission in this statement. -/
theorem closing_all_admitted_no_new_failure
    (before ending : (app).Control) (priorTrace : (E).Trace (some before))
    (phase : RuntimePhase (serviceGraph setup mode))
    (installed : phase ∈ before.execution.application.phases.head?)
    (commitment : phase.kind = .commitment)
    (raw : RecoveryState (serviceGraph setup mode))
    (effect : PhaseClosingEffect runtime leaks before.execution ending.execution raw)
    (changed : ending.execution.application.attempt ≠ before.execution.application.attempt)
    (finished : phase.Finished (phase.drain raw))
    (admitted : ∀ event ∈ phase.events, ∀ owner,
      (serviceGraph setup mode).actor? event = some owner →
      owner ∉ before.execution.application.entry.excluded →
      (phase.drain raw).native.accepted (.inr event) ≠ none) :
    ¬ (((phase.drain raw).excluded \ before.execution.application.entry.excluded) ∩
      phase.owners).Nonempty := by
  classical
  obtain ⟨_native, _binding, receipts, _stored, _remembered, _coverage⟩ :=
    phaseClosingEffect_checkpoint_facts setup mode runtime leaks bounds plan horizon scheduler
      before ending (by rw [PMF.map_comp]; exact priorTrace) raw effect changed
  have record := (receipts.exclusion.installed phase (by
    simpa only using installed)).phase_drain phase
  rintro ⟨owner, member⟩
  have excluded := Finset.mem_sdiff.mp (Finset.mem_inter.mp member).1
  rcases (record.excluded owner).mp excluded.1 with inherited |
      ⟨event, lower, acting, failed⟩
  · exact excluded.2 inherited
  · have read := ReservedEpoch.original_binding_publicFailure_iff runtime leaks
      (serviceGraph_revealRelaxedOrdered setup mode) plan (setup.initialLaw.map encodeInputs)
      horizon scheduler before (by rw [PMF.map_comp]; exact
      ((menu).toRawTrace initial horizon scheduler priorTrace))
      ending.execution raw changed effect phase installed commitment finished event
    have notEarlier : ¬ event.val < phase.low := Nat.not_lt.mpr lower
    have upper : event.val < phase.high := by
      by_contra beyond
      have impossible := read.mp failed
      simp only [notEarlier, beyond, ↓reduceIte] at impossible
    have absent : raw.native.accepted (.inr event) = none := by
      simpa only [notEarlier, upper, ↓reduceIte] using read.mp failed
    have present := admitted event ((phase.mem_events event).mpr ⟨lower, upper⟩)
      owner acting excluded.2
    rw [(phase.drain_tables raw).1] at present
    exact present absent

omit values in
/-- An actual all-admitted close constructs its initialized source extension
and exact decoded word from the original drained image. No source checkpoint,
matching cursor or independently selected source history is an input. -/
theorem exists_closing_source_word
    (maximal : plan.phases.IsChain fun first last =>
      first.kind ≠ last.kind ∨ first.kind = .sample)
    (before ending : (app).Control) (priorTrace : (E).Trace (some before))
    (phase : RuntimePhase (serviceGraph setup mode))
    (installed : phase ∈ before.execution.application.phases.head?)
    (commitment : phase.kind = .commitment)
    (raw : RecoveryState (serviceGraph setup mode))
    (effect : PhaseClosingEffect runtime leaks before.execution ending.execution raw)
    (changed : ending.execution.application.attempt ≠ before.execution.application.attempt)
    (finished : phase.Finished (phase.drain raw))
    (admitted : ∀ event ∈ phase.events, ∀ owner,
      (serviceGraph setup mode).actor? event = some owner →
      owner ∉ before.execution.application.entry.excluded →
      (phase.drain raw).native.accepted (.inr event) ≠ none) :
    ∃ (remaining : List (RuntimePhase (serviceGraph setup mode)))
      (witness : RecoverySourceWitness setup mode plan before.execution.application)
      (next : RecoverySourceCheckpoint setup mode
        (⟨remaining, before.execution.application.generation, phase.drain raw, phase.drain raw,
          before.execution.application.retired⟩ : PhaseRuntimeState (serviceGraph setup mode))),
      before.execution.application.phases = phase :: remaining ∧
      witness.checkpoint.ArchivedProposals before.execution.network.inputs ∧
      ∃ fuel, setup.commitRecoveryProtocol.ReachesWithin fuel
        ⟨_, witness.checkpoint.trace⟩ ⟨_, next.trace⟩ ∧
        setup.recoveryJointRecall next.trace =
          (witness.checkpoint.commitInstructionWord (phase.drain raw).native).reverse ++
            setup.recoveryJointRecall witness.checkpoint.trace := by
  classical
  obtain ⟨witness, archived⟩ := recoverySourceCheckpoint_proposalArchive_history setup mode runtime
    leaks bounds plan maximal horizon scheduler priorTrace
  obtain ⟨remaining, phases⟩ := List.head?_eq_some_iff.mp (Option.mem_def.mp installed)
  have low : phase.low = before.execution.application.attempt.phase := by
    simp only [PhaseRuntimeState.attempt, phases, List.head?_cons, Option.map_some,
      Option.getD_some]
  have committing := witness.checkpoint.compiled.atCommit_of_bindingPhase setup.program mode
    witness.checkpoint.residual.tail witness.checkpoint.refs witness.checkpoint.source.revelations
    witness.checkpoint.registry witness.checkpoint.embedding witness.checkpoint.before
    before.execution.application.attempt.phase phase commitment low witness.checkpoint.source
  have chain := (phasePlanGeometry_history runtime leaks plan maximal
    (setup.initialLaw.map encodeInputs) horizon scheduler
    (by rw [PMF.map_comp]; exact
      ((menu).toRawTrace initial horizon scheduler priorTrace))).2.2
  obtain ⟨native, binding, receipts, stored, remembered, coverage⟩ :=
    phaseClosingEffect_checkpoint_facts setup mode runtime leaks bounds plan horizon scheduler
      before ending (by rw [PMF.map_comp]; exact priorTrace) raw effect changed
  obtain ⟨draw, invariant⟩ := native
  let frame : PhaseRuntimeState (serviceGraph setup mode) :=
    { before.execution.application with current := raw }
  let checkpoint : RecoverySourceCheckpoint setup mode frame :=
    witness.checkpoint.transfer rfl rfl rfl
  have noNewFailure := closing_all_admitted_no_new_failure setup mode runtime leaks bounds plan
    prior before ending priorTrace phase installed commitment raw effect changed finished admitted
  obtain ⟨⟨next, _point, ⟨fuel, reached, word⟩, _history, _intended⟩, _normalized⟩ :=
    checkpoint.after_commit_clean committing phase remaining phases chain binding receipts stored
      remembered invariant coverage finished noNewFailure
  exact ⟨remaining, witness, next, phases, archived, fuel, reached, word⟩

omit values in
/-- The qualification inspects literal foreign own play at the original
information history. The initializer is not conditioned separately. -/
def foreignGood (who : Player) (history : (E).History) : Prop :=
  ∀ owner, owner ≠ who →
    ¬ PhaseProposal.GeneratedUnusableBindingHistory runtime leaks bounds
      initial horizon scheduler owner history

open Classical in
/-- The full original assessment belief followed by a literal current atom,
the original admission gate, and the same stopped history's causal finish.
Unqualified mass is retained as `none`, rather than renormalized away. -/
def qualifiedPayoff (assessment : (N).BehavioralAssessment)
    (who : Player) (site : (N).InformationSite who) (choice : (N).Choice who site.1)
    (utility : State L setup.program.terminalCtx → Player → ℝ)
    (excludedPayoff : Player → ℝ) : PMF (Option ℝ) :=
  (assessment.belief who site).bind fun history =>
    (stoppedFinish setup mode runtime leaks bounds plan prior values who history.val
      (history.property.symm ▸ choice)).map fun result =>
        if foreignGood setup mode runtime leaks bounds plan prior who history.val ∧
            originalAdmissionGate setup mode runtime leaks bounds plan prior history.val result.1
        then some (phaseExclusionBase setup mode runtime leaks utility excludedPayoff
          result.2.state who)
        else none

open Classical in
/-- Actual full-posterior qualification, without a payoff or normalization. -/
def qualificationLaw (assessment : (N).BehavioralAssessment)
    (who : Player) (site : (N).InformationSite who) (choice : (N).Choice who site.1) : PMF Bool :=
  (assessment.belief who site).bind fun history =>
    (stoppedFinish setup mode runtime leaks bounds plan prior values who history.val
      (history.property.symm ▸ choice)).map fun result =>
        decide (foreignGood setup mode runtime leaks bounds plan prior who history.val ∧
          originalAdmissionGate setup mode runtime leaks bounds plan prior history.val result.1)

/-- The coefficient is the mass of actual qualification at the original
information, including foreign-past failures in the complement. -/
def qualificationMass (assessment : (N).BehavioralAssessment)
    (who : Player) (site : (N).InformationSite who) (choice : (N).Choice who site.1) : ℝ :=
  (qualificationLaw setup mode runtime leaks bounds plan prior values assessment who site choice
    true).toReal

/-- The retained `some` mass is exactly the physical qualification event. -/
theorem qualifiedPayoff_isSome (assessment : (N).BehavioralAssessment)
    (who : Player) (site : (N).InformationSite who) (choice : (N).Choice who site.1)
    (utility : State L setup.program.terminalCtx → Player → ℝ)
    (excludedPayoff : Player → ℝ) :
    (qualifiedPayoff setup mode runtime leaks bounds plan prior values assessment who site choice
      utility excludedPayoff).map Option.isSome =
      qualificationLaw setup mode runtime leaks bounds plan prior values assessment who site
        choice := by
  classical
  simp only [qualifiedPayoff, qualificationLaw, PMF.map_bind, PMF.map_comp]
  apply bind_congr_on_support
  intro history _
  congr 1
  funext result
  simp only [Function.comp_def]
  split_ifs <;> simp_all

open Classical in
/-- Bayes normalization of the literal qualified experiment uses the original
native information mass and original history reach weights. -/
theorem qualifiedPayoff_mul_informationMass
    (assessment : (N).BehavioralAssessment)
    (bayes : InformationModel.BehavioralAssessment.IsBayesConsistent (N) assessment
      ((menu).decisionInformationAntichain initial horizon scheduler))
    (who : Player) (site : (N).InformationSite who)
    (positive : 0 < (N).informationMass assessment.strategy who site)
    (choice : (N).Choice who site.1)
    (utility : State L setup.program.terminalCtx → Player → ℝ)
    (excludedPayoff : Player → ℝ) (outcome : Option ℝ) :
    (N).informationMass assessment.strategy who site *
        qualifiedPayoff setup mode runtime leaks bounds plan prior values assessment who site
          choice utility excludedPayoff outcome =
      ∑' history : (N).InformationHistory who site.1,
        (N).historyReachWeight assessment.strategy history.val *
          ((stoppedFinish setup mode runtime leaks bounds plan prior values who history.val
            (history.property.symm ▸ choice)).map fun result =>
              if foreignGood setup mode runtime leaks bounds plan prior who history.val ∧
                  originalAdmissionGate setup mode runtime leaks bounds plan prior
                    history.val result.1 then
                some (phaseExclusionBase setup mode runtime leaks utility excludedPayoff
                  result.2.state who)
              else none) outcome := by
  have finite : (N).informationMass assessment.strategy who site ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top
      ((N).informationMass_le_one assessment.strategy who site
        ((menu).decisionInformationAntichain initial horizon scheduler who site))
  rw [qualifiedPayoff, PMF.bind_apply, ← ENNReal.tsum_mul_left]
  apply tsum_congr
  intro history
  rw [bayes who site positive history]
  rw [div_eq_mul_inv, ← mul_assoc, ← mul_assoc,
    mul_right_comm ((N).informationMass assessment.strategy who site)
      ((N).historyReachWeight assessment.strategy history.val),
    ENNReal.mul_inv_cancel (ne_of_gt positive) finite, one_mul]

/-- Zero qualification leaves only the explicit unqualified outcome. -/
theorem qualifiedPayoff_eq_pure_none
    (assessment : (N).BehavioralAssessment)
    (who : Player) (site : (N).InformationSite who) (choice : (N).Choice who site.1)
    (zero : qualificationMass setup mode runtime leaks bounds plan prior values
      assessment who site choice = 0)
    (utility : State L setup.program.terminalCtx → Player → ℝ)
    (excludedPayoff : Player → ℝ) :
    qualifiedPayoff setup mode runtime leaks bounds plan prior values assessment who site choice
      utility excludedPayoff = PMF.pure none := by
  have probabilityZero :
      qualificationLaw setup mode runtime leaks bounds plan prior values assessment who site choice
        true = 0 := by
    change (qualificationLaw setup mode runtime leaks bounds plan prior values assessment who
      site choice true).toReal = 0 at zero
    rcases (ENNReal.toReal_eq_zero_iff _).mp zero with zero | infinite
    · exact zero
    · exact False.elim ((qualificationLaw setup mode runtime leaks bounds plan prior values
        assessment who site choice).apply_ne_top true infinite)
  apply pmf_eq_pure_of_support_subset_singleton
  intro result reached
  cases result with
  | none => exact Set.mem_singleton_iff.mpr rfl
  | some amount =>
      have mapped : true ∈ ((qualifiedPayoff setup mode runtime leaks bounds plan prior values
          assessment who site choice utility excludedPayoff).map Option.isSome).support :=
        (PMF.mem_support_map_iff Option.isSome _ true).mpr ⟨some amount, reached, rfl⟩
      rw [qualifiedPayoff_isSome] at mapped
      exact False.elim (mapped probabilityZero)

open Classical in
/-- Causally insert the selected source atom and then use the zero-flag
continuation. This never conditions a baseline future on the selected value. -/
def sourceCausalPayoff (assessment : setup.proposalRecoveryModel.BehavioralAssessment)
    (who : Player) (site : setup.proposalRecoveryModel.InformationSite who)
    (choice : setup.proposalRecoveryModel.Choice who site.1)
    (positive : ∃ history ∈
        {history : setup.proposalRecoveryModel.InformationHistory who site.1 |
          setup.proposalRecoveryForeignGood who history.val},
      history ∈ (assessment.belief who site).support)
    (utility : State L setup.program.terminalCtx → Player → ℝ)
    (excludedPayoff : Player → ℝ) : PMF (Option ℝ) :=
  let profile := sourceUnflaggedStrategy setup values
  let sourceCertificate := setup.proposalRecoveryProtocol_bounded.wellFoundedHistories
  ((assessment.belief who site).filter
      {history | setup.proposalRecoveryForeignGood who history.val} positive).bind fun history =>
    ((setup.proposalRecoveryModel.runBehavioralFrom
      (Profile.update (sig := setup.proposalRecoveryModel.behavioralSignature) profile who
        ((profile who).commit site.1 choice)) 1 history.val).bind
      (setup.proposalRecoveryModel.runBehavioralTerminalFrom sourceCertificate profile)).map
        (fun terminal => some (setup.proposalRecoveryPayoff utility excludedPayoff who terminal))

/-- Splitting the actual ordinary continuation at the current block does not
change the forced causal terminal law. All later flags remain zero. -/
theorem sourceCausalPayoff_block
    (assessment : setup.proposalRecoveryModel.BehavioralAssessment)
    (who : Player) (site : setup.proposalRecoveryModel.InformationSite who)
    (choice : setup.proposalRecoveryModel.Choice who site.1)
    (positive : ∃ history ∈
        {history : setup.proposalRecoveryModel.InformationHistory who site.1 |
          setup.proposalRecoveryForeignGood who history.val},
      history ∈ (assessment.belief who site).support)
    (utility : State L setup.program.terminalCtx → Player → ℝ)
    (excludedPayoff : Player → ℝ) :
    sourceCausalPayoff setup values assessment who site choice positive utility excludedPayoff =
      ((assessment.belief who site).filter
        {history | setup.proposalRecoveryForeignGood who history.val} positive).bind fun history =>
          ((sourceForcedBlock setup values who history.val (history.property.symm ▸ choice)).bind
            (setup.proposalRecoveryModel.runBehavioralTerminalFrom
              setup.proposalRecoveryProtocol_bounded.wellFoundedHistories
              (sourceUnflaggedStrategy setup values))).map
                (fun terminal => some
                  (setup.proposalRecoveryPayoff utility excludedPayoff who terminal)) := by
  rcases site with ⟨information, occurs⟩
  unfold sourceCausalPayoff sourceForcedBlock
  simp only [PMF.bind_bind, PMF.map_bind]
  apply bind_congr_on_support
  intro history _
  rcases history with ⟨history, same⟩
  cases same
  apply bind_congr_on_support
  intro after _
  simpa only [PMF.map_bind] using congrArg (PMF.map fun terminal => some
    (setup.proposalRecoveryPayoff utility excludedPayoff who terminal))
      (setup.proposalRecoveryModel.runBehavioralTerminalFrom_eq_bind_runBehavioralFrom
        setup.proposalRecoveryProtocol_bounded.wellFoundedHistories
        (sourceUnflaggedStrategy setup values)
        (sourceCommitFuel setup history - 1) after)

omit mode runtime leaks bounds plan prior values in
/-- Exact qualified payoff transport at a clean concurrent binding information.
The original assessed beliefs determine the qualification mass and the source
causal law. This proposition asserts no proof of their correspondence. -/
def QualifiedBindingLaw (implementation : ReservedConcurrentImplementation setup) : Prop :=
  let nativeInitial := implementation.initial
  let nativeMenu := PhaseCount.onePacketMenu implementation.runtime implementation.leaks
    implementation.bounds
  let nativeModel := nativeMenu.information nativeInitial implementation.horizon
    implementation.scheduler
  ∀ _operational : implementation.Operational,
  ∀ (scale sourceBad nativeBad : Set.Icc (0 : ℝ) 1),
    0 < scale.val → scale.val < 1 →
    0 < sourceBad.val → sourceBad.val < 1 →
    0 < nativeBad.val → nativeBad.val < 1 →
  ∀ (ordinary : ∀ owner (key : setup.ProposalRecoveryComponent owner),
      PMF (setup.CommitRecoveryValueChoice owner key.1)),
    (∀ owner key, FullSupport (ordinary owner key)) →
  ∀ (source : setup.proposalRecoveryModel.BehavioralAssessment)
    (native : (nativeModel).BehavioralAssessment),
    source.IsFullyMixed →
    InformationModel.BehavioralAssessment.IsBayesConsistent setup.proposalRecoveryModel source
      setup.proposalRecoveryModel_decisionAntichain →
    (∀ owner (history : setup.proposalRecoveryProtocol.History)
        (_running : ¬ setup.proposalRecoveryProtocol.terminal history.state),
      source.strategy owner (setup.proposalRecoveryModel.infoOf owner history.trace) =
        setup.proposalRecoveryNormalizedTrembledProfile
          scale.val scale.property.1 scale.property.2
          sourceBad.val sourceBad.property.1 sourceBad.property.2
          scale.val scale.property.1 scale.property.2 ordinary owner
            (setup.proposalRecoveryModel.infoOf owner history.trace)) →
    native.IsFullyMixed →
    InformationModel.BehavioralAssessment.IsBayesConsistent nativeModel native
      (nativeMenu.decisionInformationAntichain nativeInitial implementation.horizon
        implementation.scheduler) →
    native.strategy = phaseProposalReferenceStrategy setup .concurrent
      implementation.runtime implementation.leaks implementation.bounds implementation.plan
      nativeInitial implementation.horizon implementation.scheduler ordinary
      ⟨nativeBad, scale, scale, scale⟩ →
  ∀ (who : Player) (site : (nativeModel).InformationSite who)
    (past : List (phaseApplication implementation.runtime implementation.leaks).PlayerEntry)
    (view : (phaseApplication implementation.runtime implementation.leaks).PlayerView),
    site.1 = some (past, view) →
  ∀ (event : (serviceGraph setup .concurrent).EventId) (payload : L.Ty)
    (binding : (serviceGraph setup .concurrent).outputLayout event = .binding who payload),
    PhaseRuntimeState.requests view.application.2 who
      ⟨view.application.2.attempt, event⟩ →
    (∀ message ∈ (phaseApplication implementation.runtime implementation.leaks).outputs past,
      PhaseCount.event? message.payload ≠ some ⟨view.application.2.attempt, event⟩) →
    ¬ phaseProposalSavedBindingFailure setup .concurrent implementation.runtime
      implementation.leaks who event view →
    ¬ phaseProposalCurrentBindingFailure setup .concurrent implementation.runtime
      implementation.leaks who event view →
    ¬ (view.application.2.excluded \
      ((view.application.2.retired.map fun record =>
          record.2.sourceFailureFootprint.2).foldr (fun first rest => first ∪ rest) ∅ ∪
        view.application.2.native.sourceFailureFootprint.1
          view.application.2.attempt.phase)).Nonempty →
    let proper := fun (value : L.Val payload) (choice : (nativeModel).Choice who site.1) =>
      ∃ (serial : Nat) (material : WitnessedSubmission (serviceGraph setup .concurrent)),
        choice.1 = some ⟨some material⟩ ∧
        material.call.packet = .commitment event (who, .prepared serial) ∧
        PhaseProposal.bindingPreparation material = some ⟨payload, value⟩
    let mass := qualificationMass setup .concurrent implementation.runtime implementation.leaks
      implementation.bounds implementation.plan implementation.prior ordinary native who site
    let payoff := qualifiedPayoff setup .concurrent implementation.runtime implementation.leaks
      implementation.bounds implementation.plan implementation.prior ordinary native who site
    (∀ (value : L.Val payload) (choice : (nativeModel).Choice who site.1),
      proper value choice → mass choice = 0 ∧
        ∀ (utility : State L setup.program.terminalCtx → Player → ℝ)
          (excludedPayoff : Player → ℝ), payoff choice utility excludedPayoff = PMF.pure none) ∨
    ∃ (sourceSite : setup.proposalRecoveryModel.InformationSite who)
      (retained : Set.Ioc (0 : ℝ) 1)
      (encode : L.Val payload → setup.proposalRecoveryModel.Choice who sourceSite.1)
      (positive : ∃ history ∈
          {history : setup.proposalRecoveryModel.InformationHistory who sourceSite.1 |
            setup.proposalRecoveryForeignGood who history.val},
        history ∈ (source.belief who sourceSite).support),
      phaseProposalQuery? setup .concurrent implementation.runtime implementation.leaks
          implementation.plan who event past view =
        some (setup.proposalRecoveryQuery who sourceSite.1) ∧
      (∀ value, phaseRecoveryBindingData setup .concurrent event who payload binding
        ((encode value).1.map (fun move => move.semantic)) = (.success value, false)) ∧
      sourceUnflaggedStrategy setup ordinary who sourceSite.1 =
        (ordinary who (setup.proposalRecoveryQuery who sourceSite.1)).map (fun sampled =>
          encode (phaseRecoveryDomainValue setup .concurrent event who payload binding
            sampled.val.val)) ∧
      ∀ (value : L.Val payload) (choice : (nativeModel).Choice who site.1),
        proper value choice → mass choice = retained.val ∧
          ∀ (utility : State L setup.program.terminalCtx → Player → ℝ)
            (excludedPayoff : Player → ℝ),
            payoff choice utility excludedPayoff =
              mix retained.val retained.property.1.le retained.property.2
                (sourceCausalPayoff setup ordinary source who sourceSite (encode value) positive
                  utility excludedPayoff) (PMF.pure none)

omit values in
private theorem closing_all_admitted_excluded_eq
    (serviceScheduler : (app).Scheduler)
    (before ending : (app).Control)
    (priorTrace : ((menu).protocol initial horizon serviceScheduler).Trace (some before))
    (phase : RuntimePhase (serviceGraph setup mode))
    (installed : phase ∈ before.execution.application.phases.head?)
    (commitment : phase.kind = .commitment)
    (raw : RecoveryState (serviceGraph setup mode))
    (effect : PhaseClosingEffect runtime leaks before.execution ending.execution raw)
    (changed : ending.execution.application.attempt ≠ before.execution.application.attempt)
    (finished : phase.Finished (phase.drain raw))
    (admitted : ∀ event ∈ phase.events, ∀ owner,
      (serviceGraph setup mode).actor? event = some owner →
      owner ∉ before.execution.application.entry.excluded →
      (phase.drain raw).native.accepted (.inr event) ≠ none) :
    (phase.drain raw).excluded = before.execution.application.entry.excluded := by
  classical
  obtain ⟨_native, _binding, receipts, _stored, _remembered, _coverage⟩ :=
    phaseClosingEffect_checkpoint_facts setup mode runtime leaks bounds plan horizon
      serviceScheduler
      before ending (by rw [PMF.map_comp]; exact priorTrace) raw effect changed
  have record := (receipts.exclusion.installed phase (by simpa only using installed)).phase_drain
    phase
  apply Finset.ext
  intro owner
  constructor
  · intro member
    rcases (record.excluded owner).mp member with inherited |
        ⟨event, lower, acting, failed⟩
    · exact inherited
    · by_contra active
      have read := ReservedEpoch.original_binding_publicFailure_iff runtime leaks
        (serviceGraph_revealRelaxedOrdered setup mode) plan (setup.initialLaw.map encodeInputs)
        horizon serviceScheduler before (by rw [PMF.map_comp]; exact
      ((menu).toRawTrace initial horizon serviceScheduler priorTrace))
        ending.execution raw changed effect phase installed commitment finished event
      have notEarlier : ¬ event.val < phase.low := Nat.not_lt.mpr lower
      have upper : event.val < phase.high := by
        by_contra beyond
        have impossible := read.mp failed
        simp only [notEarlier, beyond, ↓reduceIte] at impossible
      have absent : raw.native.accepted (.inr event) = none := by
        simpa only [notEarlier, upper, ↓reduceIte] using read.mp failed
      have present := admitted event ((phase.mem_events event).mpr ⟨lower, upper⟩)
        owner acting active
      rw [(phase.drain_tables raw).1] at present
      exact present absent
  · intro inherited
    exact (record.excluded owner).mpr (Or.inl inherited)

omit values in
/-- On the actual first commitment exit, the original trace gate is precisely
equality with the exclusion saved at the original entry. -/
theorem attemptUntil_gate_iff
    (delay bound : (serviceGraph setup mode).EventId → Nat)
    (contract : PhaseService.AsyncContract runtime leaks initial horizon scheduler delay bound)
    (profile : ∀ owner, (N).BehavioralPolicy owner)
    (start : (app).Control) (trace : (E).Trace (some start))
    (origin : (app).Control) (originTrace : (E).Trace (some origin))
    (originKept : TracePrefix originTrace trace)
    (sameAttempt : start.execution.application.attempt = origin.execution.application.attempt)
    (samePhases : start.execution.application.phases = origin.execution.application.phases)
    (phase : RuntimePhase (serviceGraph setup mode))
    (installed : phase ∈ start.execution.application.phases.head?)
    (commitment : phase.kind = .commitment)
    (final : (E).History)
    (supported : final ∈ ((N).runBehavioralUntil
      ((menu).bounded initial horizon scheduler).wellFoundedHistories profile
      (attemptExit setup mode runtime leaks bounds plan prior ⟨some start, trace⟩)
      ⟨some start, trace⟩).support) :
    originalAdmissionGate setup mode runtime leaks bounds plan prior
      ⟨some origin, originTrace⟩ final ↔
      ∃ ending : (app).Control, final.state = some ending ∧
        ending.execution.application.attempt ≠ origin.execution.application.attempt ∧
        ending.execution.application.current.excluded =
          origin.execution.application.entry.excluded := by
  classical
  have initialized : ∀ state ∈ (initial).support, state.Ordered := by
    intro state member
    obtain ⟨inputs, _, rfl⟩ := PMF.support_map .. ▸ member
    exact PhaseRuntimeState.initial_ordered plan (encodeInputs inputs)
  have ordered := (phaseApplication_seedOrder runtime leaks).history initial horizon scheduler
    initialized ((menu).toRawTrace initial horizon scheduler originTrace)
  constructor
  · rintro ⟨original, before, ending, currentPhase, priorTrace, joint, legal, realized, raw,
      initialState, finalEq, kept, _originalPhase, installedNow, kind, same, changed, effect,
      normalized, finished, admitted⟩
    cases Option.some.inj initialState
    have entryEq := (phase_attempt_progress_of_prefix runtime leaks menu initial initialized
      horizon scheduler origin before originTrace priorTrace kept ordered).2.2 same.symm
    have excluded := closing_all_admitted_excluded_eq setup mode runtime leaks bounds plan scheduler
      before ending priorTrace currentPhase installedNow kind raw effect
      (fun equal => changed (equal.trans same)) finished (by simpa only [← entryEq] using admitted)
    have actualExcluded : ending.execution.application.current.excluded =
        (currentPhase.drain raw).excluded := by
      rw [normalized]
      simpa only [PhaseRuntimeState.normalize, RuntimePhase.drain_excluded] using
        (PhaseRuntimeState.settle_physical before.execution.application.phases
          before.execution.application.generation before.execution.application.entry raw
          before.execution.application.retired).1
    exact ⟨ending, congrArg History.state finalEq, changed,
      actualExcluded.trans (excluded.trans (congrArg RecoveryState.excluded entryEq.symm))⟩
  · rintro ⟨ending, finalState, changed, excludedEq⟩
    have stopEq : attemptExit setup mode runtime leaks bounds plan prior ⟨some start, trace⟩ =
        (fun history : (E).History => match history.state with
          | none => False
          | some control => control.execution.application.attempt ≠
              start.execution.application.attempt) := by
      funext history
      cases state : history.state <;> simp only [attemptExit, state]
    have snapshotSupported := supported
    rw [stopEq] at snapshotSupported
    have snapshotLaw := phase_attempt_stopped_receipt_snapshot runtime leaks menu plan
      (setup.initialLaw.map encodeInputs) horizon scheduler delay bound
    rw [PMF.map_comp] at snapshotLaw
    dsimp only [Function.comp_def] at snapshotLaw
    obtain ⟨actual, actualState, actualChanged, _idle, snapshot, finished, valid, covered,
      excluded, _receipts, before, priorTrace, joint, legal, realized, raw, kept, edgeKept,
      same, installedNow, snapshotEq, normalized, effect⟩ :=
      snapshotLaw contract profile start trace phase installed final
          (by
            convert snapshotSupported using 1; congr 1
            all_goals
              congr 1
              funext history
              cases state : history.state <;> rfl)
    cases Option.some.inj (actualState.symm.trans finalState)
    have first := (N).runBehavioralUntil_support_first
      ((menu).bounded initial horizon scheduler).wellFoundedHistories profile
        (attemptExit setup mode runtime leaks bounds plan prior ⟨some start, trace⟩)
        ⟨some start, trace⟩ final supported
    have edgeEq :
        (⟨some ending, priorTrace.extend joint legal realized⟩ : (E).History) = final := by
      apply edgeKept.eq_of_length
      have lower := edgeKept.length_le
      by_contra different
      have shorter : (priorTrace.extend joint legal realized).length < final.trace.length := by
        omega
      exact first ⟨some ending, priorTrace.extend joint legal realized⟩
        (kept.extend joint legal realized) edgeKept shorter actualChanged
    refine ⟨origin, before, ending, phase, priorTrace, joint, legal, realized, raw, rfl,
      edgeEq.symm, originKept.trans kept, ?_, installedNow, commitment,
      same.trans sameAttempt, changed, effect,
      normalized, snapshotEq ▸ finished, ?_⟩
    · simpa only [← samePhases] using installed
    · intro event inside owner acting active absent
      obtain ⟨author, payload, layout⟩ := commitment ▸
        phase.fields event ((phase.mem_events event).mp inside).1
          ((phase.mem_events event).mp inside).2
      have authorEq : author = owner := Option.some.inj
        ((actor?_of_outputLayout_binding (serviceGraph setup mode) layout).symm.trans acting)
      subst author
      have missing : snapshot.native.PublicFailure event := Or.inl
        ((snapshot.native.publicView_missedBinding event owner payload layout).mpr
          ⟨finished inside, by simpa only [snapshotEq] using absent⟩)
      exact active (excludedEq ▸ excluded ▸ covered.covered event owner acting missing)

omit prior values in
/-- At an idle counted history, stopping on the original namespace change has
exactly the existing physical stopped-round law. The full stopped control is
retained, so supported physical endpoints have supported counted preimages. -/
theorem attemptUntil_state
    (initialLaw : PMF (app).State)
    (serviceScheduler : (app).Scheduler)
    (profile : ∀ owner, ((menu).information initialLaw horizon serviceScheduler).BehavioralPolicy
      owner)
    (attempt : CommitAttemptId) (remaining : Nat) (execution : (app).Execution)
    (trace : ((menu).protocol initialLaw horizon serviceScheduler).Trace
      (some ⟨remaining, none, execution⟩)) :
    (((menu).information initialLaw horizon serviceScheduler).runBehavioralUntil
      ((menu).bounded initialLaw horizon serviceScheduler).wellFoundedHistories profile
      (fun history => match history.state with
        | none => False
        | some control => control.execution.application.attempt ≠ attempt)
      ⟨some ⟨remaining, none, execution⟩, trace⟩).map History.state =
    ((app).runUntil serviceScheduler ((menu).decodeProfile initialLaw horizon serviceScheduler
      profile) (fun next => next.application.attempt ≠ attempt) remaining execution).map
      (fun next => some ⟨horizon - next.environmentRecall.length, none, next⟩) := by
  classical
  let model := (menu).information initialLaw horizon serviceScheduler
  let protocol := (menu).protocol initialLaw horizon serviceScheduler
  let certificate := ((menu).bounded initialLaw horizon serviceScheduler).wellFoundedHistories
  let players := (menu).decodeProfile initialLaw horizon serviceScheduler profile
  let halted := fun next : (app).Execution => next.application.attempt ≠ attempt
  let stopped := fun history : protocol.History => match history.state with
    | none => False
    | some control => halted control.execution
  let pack := fun next : (app).Execution =>
    (some ⟨horizon - next.environmentRecall.length, none, next⟩ : (app).ProtocolState)
  let physical := fun state : (app).ProtocolState => match state with
    | none => PMF.pure none
    | some control =>
        if halted control.execution then PMF.pure (some control)
        else ((app).resume players control.actor control.execution).bind fun next =>
          ((app).runUntil serviceScheduler players halted control.remaining next).map pack
  have packed (control : (app).Control)
      (actual : protocol.Trace (some control)) (idle : control.actor = none) :
      pack control.execution = some control := by
    have accounted := (app).raw_trace_horizon initialLaw horizon serviceScheduler
      ((menu).toRawTrace initialLaw horizon serviceScheduler actual)
    rcases control with ⟨rounds, actor, current⟩
    change actor = none at idle
    subst actor
    change current.environmentRecall.length + rounds = horizon at accounted
    dsimp only [pack]
    congr 2
    omega
  have loop : ∀ history : protocol.History, ∀ control : (app).Control,
      history.state = some control →
      (model.runBehavioralUntil certificate profile stopped history).map History.state =
        physical (some control) := by
    intro history
    induction history using certificate.induction with
    | _ history ih =>
      intro control current
      by_cases halt : stopped history
      · have haltedControl : halted control.execution := by
          simpa only [stopped, current] using halt
        rw [model.runBehavioralUntil_of_stopped certificate profile halt, PMF.pure_map]
        simp only [physical, haltedControl, ↓reduceIte, current]
      by_cases ended : protocol.terminal history.state
      · have terminal : control.remaining = 0 ∧ control.actor = none := by
          have actual := ended
          rw [current] at actual
          change control.remaining = 0 ∧ control.actor = none at actual
          exact actual
        rw [model.runBehavioralUntil_of_terminal certificate profile ended, PMF.pure_map]
        have notHalted : ¬ halted control.execution := by
          simpa only [stopped, current] using halt
        simp only [physical, notHalted, ↓reduceIte, terminal.1, terminal.2,
          ReactiveApplication.resume, PMF.pure_bind, ReactiveApplication.runUntil,
          PMF.pure_map, packed control (current ▸ history.trace) terminal.2, current]
      have notHalted : ¬ halted control.execution := by
        simpa only [stopped, current] using halt
      rw [model.runBehavioralUntil_of_running certificate profile halt ended, PMF.map_bind]
      calc
        _ = (model.runBehavioralFrom profile 1 history).bind
            (fun next => physical next.state) := by
          apply bind_congr_on_support
          intro next member
          have realized := model.mem_support_runBehavioralFrom_one profile ended member
          obtain ⟨joint, _legal, moved⟩ := realized.1
          change next.state ∈ ((app).transition initialLaw horizon serviceScheduler
            history.state joint).support at moved
          rw [current] at moved
          obtain ⟨child, nextState, _recall⟩ := (app).transition_recall_prefix initialLaw horizon
            serviceScheduler control next.state joint moved
          simpa only [nextState] using ih next realized.1 child nextState
        _ = ((model.runBehavioralFrom profile 1 history).map History.state).bind physical :=
          (show ((model.runBehavioralFrom profile 1 history).map History.state).bind physical =
            (model.runBehavioralFrom profile 1 history).bind
              (fun next => physical next.state) from
                by simpa only [Function.comp_def] using
                  (PMF.bind_map (model.runBehavioralFrom profile 1 history)
                    History.state physical)).symm
        _ = ((app).controlStep initialLaw horizon serviceScheduler players
            (some control)).bind physical := by
          rw [(menu).run_map_controlSteps, Function.iterate_one, PMF.pure_bind, current]
        _ = physical (some control) := by
          rcases control with ⟨rounds, actor, before⟩
          cases actor with
          | some owner =>
              have responseAttempt (response : (app).Action) :
                  (before.respond app owner response).application.attempt =
                    before.application.attempt := by
                rcases response with ⟨_ | material⟩ <;> rfl
              simp only [ReactiveApplication.controlStep, ReactiveApplication.actor,
                Option.bind_some, ReactiveApplication.transition, ↓reduceIte,
                Option.getD_some, PMF.bind_bind, PMF.pure_bind, physical, notHalted,
                ↓reduceIte, ReactiveApplication.resume, ReactiveApplication.invoke,
                PMF.bind_map, Function.comp_def]
              apply bind_congr_on_support
              intro response _
              have unchanged : ¬ halted (before.respond app owner response) := by
                simpa only [halted, responseAttempt] using notHalted
              simp only [unchanged, ↓reduceIte]
          | none =>
              cases rounds with
              | zero =>
                  apply (ended ?_).elim
                  rw [current]
                  change (0 : Nat) = 0 ∧ (none : Option Player) = none
                  exact ⟨rfl, rfl⟩
              | succ rounds =>
                  simp only [ReactiveApplication.controlStep, ReactiveApplication.actor,
                    Option.bind_some, ReactiveApplication.transition,
                    PMF.bind_bind, PMF.bind_map, Function.comp_def]
                  change ((serviceScheduler before.environmentRecall
                    (before.observeEnvironment app)).bind fun command =>
                      (before.environmentStep app command).bind fun next =>
                        physical (some ⟨rounds, command.actor? app, next⟩)) = _
                  have unfolded : physical (some ⟨rounds + 1, none, before⟩) =
                      ((app).runUntil serviceScheduler players halted (rounds + 1) before).map
                        pack := by
                    simp only [physical, notHalted, ↓reduceIte, ReactiveApplication.resume,
                      PMF.pure_bind]
                  rw [unfolded]
                  simp only [ReactiveApplication.runUntil, notHalted, ↓reduceIte,
                    PMF.map_bind, ReactiveApplication.round, ReactiveApplication.dispatch,
                    PMF.bind_bind]
                  apply bind_congr_on_support
                  intro command selected
                  apply bind_congr_on_support
                  intro next moved
                  have actual := (menu).toRawTrace initialLaw horizon serviceScheduler
                    (current ▸ history.trace)
                  obtain ⟨nextTrace⟩ := (app).raw_trace_environment initialLaw horizon
                    serviceScheduler rounds before next command actual selected moved
                  have accounted := (app).raw_trace_horizon initialLaw horizon serviceScheduler
                    nextTrace
                  have aligned : horizon - next.environmentRecall.length = rounds := by
                    change next.environmentRecall.length + rounds = horizon at accounted
                    omega
                  cases selectedActor : command.actor? app with
                  | none =>
                      by_cases atExit : halted next
                      · simp only [physical, atExit, ↓reduceIte,
                          ReactiveApplication.resume, PMF.pure_bind,
                          (app).runUntil_of_stop serviceScheduler players halted rounds next
                            atExit, PMF.pure_map,
                          pack, aligned]
                      · simp only [physical, atExit, ↓reduceIte,
                          ReactiveApplication.resume, PMF.pure_bind]
                  | some owner =>
                      have sameApplication : next.application = before.application := by
                        cases command with
                        | activate responder =>
                            dsimp only [ReactiveApplication.Execution.environmentStep] at moved
                            obtain ⟨updated, observed, rfl⟩ :=
                              (PMF.mem_support_map_iff _ _ _).mp moved
                            obtain ⟨_seen, _supported, rfl⟩ :=
                              (PMF.mem_support_map_iff _ _ _).mp observed
                            rfl
                        | «include» id => cases selectedActor
                        | application call => cases selectedActor
                        | wait => cases selectedActor
                      have unchanged : ¬ halted next := by
                        simpa only [halted, sameApplication] using notHalted
                      simp only [physical, unchanged, ↓reduceIte]
  change (model.runBehavioralUntil certificate profile stopped
    ⟨some ⟨remaining, none, execution⟩, trace⟩).map History.state =
      ((app).runUntil serviceScheduler players halted remaining execution).map pack
  have actual := loop ⟨some ⟨remaining, none, execution⟩, trace⟩
    ⟨remaining, none, execution⟩ rfl
  by_cases halt : halted execution
  · rw [(app).runUntil_of_stop serviceScheduler players halted remaining execution halt,
      PMF.pure_map, packed ⟨remaining, none, execution⟩ trace rfl]
    simpa only [physical, halt, ↓reduceIte] using actual
  · simpa only [physical, halt, ↓reduceIte, ReactiveApplication.resume, PMF.pure_bind]
      using actual

open Classical in
/-- The original first-exit gate, terminal state and immutable tape have one
joint law. The tape posterior is taken at the original callback and the same
tape drives both the existing stopped evaluator and its terminal finish. -/
theorem stoppedFinish_gate_seed_joint
    (activationGap processingGap : Nat)
    (gaps : ∀ tape ∈ prior.support, tape.BoundedGaps (ReservedEpoch.completionCycles runtime)
      activationGap processingGap)
    (maximal : plan.phases.IsChain fun first last => first.kind ≠ last.kind ∨ first.kind = .sample)
    (who : Player) (history : (E).History)
    (choice : (N).Choice who ((N).infoOf who history.trace))
    (remaining : Nat) (execution : (app).Execution)
    (current : history.state = some ⟨remaining, some who, execution⟩)
    (response : (app).Action) (selected : choice.1 = some response)
    (phase : RuntimePhase (serviceGraph setup mode))
    (installed : phase ∈ execution.application.phases.head?)
    (commitment : phase.kind = .commitment) :
    let family := ReservedEpoch.family runtime leaks (ReservedEpoch.packetCapacity runtime)
    let mixture := (app).schedulerMixture prior family
    let players := phaseProposalUnflaggedPolicy setup mode runtime leaks bounds plan values
    let stop := fun next : (app).Execution =>
      next.application.attempt ≠ execution.application.attempt
    let seedAt := fun state : (app).ProtocolState => match state with
      | none => prior
      | some control => mixture.posterior control.execution.environmentRecall
    ((stoppedFinish setup mode runtime leaks bounds plan prior values who history choice).bind
      fun result => (seedAt result.2.state).map fun tape =>
        ((decide (originalAdmissionGate setup mode runtime leaks bounds plan prior
            history result.1),
          result.2.state), tape)) =
    (mixture.posterior execution.environmentRecall).bind fun tape =>
      ((app).runUntil (family tape) players stop remaining
        (execution.respond app who response)).bind fun ending =>
          ((app).finish initial horizon (family tape) players
            (some ⟨horizon - ending.environmentRecall.length, none, ending⟩)).map fun terminal =>
              ((decide (ending.application.attempt ≠ execution.application.attempt ∧
                  ending.application.current.excluded = execution.application.entry.excluded),
                terminal), tape) := by
  classical
  intro family mixture players stop seedAt
  let certificate := ((menu).bounded initial horizon scheduler).wellFoundedHistories
  let afterExecution := execution.respond app who response
  let pack := fun ending : (app).Execution =>
    (some ⟨horizon - ending.environmentRecall.length, none, ending⟩ : (app).ProtocolState)
  let gate := fun state : (app).ProtocolState => decide (∃ ending : (app).Control,
    state = some ending ∧ ending.execution.application.attempt ≠ execution.application.attempt ∧
      ending.execution.application.current.excluded = execution.application.entry.excluded)
  have packGate (ending : (app).Execution) : gate (pack ending) =
      decide (ending.application.attempt ≠ execution.application.attempt ∧
        ending.application.current.excluded = execution.application.entry.excluded) := by
    dsimp only [gate, pack]
    apply decide_eq_decide.mpr
    constructor
    · rintro ⟨actual, same, changed, excluded⟩
      cases Option.some.inj same
      exact ⟨changed, excluded⟩
    · rintro ⟨changed, excluded⟩
      exact ⟨_, rfl, changed, excluded⟩
  have decoded : (menu).decodeProfile initial horizon scheduler plain = players := by
    funext owner
    exact (menu).decode_restrictPolicy_of_covered initial horizon scheduler owner _
      (phaseProposalUnflaggedPolicy_covered setup mode runtime leaks bounds plan values owner)
  have contract := ReservedEpoch.implementation_asyncContract runtime leaks prior
    activationGap processingGap gaps plan (serviceGraph_revealRelaxedOrdered setup mode) maximal
    (setup.initialLaw.map encodeInputs)
  simp only [PMF.map_comp, Function.comp_def] at contract
  have responseState := currentStep_state setup mode runtime leaks bounds plan prior values who
    history choice remaining execution current response selected
  have actual : (stoppedFinish setup mode runtime leaks bounds plan prior values who history
      choice).bind (fun result => (seedAt result.2.state).map fun tape =>
        ((decide (originalAdmissionGate setup mode runtime leaks bounds plan prior
            history result.1),
          result.2.state), tape)) =
      ((app).runUntil scheduler players stop remaining afterExecution).bind fun ending =>
        ((app).finish initial horizon scheduler players (pack ending)).bind fun terminal =>
          (seedAt terminal).map fun tape => ((gate (pack ending), terminal), tape) := by
    unfold stoppedFinish
    rw [PMF.bind_bind]
    calc
      _ = (currentStep setup mode runtime leaks bounds plan prior values who history choice).bind
          (fun _ => ((app).runUntil scheduler players stop remaining afterExecution).bind
            fun ending => ((app).finish initial horizon scheduler players (pack ending)).bind
              fun terminal => (seedAt terminal).map fun tape =>
                ((gate (pack ending), terminal), tape)) := by
        apply bind_congr_on_support
        intro after reached
        have afterState : after.state = some ⟨remaining, none, afterExecution⟩ := by
          have member := (PMF.mem_support_map_iff History.state _ _).mpr ⟨after, reached, rfl⟩
          rw [responseState, PMF.mem_support_pure_iff] at member
          exact member
        let afterTrace : (E).Trace (some ⟨remaining, none, afterExecution⟩) :=
          afterState ▸ after.trace
        let originTrace : (E).Trace (some ⟨remaining, some who, execution⟩) :=
          current ▸ history.trace
        have recast (original : (E).History) (state : (E).State)
            (same : original.state = state) :
            (⟨state, same ▸ original.trace⟩ : (E).History) = original := by
          rcases original with ⟨source, trace⟩
          cases same
          rfl
        have originEq : (⟨some ⟨remaining, some who, execution⟩, originTrace⟩ : (E).History) =
            history := recast history _ current
        have afterEq : (⟨some ⟨remaining, none, afterExecution⟩, afterTrace⟩ : (E).History) =
            after := recast after _ afterState
        have retained : TracePrefix history.trace after.trace := by
          change after ∈ ((N).runBehavioralFrom _ 1 history).support at reached
          exact ((N).runBehavioralFrom_reachesWithin _ 1 history after reached).tracePrefix
        have sameAttempt : afterExecution.application.attempt = execution.application.attempt := by
          rcases response with ⟨_ | material⟩ <;> rfl
        have samePhases : afterExecution.application.phases = execution.application.phases := by
          rcases response with ⟨_ | material⟩ <;> rfl
        let exit := fun final : (E).History => match final.state with
          | none => False
          | some control => control.execution.application.attempt ≠ execution.application.attempt
        have originExit :
            attemptExit setup mode runtime leaks bounds plan prior history = exit := by
          funext final
          cases state : final.state <;> simp only [attemptExit, current, state, exit]
        have afterExit : attemptExit setup mode runtime leaks bounds plan prior
            ⟨some ⟨remaining, none, afterExecution⟩, afterTrace⟩ = exit := by
          funext final
          cases state : final.state <;> simp only [attemptExit, state, sameAttempt, exit]
        let stops := (N).runBehavioralUntil certificate plain
          (attemptExit setup mode runtime leaks bounds plan prior history) after
        let normalStops := (N).runBehavioralUntil certificate plain exit
          ⟨some ⟨remaining, none, afterExecution⟩, afterTrace⟩
        have normalizedStops : stops = normalStops :=
          congrArg₂ (fun predicate start =>
            (N).runBehavioralUntil certificate plain predicate start)
            originExit afterEq.symm
        have stopsLaw : stops.map History.state =
            ((app).runUntil scheduler players stop remaining afterExecution).map pack := by
          have law := attemptUntil_state setup mode runtime leaks bounds initial scheduler plain
            execution.application.attempt remaining afterExecution afterTrace
          have normalLaw : normalStops.map History.state =
              ((app).runUntil scheduler players stop remaining afterExecution).map pack := by
            dsimp only [normalStops, exit, certificate, stop, pack]
            rw [decoded] at law
            convert law using 1; congr 1; congr 1
            all_goals
              funext final
              cases state : final.state <;> rfl
          exact (congrArg (PMF.map History.state) normalizedStops).trans normalLaw
        calc
          _ = stops.bind (fun ending => ((app).finish initial horizon scheduler players
              ending.state).bind fun terminal => (seedAt terminal).map fun tape =>
                ((gate ending.state, terminal), tape)) := by
            simp only [PMF.bind_bind, PMF.bind_map, Function.comp_def]
            apply bind_congr_on_support
            intro ending supported
            have retainedCasted : TracePrefix originTrace afterTrace := by
              have same := congrArg₂ (fun left right : (E).History =>
                TracePrefix left.trace right.trace) originEq afterEq
              exact same.symm ▸ retained
            have normalSupported : ending ∈ normalStops.support := normalizedStops ▸ supported
            have gateSupported : ending ∈ ((N).runBehavioralUntil certificate plain
                (attemptExit setup mode runtime leaks bounds plan prior
                  ⟨some ⟨remaining, none, afterExecution⟩, afterTrace⟩)
                ⟨some ⟨remaining, none, afterExecution⟩, afterTrace⟩).support := by
              simpa only [normalStops, afterExit] using normalSupported
            have gateEq := attemptUntil_gate_iff setup mode runtime leaks bounds plan prior
              _ _ contract plain ⟨remaining, none, afterExecution⟩ afterTrace
              ⟨remaining, some who, execution⟩ originTrace retainedCasted
              sameAttempt samePhases phase (by simpa only [samePhases] using installed)
              commitment ending gateSupported
            have gateValue : decide (originalAdmissionGate setup mode runtime leaks bounds plan
                prior history ending) = gate ending.state := by
              dsimp only [gate]
              exact decide_eq_decide.mpr (by simpa only [originEq] using gateEq)
            have retag := congrArg (fun admitted : Bool =>
              ((N).runBehavioralTerminalFrom certificate plain ending).bind fun terminal =>
                (seedAt terminal.state).map fun tape => ((admitted, terminal.state), tape))
                  gateValue
            have terminalLaw := (menu).terminal_run_eq_finish initial horizon scheduler
              certificate plain ending
            rw [decoded] at terminalLaw
            let kernel := fun terminal : (app).ProtocolState =>
              (seedAt terminal).map fun tape => ((gate ending.state, terminal), tape)
            have projected := congrArg (fun law : PMF (app).ProtocolState => law.bind kernel)
              terminalLaw
            have composed := (PMF.bind_map
              ((N).runBehavioralTerminalFrom certificate plain ending) History.state kernel).symm
            exact retag.trans (composed.trans projected)
          _ = _ := by
            simpa only [PMF.bind_map, Function.comp_def] using
              congrArg (fun law => law.bind fun state =>
                ((app).finish initial horizon scheduler players state).bind fun terminal =>
                  (seedAt terminal).map fun tape => ((gate state, terminal), tape)) stopsLaw
      _ = _ := PMF.bind_const _ _
  rw [actual]
  symm
  have stoppedJoint := (app).schedulerMixture_runUntil_joint prior family players stop
    remaining afterExecution
  have transformed := congrArg (fun law => law.bind fun result : (app).Execution ×
      ReservedEpoch.Tape Player tapeLength =>
        ((app).finish initial horizon (family result.2) players (pack result.1)).map
          fun terminal => ((gate (pack result.1), terminal), result.2)) stoppedJoint
  simp only [PMF.bind_bind, PMF.bind_map, Function.comp_def] at transformed
  have startRecall : afterExecution.environmentRecall = execution.environmentRecall :=
    (app).respond_environmentRecall execution who response
  rw [startRecall] at transformed
  calc
    _ = ((app).runUntil scheduler players stop remaining afterExecution).bind fun ending =>
        (mixture.posterior ending.environmentRecall).bind fun tape =>
          ((app).finish initial horizon (family tape) players (pack ending)).map
            fun terminal => ((gate (pack ending), terminal), tape) := by
      simp only [packGate] at transformed ⊢
      simpa only [family, mixture, ReservedEpoch.implementation, pack, afterExecution]
        using transformed
    _ = _ := by
      apply bind_congr_on_support
      intro ending _
      have finished := (app).schedulerMixture_finish_joint prior family initial horizon players
        (pack ending)
      have mapped := congrArg (PMF.map fun result : (app).ProtocolState ×
          ReservedEpoch.Tape Player tapeLength => ((gate (pack ending), result.1), result.2))
            finished
      simp only [pack, family, PMF.map_bind, PMF.map_comp, Function.comp_def] at mapped
      convert mapped using 1; congr 1
      all_goals
        funext terminal
        dsimp only [seedAt, pack, mixture, family]
        congr 1; first | rfl | (cases terminal <;> rfl)



/-- Inclusion of actual component supports preserves ordinary run support
from the same retained enriched history. -/
private theorem ordinary_run_supported
    (steered : ∀ who (key : setup.ProposalRecoveryComponent who),
      PMF (setup.CommitRecoveryValueChoice who key.1))
    (included : ∀ who key choice, choice ∈ (steered who key).support →
      choice ∈ (values who key).support) :
    ∀ fuel (start completed : setup.proposalRecoveryProtocol.History),
      completed ∈ (setup.proposalRecoveryModel.runBehavioralFrom
        (sourceUnflaggedStrategy setup steered) fuel start).support →
      completed ∈ (setup.proposalRecoveryModel.runBehavioralFrom
        (sourceUnflaggedStrategy setup values) fuel start).support := by
  intro fuel
  induction fuel with
  | zero => intro start completed supported; exact supported
  | succ fuel ih =>
    intro start completed supported
    dsimp only [sourceUnflaggedStrategy] at supported ⊢
    rw [setup.proposalRecovery_ordinary_run_succ steered fuel start] at supported
    rw [setup.proposalRecovery_ordinary_run_succ values fuel start]
    obtain ⟨draws, drawn, reached⟩ := Set.mem_iUnion₂.mp
      (PMF.support_bind .. ▸ supported)
    obtain ⟨next, moved, tail⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
    rw [PMF.support_bind]
    refine Set.mem_iUnion₂.mpr ⟨draws, ?_, ?_⟩
    · apply (independentProduct_support_iff _ draws).mpr
      intro who
      exact included who _ (draws who)
        ((independentProduct_support_iff _ draws).mp drawn who)
    · rw [PMF.support_bind]
      exact Set.mem_iUnion₂.mpr ⟨next, moved, ih next completed tail⟩

omit [Fintype Player] [IExpr.ResultTypes L] in
/-- A structural block never emits a binding under an inherited name. -/
private theorem word_action_fresh
    {Γ Δ : SourceCtx Player L} {O P : Finset VarId}
    (block : SourceProgram.CommitPrefix Γ O Δ P) (who : Player)
    (index : Nat) (view : DecisionView who Δ)
    (owner : Player) (name : VarId) (payload : L.Ty)
    (result : PublicationResult (L.Val payload))
    (selected : block.wordAction who index view =
      some (OwnAction.commit owner name payload result)) : name ∉ Γ.map Prod.fst := by
  induction block generalizing index with
  | nil => cases selected
  | @commit Γ O Δ P head actor valueType fresh guard rest ih =>
    cases index with
    | zero =>
      simp only [SourceProgram.CommitPrefix.wordAction] at selected
      split at selected
      · cases Option.some.inj selected
        exact fresh
      · cases selected
    | succ index =>
      have absent := ih index view selected
      exact fun member => absent (List.mem_cons_of_mem _ member)

omit [Fintype Player] [IExpr.ResultTypes L] in
/-- Two addressed reads of one complete block word cannot assign different
results to the same typed source binding name. -/
private theorem word_action_unique
    {Γ Δ : SourceCtx Player L} {O P : Finset VarId}
    (block : SourceProgram.CommitPrefix Γ O Δ P) (who : Player)
    (first second : Nat) (view : DecisionView who Δ)
    (owner : Player) (name : VarId) (payload : L.Ty)
    (left right : PublicationResult (L.Val payload))
    (readLeft : block.wordAction who first view =
      some (OwnAction.commit owner name payload left))
    (readRight : block.wordAction who second view =
      some (OwnAction.commit owner name payload right)) : left = right := by
  induction block generalizing first second with
  | nil => cases readLeft
  | @commit Γ O Δ P head actor valueType fresh guard rest ih =>
    cases first with
    | zero =>
      cases second with
      | zero =>
        have same := Option.some.inj (readLeft.symm.trans readRight)
        simpa only [OwnAction.commit.injEq, heq_eq_eq, true_and] using same
      | succ second =>
        simp only [SourceProgram.CommitPrefix.wordAction] at readLeft
        split at readLeft
        · have names : head = name := congrArg (fun action : OwnAction Player L =>
            match action with
            | .commit _ named _ _ => named
            | .reveal _ named _ => named) (Option.some.inj readLeft)
          have absent := word_action_fresh rest who second view owner name payload right
            readRight
          exact (absent (List.mem_cons.mpr (Or.inl names.symm))).elim
        · cases readLeft
    | succ first =>
      cases second with
      | zero =>
        simp only [SourceProgram.CommitPrefix.wordAction] at readRight
        split at readRight
        · have names : head = name := congrArg (fun action : OwnAction Player L =>
            match action with
            | .commit _ named _ _ => named
            | .reveal _ named _ => named) (Option.some.inj readRight)
          have absent := word_action_fresh rest who first view owner name payload left
            readLeft
          exact (absent (List.mem_cons.mpr (Or.inl names.symm))).elim
        · cases readRight
      | succ second => exact ih first second view readLeft readRight

omit [Fintype Player] [IExpr.ResultTypes L] in
private theorem word_action_commit
    {Γ Δ : SourceCtx Player L} {O P : Finset VarId}
    (block : SourceProgram.CommitPrefix Γ O Δ P) (who : Player) (index : Nat)
    (view : DecisionView who Δ) (action : OwnAction Player L)
    (selected : block.wordAction who index view = some action) :
    ∃ (owner : Player) (name : VarId) (payload : L.Ty)
      (result : PublicationResult (L.Val payload)),
      action = OwnAction.commit owner name payload result := by
  induction block generalizing index with
  | nil => cases selected
  | @commit Γ O Δ P name owner payload fresh guard rest ih =>
      cases index with
      | zero =>
          simp only [SourceProgram.CommitPrefix.wordAction] at selected
          split at selected
          · exact ⟨owner, name, payload, _, (Option.some.inj selected).symm⟩
          · cases selected
      | succ index => exact ih index view selected

omit [Fintype Player] in
/-- Even an unrealized source observation offers commitments at only one
syntactic name and payload. This concerns the actual menu, not a suffix map. -/
private theorem available_commit_shape
    {Γ : SourceCtx Player L} {O : Finset VarId} (who : Player)
    (program : SourceProgram Player L Γ O) (admission : CommitmentInterface program)
    (view : ProtocolView who program)
    (leftOwner rightOwner : Player) (leftName rightName : VarId)
    (leftPayload rightPayload : L.Ty)
    (left : PublicationResult (L.Val leftPayload))
    (right : PublicationResult (L.Val rightPayload))
    (leftOffered : OwnAction.commit leftOwner leftName leftPayload left ∈
      ProtocolView.available who program admission view)
    (rightOffered : OwnAction.commit rightOwner rightName rightPayload right ∈
      ProtocolView.available who program admission view) :
    leftOwner = rightOwner ∧ leftName = rightName ∧ leftPayload = rightPayload := by
  revert admission view
  induction program with
  | ret payoffs => intro admission view leftOffered; cases leftOffered
  | sample name fresh law next ih =>
      intro admission view leftOffered rightOffered
      cases view with
      | inl view => cases leftOffered
      | inr view => exact ih admission view leftOffered rightOffered
  | commit name owner fresh guard next ih =>
      intro admission view leftOffered rightOffered
      cases view with
      | inl view =>
          obtain ⟨first, _firstAdmitted, firstEq⟩ := leftOffered
          obtain ⟨second, _secondAdmitted, secondEq⟩ := rightOffered
          cases firstEq
          cases secondEq
          exact ⟨rfl, rfl, rfl⟩
      | inr view => exact ih (fun site => admission (some site)) view leftOffered rightOffered
  | reveal published owner name fresh selected unresolved next ih =>
      intro admission view leftOffered rightOffered
      cases view with
      | inl view =>
          obtain ⟨disclose, impossible⟩ := leftOffered
          cases impossible
      | inr view => exact ih admission view leftOffered rightOffered

omit [Fintype Player] in
/-- A complete typed block word selects at most one legal ordinary atom at
any source information. No representative actual history is selected. -/
private theorem source_word_choices_unique
    {Γ Δ : SourceCtx Player L} {O P : Finset VarId}
    (block : SourceProgram.CommitPrefix Γ O Δ P) (who : Player) (view : DecisionView who Δ)
    (word : List (OwnAction Player L))
    (readout : ∀ action ∈ word, ∃ index, block.wordAction who index view = some action)
    (information : setup.proposalRecoveryModel.InfoState who)
    (first second : setup.proposalRecoveryModel.Choice who information)
    (firstListed : ∃ action ∈ word,
      first.val = some (ProposalRecoveryMove.ordinary ⟨action, false⟩))
    (secondListed : ∃ action ∈ word,
      second.val = some (ProposalRecoveryMove.ordinary ⟨action, false⟩)) :
    first = second := by
  obtain ⟨leftAction, leftMember, leftSelected⟩ := firstListed
  obtain ⟨rightAction, rightMember, rightSelected⟩ := secondListed
  obtain ⟨leftIndex, leftRead⟩ := readout leftAction leftMember
  obtain ⟨rightIndex, rightRead⟩ := readout rightAction rightMember
  obtain ⟨leftOwner, leftName, leftPayload, left, rfl⟩ :=
    word_action_commit block who leftIndex view leftAction leftRead
  obtain ⟨rightOwner, rightName, rightPayload, right, rfl⟩ :=
    word_action_commit block who rightIndex view rightAction rightRead
  have leftLegal := first.property
  have rightLegal := second.property
  change setup.proposalRecoveryMenu who information first.val at leftLegal
  change setup.proposalRecoveryMenu who information second.val at rightLegal
  rw [leftSelected] at leftLegal
  rw [rightSelected] at rightLegal
  cases observed : information.1.1.1 with
  | none =>
      simp only [Setup.proposalRecoveryMenu, observed, Option.elim_none, and_false] at leftLegal
  | some current =>
      simp only [Setup.proposalRecoveryMenu, observed, Option.elim_some] at leftLegal rightLegal
      obtain ⟨owners, names, payloads⟩ := available_commit_shape who setup.program
        (CommitmentInterface.forfeiture setup.program) current leftOwner rightOwner
          leftName rightName leftPayload rightPayload left right
            leftLegal.2.1.1 rightLegal.2.1.1
      subst rightOwner
      subst rightName
      subst rightPayload
      have same := word_action_unique block who leftIndex rightIndex view leftOwner leftName
        leftPayload left right leftRead rightRead
      apply Subtype.ext
      rw [leftSelected, rightSelected, same]

omit [Fintype Player] in
open Classical in
/-- On a genuine proper steering row, the literal source word selector is
an ordinary component table at the actual query. The table is chosen directly
on that component, without selecting a representative full information. -/
private theorem source_word_component_law
    (word : SourceProgram.History Player L) (who : Player)
    (information : setup.proposalRecoveryModel.InfoState who)
    (proper : ∀ (choice : setup.proposalRecoveryModel.Choice who information)
      action, action ∈ word who →
      choice.val = some (ProposalRecoveryMove.ordinary ⟨action, false⟩) →
        ¬ action.IsFailure)
    (unique : ∀ (first second : setup.proposalRecoveryModel.Choice who information),
      (∃ action ∈ word who,
        first.val = some (ProposalRecoveryMove.ordinary ⟨action, false⟩)) →
      (∃ action ∈ word who,
        second.val = some (ProposalRecoveryMove.ordinary ⟨action, false⟩)) → first = second) :
    let steered : ∀ owner (key : setup.ProposalRecoveryComponent owner),
        PMF (setup.CommitRecoveryValueChoice owner key.1) := fun owner key =>
      if offered : ∃ choice : setup.CommitRecoveryValueChoice owner key.1,
          ∃ action ∈ word owner, choice.val.val = some ⟨action, false⟩ then
        PMF.pure (Classical.choose offered)
      else values owner key
    sourceBlockWordStrategy setup values word who information =
      sourceUnflaggedStrategy setup steered who information := by
  classical
  intro steered
  let key := setup.proposalRecoveryQuery who information
  let restore := fun choice : setup.CommitRecoveryValueChoice who key.1 =>
    (setup.proposalRecoveryComponentChoice who information).symm
      (setup.proposalRecoveryComponentLabelChoice who key false choice.val)
  have restoreRaw (choice : setup.CommitRecoveryValueChoice who key.1)
      (action : OwnAction Player L)
      (selected : choice.val.val = some ⟨action, false⟩) :
      (restore choice).val = some (ProposalRecoveryMove.ordinary ⟨action, false⟩) := by
    change (choice.val.val.map (fun move => ProposalRecoveryMove.label move false)) = _
    rw [selected, Option.map_some, ProposalRecoveryMove.label_false]
  have pull (choice : setup.proposalRecoveryModel.Choice who information)
      (action : OwnAction Player L) (member : action ∈ word who)
      (selected : choice.val = some (ProposalRecoveryMove.ordinary ⟨action, false⟩)) :
      ∃ value : setup.CommitRecoveryValueChoice who key.1,
        value.val.val = some ⟨action, false⟩ := by
    let semantic := setup.proposalRecoveryComponentSemanticChoice who key
      (setup.proposalRecoveryComponentChoice who information choice)
    have raw : semantic.val = some ⟨action, false⟩ := by
      change choice.val.map (·.semantic) = _
      rw [selected]
      rfl
    refine ⟨⟨semantic, ?_⟩, raw⟩
    intro move picked
    rw [raw] at picked
    cases Option.some.inj picked
    exact ⟨rfl, proper choice action member selected⟩
  have offeredIff :
      (∃ choice : setup.proposalRecoveryModel.Choice who information,
        ∃ action ∈ word who,
          choice.val = some (ProposalRecoveryMove.ordinary ⟨action, false⟩)) ↔
      (∃ choice : setup.CommitRecoveryValueChoice who key.1,
        ∃ action ∈ word who, choice.val.val = some ⟨action, false⟩) := by
    constructor
    · rintro ⟨choice, action, member, selected⟩
      obtain ⟨value, raw⟩ := pull choice action member selected
      exact ⟨value, action, member, raw⟩
    · rintro ⟨choice, action, member, selected⟩
      exact ⟨restore choice, action, member, restoreRaw choice action selected⟩
  have ordinary := setup.proposalRecovery_ordinary_choice_law steered who information
  change sourceUnflaggedStrategy setup steered who information =
    (steered who key).map restore at ordinary
  rw [ordinary]
  by_cases offered : ∃ choice : setup.CommitRecoveryValueChoice who key.1,
      ∃ action ∈ word who, choice.val.val = some ⟨action, false⟩
  · have sourceOffered := offeredIff.mpr offered
    change (if available : ∃ choice : setup.proposalRecoveryModel.Choice who information,
        ∃ action ∈ word who,
          choice.val = some (ProposalRecoveryMove.ordinary ⟨action, false⟩) then
      PMF.pure (Classical.choose available)
      else sourceUnflaggedStrategy setup values who information) = _
    rw [dite_eq_left sourceOffered]
    have chosen : steered who key = PMF.pure (Classical.choose offered) := by
      dsimp only [steered]
      rw [dite_eq_left offered]
    rw [chosen, PMF.pure_map]
    apply congrArg PMF.pure
    apply unique
    · exact Classical.choose_spec sourceOffered
    · obtain ⟨action, member, selected⟩ := Classical.choose_spec offered
      exact ⟨action, member, restoreRaw _ action selected⟩
  · have sourceAbsent : ¬ ∃ choice : setup.proposalRecoveryModel.Choice who information,
        ∃ action ∈ word who,
          choice.val = some (ProposalRecoveryMove.ordinary ⟨action, false⟩) :=
      fun witness => offered (offeredIff.mp witness)
    have unchanged : steered who key = values who key := by
      dsimp only [steered]
      rw [dite_eq_right offered]
    rw [unchanged]
    unfold sourceBlockWordStrategy
    rw [dite_eq_right sourceAbsent]
    exact setup.proposalRecovery_ordinary_choice_law values who information

omit [Fintype Player] in
open Classical in
/-- The literal proper block-word strategy is one ordinary component table
on every information. Availability and uniqueness come from its actual menu
and the same typed word; no chosen full-information representative is used. -/
private theorem source_word_strategy_table
    {Γ Δ : SourceCtx Player L} {O P : Finset VarId}
    (block : SourceProgram.CommitPrefix Γ O Δ P) (word : SourceProgram.History Player L)
    (views : ∀ who, DecisionView who Δ)
    (readout : ∀ who action, action ∈ word who →
      ∃ index, block.wordAction who index (views who) = some action)
    (proper : ∀ who action, action ∈ word who → ¬ action.IsFailure) :
    let steered : ∀ owner (key : setup.ProposalRecoveryComponent owner),
        PMF (setup.CommitRecoveryValueChoice owner key.1) := fun owner key =>
      if offered : ∃ choice : setup.CommitRecoveryValueChoice owner key.1,
          ∃ action ∈ word owner, choice.val.val = some ⟨action, false⟩ then
        PMF.pure (Classical.choose offered)
      else values owner key
    sourceBlockWordStrategy setup values word = sourceUnflaggedStrategy setup steered := by
  intro steered
  funext who information
  exact source_word_component_law setup values word who information
    (fun _ action member _ => proper who action member)
    (source_word_choices_unique setup block who (views who) (word who)
      (readout who) information)


omit [Fintype Player] in
/-- No future legal commitment can reuse a name already present in the
inherited typed context, even at an arbitrary view of that residual program. -/
private theorem available_commit_not_in_context
    {Γ : SourceCtx Player L} {O : Finset VarId} (who : Player)
    (program : SourceProgram Player L Γ O) (admission : CommitmentInterface program)
    (view : ProtocolView who program) (owner : Player) (name : VarId)
    (payload : L.Ty) (result : PublicationResult (L.Val payload))
    (offered : OwnAction.commit owner name payload result ∈
      ProtocolView.available who program admission view) : name ∉ Γ.map Prod.fst := by
  revert admission view
  induction program with
  | ret payoffs => intro admission view offered; cases offered
  | sample nextName fresh law next ih =>
      intro admission view offered inherited
      cases view with
      | inl view => cases offered
      | inr view =>
          exact ih admission view offered (List.mem_cons_of_mem _ inherited)
  | commit nextName nextOwner fresh guard next ih =>
      intro admission view offered inherited
      cases view with
      | inl view =>
          obtain ⟨chosen, _admitted, same⟩ := offered
          cases same
          exact fresh inherited
      | inr view =>
          exact ih (fun site => admission (some site)) view offered
            (List.mem_cons_of_mem _ inherited)
  | reveal published nextOwner selectedName fresh selected unresolved next ih =>
      intro admission view offered inherited
      cases view with
      | inl view =>
          obtain ⟨disclose, impossible⟩ := offered
          cases impossible
      | inr view =>
          exact ih admission view offered (List.mem_cons_of_mem _ inherited)

omit [Fintype Player] in
/-- Literal past focal commitments cannot be selected again at a genuine
remaining source suffix. The assertion concerns the actual trace menu. -/
private theorem source_word_focal_past
    {Γ : SourceCtx Player L} {O : Finset VarId}
    (program : SourceProgram Player L Γ O)
    (lift : ProtocolState program → ProtocolState setup.program)
    (origin : ProtocolSuffix setup.program program lift)
    (current : CommitRecoveryState setup.program)
    (trace : setup.proposalRecoveryProtocol.Trace (some current))
    (point : ProtocolState program) (atPoint : current.point = lift point)
    (who : Player) (word : SourceProgram.History Player L)
    (past : ∀ action ∈ word who, ∃ owner name payload result,
      action = OwnAction.commit owner name payload result ∧ name ∈ Γ.map Prod.fst) :
    sourceBlockWordStrategy setup values word who
        (setup.proposalRecoveryModel.infoOf who trace) =
      sourceUnflaggedStrategy setup values who
        (setup.proposalRecoveryModel.infoOf who trace) := by
  classical
  unfold sourceBlockWordStrategy
  rw [dite_eq_right]
  rintro ⟨choice, action, member, selected⟩
  obtain ⟨owner, name, payload, result, rfl, inherited⟩ := past action member
  have legal := (setup.proposalRecoveryMenu_adequate who trace choice.val).mp choice.property
  rw [selected] at legal
  have offered : (⟨OwnAction.commit owner name payload result, false⟩ :
      CommitRecoveryMove Player L) ∈ ProtocolView.recoveryAvailable who setup.program
        (ProtocolState.observe who setup.program current.point) := legal.2.1
  rw [atPoint, origin.recoveryAvailable who point] at offered
  exact (available_commit_not_in_context who program
    (CommitmentInterface.forfeiture program) (ProtocolState.observe who program point)
      owner name payload result offered.1) inherited

/-- After the focal listed prefix, the actual remaining runner uses the
original focal table. Foreign steering and the full source history are kept. -/
private theorem source_word_run_past
    (steered : ∀ owner (key : setup.ProposalRecoveryComponent owner),
      PMF (setup.CommitRecoveryValueChoice owner key.1))
    (word : SourceProgram.History Player L)
    (strategy : sourceBlockWordStrategy setup values word =
      sourceUnflaggedStrategy setup steered) (who : Player)
    {Γ Δ : SourceCtx Player L} {O P : Finset VarId}
    (block : SourceProgram.CommitPrefix Γ O Δ P) :
    ∀ (suffix : SourceProgram Player L Δ P)
      (lift : ProtocolState (block.prepend suffix) → ProtocolState setup.program)
      (_origin : ProtocolSuffix setup.program (block.prepend suffix) lift)
      (source : SourceProgram.Config Player L Γ)
      (current : CommitRecoveryState setup.program)
      (trace : setup.proposalRecoveryProtocol.Trace (some current)),
      current.point = lift (ProtocolState.entry (block.prepend suffix) source) →
      current.excluded = current.entryExcluded →
      (∀ action ∈ word who, ∃ owner name payload result,
        action = OwnAction.commit owner name payload result ∧ name ∈ Γ.map Prod.fst) →
      setup.proposalRecoveryModel.runBehavioralFrom (sourceUnflaggedStrategy setup steered)
          block.length ⟨some current, trace⟩ =
        setup.proposalRecoveryModel.runBehavioralFrom
          (sourceUnflaggedStrategy setup (fun owner key =>
            if owner = who then values owner key else steered owner key))
          block.length ⟨some current, trace⟩ := by
  classical
  let hybrid := fun owner (key : setup.ProposalRecoveryComponent owner) =>
    if owner = who then values owner key else steered owner key
  induction block with
  | nil => intro suffix lift origin source current trace point ordinary past; rfl
  | @commit Γ O Δ P name owner payload fresh guard rest ih =>
      intro suffix lift origin source current trace point ordinary past
      let first := sourceUnflaggedStrategy setup steered
      let second := sourceUnflaggedStrategy setup hybrid
      have policies : ∀ player,
          first player (setup.proposalRecoveryModel.infoOf player trace) =
            second player (setup.proposalRecoveryModel.infoOf player trace) := by
        intro player
        by_cases same : player = who
        · subst player
          change sourceUnflaggedStrategy setup steered who _ = _
          rw [← strategy, source_word_focal_past setup values _ lift origin current trace
            _ point who word past]
          change sourceUnflaggedStrategy setup values who _ =
            sourceUnflaggedStrategy setup hybrid who _
          simp only [sourceUnflaggedStrategy, setup.proposalRecovery_ordinary_choice_law,
            hybrid, ite_true]
        · change sourceUnflaggedStrategy setup steered player _ =
            sourceUnflaggedStrategy setup hybrid player _
          simp only [sourceUnflaggedStrategy, setup.proposalRecovery_ordinary_choice_law,
            hybrid, ite_eq_right same]
      have oneStep : setup.proposalRecoveryModel.runBehavioralFrom first 1
            ⟨some current, trace⟩ =
          setup.proposalRecoveryModel.runBehavioralFrom second 1 ⟨some current, trace⟩ := by
        by_cases terminal : setup.proposalRecoveryProtocol.terminal (some current)
        · rw [setup.proposalRecoveryModel.runBehavioralFrom_of_terminal first 1 terminal,
            setup.proposalRecoveryModel.runBehavioralFrom_of_terminal second 1 terminal]
        · rw [setup.proposalRecoveryModel.runBehavioralFrom_succ_of_not_terminal first 0 terminal,
            setup.proposalRecoveryModel.runBehavioralFrom_succ_of_not_terminal second 0 terminal,
            setup.proposalRecoveryModel.behavioralJoint_congr trace terminal policies]
          rfl
      change setup.proposalRecoveryModel.runBehavioralFrom first (rest.length + 1) _ =
        setup.proposalRecoveryModel.runBehavioralFrom second (rest.length + 1) _
      rw [Nat.add_comm rest.length 1,
        setup.proposalRecoveryModel.runBehavioralFrom_add first 1 rest.length,
        setup.proposalRecoveryModel.runBehavioralFrom_add second 1 rest.length, ← oneStep]
      apply bind_congr_on_support
      intro next supported
      let head : SourceProgram.CommitPrefix Γ O ((name, .commitment owner payload) :: Γ)
        (insert name O) :=
        .commit name owner fresh guard .nil
      obtain ⟨middle, last, lastTrace, _attempt, nextEq, lastPoint, lastExcluded,
          lastEntry, _generation, _word, _labels, _proper⟩ :=
        proposalRecovery_ordinary_commit_block_support setup steered head
          (rest.prepend suffix) lift origin source current trace point ordinary next supported
      subst next
      apply ih suffix (fun state => lift (.inr state))
        (ProtocolSuffix.commitTail fresh guard (rest.prepend suffix) origin)
        middle last lastTrace lastPoint (lastExcluded.trans lastEntry.symm)
      intro action member
      obtain ⟨player, oldName, oldPayload, result, equal, inherited⟩ := past action member
      exact ⟨player, oldName, oldPayload, result, equal, List.mem_cons_of_mem _ inherited⟩

/-- Erasing only inherited excluded owners' lists preserves the actual
runner. Such owners stay inactive along every genuine source continuation. -/
private theorem source_word_run_mask_excluded
    (word : SourceProgram.History Player L) (excluded : Finset Player)
    (start : setup.proposalRecoveryProtocol.History) (fuel : Nat)
    (inherited : excluded ⊆ (setup.commitRecoveryPublic start.state).1) :
    setup.proposalRecoveryModel.runBehavioralFrom
        (sourceBlockWordStrategy setup values word) fuel start =
      setup.proposalRecoveryModel.runBehavioralFrom
        (sourceBlockWordStrategy setup values (fun owner =>
          if owner ∈ excluded then [] else word owner))
        fuel start := by
  classical
  apply setup.proposalRecoveryModel.runBehavioralFrom_congr fuel start
  intro later reached _running owner
  have retained := setup.commitRecovery_public_excluded_of_reaches
    (proposalRecovery_reaches_semantic setup reached)
  by_cases omitted : owner ∈ excluded
  · have inactive : ¬ setup.proposalRecoveryProtocol.active later.state owner := by
      have present := retained (inherited omitted)
      cases state : later.state with
      | none => exact not_false
      | some current =>
          have now : owner ∈ current.excluded := by
            simpa only [Setup.commitRecoveryPublic, state] using present
          change ¬ current.Active owner
          exact fun active => active.2 now
    have absent : ¬ ∃ choice : setup.proposalRecoveryModel.Choice owner
        (setup.proposalRecoveryModel.infoOf owner later.trace),
        ∃ action ∈ word owner,
          choice.val = some (ProposalRecoveryMove.ordinary ⟨action, false⟩) := by
      rintro ⟨choice, action, _member, selected⟩
      have legal := (setup.proposalRecoveryMenu_adequate owner later.trace choice.val).mp
        choice.property
      rw [selected] at legal
      exact inactive legal.1
    unfold sourceBlockWordStrategy
    rw [dite_eq_right absent]
    simp only [ite_eq_left omitted, List.not_mem_nil, false_and, exists_false, dite_false]
  · unfold sourceBlockWordStrategy
    simp only [ite_eq_right omitted]


/-- Inactive-list erasure retains the actual static cut together with its
completed history. The second runner keeps that same cut and its real fuel. -/
private theorem source_word_cut_mask_excluded
    (word : SourceProgram.History Player L) (excluded : Finset Player)
    (entry : setup.proposalRecoveryProtocol.History) (before : Nat)
    (inherited : excluded ⊆ (setup.commitRecoveryPublic entry.state).1) :
    ((setup.proposalRecoveryModel.runBehavioralFrom
        (sourceBlockWordStrategy setup values word) before entry).bind fun cut =>
      (setup.proposalRecoveryModel.runBehavioralFrom
        (sourceBlockWordStrategy setup values word) (sourceCommitFuel setup cut) cut).map
          (fun completed => (cut, completed))) =
    ((setup.proposalRecoveryModel.runBehavioralFrom
        (sourceBlockWordStrategy setup values (fun owner =>
          if owner ∈ excluded then [] else word owner)) before entry).bind fun cut =>
      (setup.proposalRecoveryModel.runBehavioralFrom
        (sourceBlockWordStrategy setup values (fun owner =>
          if owner ∈ excluded then [] else word owner)) (sourceCommitFuel setup cut) cut).map
          (fun completed => (cut, completed))) := by
  rw [← source_word_run_mask_excluded setup values word excluded entry before inherited]
  apply bind_congr_on_support
  intro cut supported
  have reached := setup.proposalRecoveryProtocol.runRandomizedFor_reachesWithin
    (setup.proposalRecoveryModel.randomizedChooser (sourceBlockWordStrategy setup values word))
      before entry cut supported
  have retained := setup.commitRecovery_public_excluded_of_reaches
    (proposalRecovery_reaches_semantic setup reached)
  exact congrArg (PMF.map (fun completed => (cut, completed)))
    (source_word_run_mask_excluded setup values word excluded cut (sourceCommitFuel setup cut)
      (inherited.trans retained))

/-- A listed genuine joint move is followed by the actual original local
step. Inactive coordinates are forced by legality, not conditioned as values. -/
private theorem source_word_forced_step
    {Γ Δ : SourceCtx Player L} {O P : Finset VarId}
    (block : SourceProgram.CommitPrefix Γ O Δ P) (word : SourceProgram.History Player L)
    (views : ∀ owner, DecisionView owner Δ)
    (readout : ∀ owner action, action ∈ word owner →
      ∃ index, block.wordAction owner index (views owner) = some action)
    (history : setup.proposalRecoveryProtocol.History)
    (choices : ∀ owner, setup.proposalRecoveryModel.Choice owner
      (setup.proposalRecoveryModel.infoOf owner history.trace))
    (listed : ∀ owner move, (choices owner).val = some move →
      ∃ action ∈ word owner, move = ProposalRecoveryMove.ordinary ⟨action, false⟩) :
    setup.proposalRecoveryModel.runBehavioralFrom
        (sourceBlockWordStrategy setup values word) 1 history =
      setup.proposalRecoveryModel.localStep history choices := by
  classical
  have policies : ∀ owner,
      sourceBlockWordStrategy setup values word owner
          (setup.proposalRecoveryModel.infoOf owner history.trace) = PMF.pure (choices owner) := by
    intro owner
    cases selected : (choices owner).val with
    | none =>
        have inactive := (choices owner).property
        change setup.proposalRecoveryMenu owner _ (choices owner).val at inactive
        rw [selected] at inactive
        change ¬ setup.proposalRecoveryActive owner _ at inactive
        apply pmf_eq_pure_of_support_subset_singleton
        intro chosen _supported
        apply Subtype.ext
        cases chosenValue : chosen.val with
        | none => exact selected.symm
        | some move =>
            have legal := chosen.property
            change setup.proposalRecoveryMenu owner _ chosen.val at legal
            rw [chosenValue] at legal
            exact (inactive legal.1).elim
    | some move =>
        obtain ⟨action, member, rfl⟩ := listed owner move selected
        have offered : ∃ choice : setup.proposalRecoveryModel.Choice owner
            (setup.proposalRecoveryModel.infoOf owner history.trace),
            ∃ action ∈ word owner,
              choice.val = some (ProposalRecoveryMove.ordinary ⟨action, false⟩) :=
          ⟨choices owner, action, member, selected⟩
        unfold sourceBlockWordStrategy
        rw [dite_eq_left offered]
        apply congrArg PMF.pure
        exact source_word_choices_unique setup block owner (views owner) (word owner)
          (readout owner) _ _ _ (Classical.choose_spec offered) ⟨action, member, selected⟩
  rw [setup.proposalRecoveryModel.runBehavioralFrom_succ_localStep]
  simp_rw [policies]
  rw [independentProduct_pure, PMF.pure_bind]
  change (setup.proposalRecoveryModel.localStep history choices).bind PMF.pure = _
  exact PMF.bind_pure _

/-- A covered ordinary prefix is replayed literally from its original entry.
Only the genuine supported prefix word is forced; its original past is kept. -/
private theorem source_word_forced_prefix
    {baseΓ endΓ : SourceCtx Player L} {baseO endO : Finset VarId}
    (wordBlock : SourceProgram.CommitPrefix baseΓ baseO endΓ endO)
    (word : SourceProgram.History Player L) (views : ∀ owner, DecisionView owner endΓ)
    (readout : ∀ owner action, action ∈ word owner →
      ∃ index, wordBlock.wordAction owner index (views owner) = some action)
    {Γ Δ : SourceCtx Player L} {O P : Finset VarId}
    (block : SourceProgram.CommitPrefix Γ O Δ P) :
    ∀ (suffix : SourceProgram Player L Δ P)
      (lift : ProtocolState (block.prepend suffix) → ProtocolState setup.program)
      (_origin : ProtocolSuffix setup.program (block.prepend suffix) lift)
      (source : SourceProgram.Config Player L Γ)
      (current : CommitRecoveryState setup.program)
      (trace : setup.proposalRecoveryProtocol.Trace (some current)),
      current.point = lift (ProtocolState.entry (block.prepend suffix) source) →
      current.excluded = current.entryExcluded →
      ∀ target : setup.proposalRecoveryProtocol.History,
      target ∈ (setup.proposalRecoveryModel.runBehavioralFrom
        (sourceUnflaggedStrategy setup values) block.length ⟨some current, trace⟩).support →
      (∀ joint ∈ ((setup.proposalRecoveryJointRecall target.trace).take block.length).reverse,
        ∀ owner move, joint owner = some move →
          ∃ action ∈ word owner, move = ProposalRecoveryMove.ordinary ⟨action, false⟩) →
      setup.proposalRecoveryModel.runBehavioralFrom
        (sourceBlockWordStrategy setup values word) block.length ⟨some current, trace⟩ =
          PMF.pure target := by
  classical
  let original := sourceUnflaggedStrategy setup values
  let forced := sourceBlockWordStrategy setup values word
  induction block with
  | nil =>
      intro suffix lift origin source current trace point ordinary target supported _covered
      have same : target = ⟨some current, trace⟩ := (PMF.mem_support_pure_iff ..).mp supported
      subst target
      rfl
  | @commit Γ O Δ P name owner payload fresh guard rest ih =>
      intro suffix lift origin source current trace point ordinary target supported covered
      change target ∈ (setup.proposalRecoveryModel.runBehavioralFrom original
        (rest.length + 1) ⟨some current, trace⟩).support at supported
      rw [Nat.add_comm rest.length 1,
        setup.proposalRecoveryModel.runBehavioralFrom_add original 1 rest.length] at supported
      obtain ⟨middle, headSupport, tailSupport⟩ := (PMF.mem_support_bind_iff ..).mp supported
      have oneLaw : setup.proposalRecoveryModel.runBehavioralFrom original 1
          ⟨some current, trace⟩ =
          (independentProduct (fun player => original player
            (setup.proposalRecoveryModel.infoOf player trace))).bind
              (setup.proposalRecoveryModel.localStep ⟨some current, trace⟩) := by
        rw [setup.proposalRecoveryModel.runBehavioralFrom_succ_localStep]
        exact PMF.bind_pure _
      have headDraw := headSupport
      rw [oneLaw] at headDraw
      obtain ⟨choices, _choiceSupport, localSupport⟩ := (PMF.mem_support_bind_iff ..).mp headDraw
      let head : SourceProgram.CommitPrefix Γ O ((name, .commitment owner payload) :: Γ)
        (insert name O) :=
        .commit name owner fresh guard .nil
      obtain ⟨middleSource, after, afterTrace, _headAttempt, middleEq, afterPoint,
          afterExcluded, afterEntry, _afterGeneration, _afterWord, _afterLabels⟩ :=
        proposalRecovery_ordinary_commit_block_support setup values head
          (rest.prepend suffix) lift origin source current trace point ordinary middle headSupport
      subst middle
      obtain ⟨_finished, _owners, _attempt, _monotone, _headWord, _middleState, _semantic,
          middleLabels⟩ := proposalRecovery_localStep_commit_attempt setup fresh guard
            (rest.prepend suffix) lift origin source current trace point choices
              ⟨some after, afterTrace⟩ localSupport
      obtain ⟨finished, last, lastTrace, tailAttempt, targetEq, _lastPoint, _lastExcluded,
          _lastEntry, _lastGeneration, _lastWord, tailLabels, _tailProper⟩ :=
        proposalRecovery_ordinary_commit_block_support setup values rest suffix
          (fun state => lift (.inr state))
          (ProtocolSuffix.commitTail fresh guard (rest.prepend suffix) origin)
          middleSource after afterTrace afterPoint (afterExcluded.trans afterEntry.symm)
          target tailSupport
      subst target
      let tailWord : List (Player → Option (ProposalRecoveryMove Player L)) :=
        tailAttempt.joints.map
        (fun joint player => (joint player).map ProposalRecoveryMove.ordinary)
      have tailSize : tailWord.length = rest.length := by
        simp only [tailWord, List.length_map, tailAttempt.joints_length]
      have tailRead : ((setup.proposalRecoveryJointRecall lastTrace).take rest.length).reverse =
          tailWord := by
        rw [tailLabels, List.map_reverse]
        change ((tailWord.reverse ++ setup.proposalRecoveryJointRecall afterTrace).take
          rest.length).reverse = tailWord
        rw [← tailSize, ← List.length_reverse (as := tailWord), List.take_left,
          List.reverse_reverse]
      have listRead (past middle final tail : List (Player → Option
          (ProposalRecoveryMove Player L))) (headJoint : Player → Option
          (ProposalRecoveryMove Player L)) (length : Nat)
          (size : tail.length = length) (one : middle = headJoint :: past)
          (many : final = tail.reverse ++ middle) :
          (final.take (length + 1)).reverse = headJoint :: tail := by
        rw [many, one, ← List.singleton_append, ← List.append_assoc, ← List.reverse_cons]
        have size' : (headJoint :: tail).reverse.length = length + 1 := by
          simp only [List.length_reverse, List.length_cons, size]
        exact (congrArg List.reverse (List.take_left' size')).trans
          (List.reverse_reverse _)
      have tailLabels' : setup.proposalRecoveryJointRecall lastTrace =
          tailWord.reverse ++ setup.proposalRecoveryJointRecall afterTrace := by
        simpa only [tailWord, List.map_reverse] using tailLabels
      have allRead : ((setup.proposalRecoveryJointRecall lastTrace).take
          (rest.length + 1)).reverse =
            (fun player => (choices player).val) :: tailWord :=
        listRead (setup.proposalRecoveryJointRecall trace)
          (setup.proposalRecoveryJointRecall afterTrace)
          (setup.proposalRecoveryJointRecall lastTrace) tailWord
          (fun player => (choices player).val) rest.length tailSize middleLabels tailLabels'
      change ∀ joint ∈ ((setup.proposalRecoveryJointRecall lastTrace).take
        (rest.length + 1)).reverse, _ at covered
      rw [allRead] at covered
      have listed : ∀ player move, (choices player).val = some move →
          ∃ action ∈ word player, move = ProposalRecoveryMove.ordinary ⟨action, false⟩ :=
        covered _ (List.mem_cons_self ..)
      have forcedHead := source_word_forced_step setup values wordBlock word views readout
        ⟨some current, trace⟩ choices listed
      have localPure : setup.proposalRecoveryModel.localStep ⟨some current, trace⟩ choices =
          PMF.pure ⟨some after, afterTrace⟩ := by
        by_cases running : setup.proposalRecoveryProtocol.terminal (some current)
        · simp only [InformationModel.localStep, dite_eq_left running] at localSupport ⊢
          have same := (PMF.mem_support_pure_iff ..).mp localSupport
          rw [same]
        · have committing : ProtocolState.atCommit setup.program current.point = true := by
            rw [point, origin.atCommit_lift]
            rfl
          apply pmf_eq_pure_of_support_subset_singleton
          intro other otherSupport
          rw [InformationModel.localStep, dite_eq_right running,
            PMF.mem_support_bindOnSupport_iff] at localSupport otherSupport
          obtain ⟨firstState, firstReached, firstEq⟩ := localSupport
          obtain ⟨secondState, secondReached, secondEq⟩ := otherSupport
          rw [PMF.mem_support_pure_iff] at firstEq secondEq
          subst other
          rw [firstEq]
          change firstState ∈ ((current.step
            (Setup.proposalRecoveryJoint (fun player => (choices player).val))).map some).support
              at firstReached
          change secondState ∈ ((current.step
            (Setup.proposalRecoveryJoint (fun player => (choices player).val))).map some).support
              at secondReached
          obtain ⟨first, firstMember, rfl⟩ := (PMF.mem_support_map_iff some
            (current.step (Setup.proposalRecoveryJoint (fun player => (choices player).val)))
            firstState).mp firstReached
          obtain ⟨second, secondMember, rfl⟩ := (PMF.mem_support_map_iff some
            (current.step (Setup.proposalRecoveryJoint (fun player => (choices player).val)))
            secondState).mp secondReached
          have same := current.step_unique_of_commit committing
            (Setup.proposalRecoveryJoint (fun player => (choices player).val))
              first second firstMember secondMember
          cases same
          rfl
      change setup.proposalRecoveryModel.runBehavioralFrom forced (rest.length + 1)
        ⟨some current, trace⟩ = _
      rw [Nat.add_comm rest.length 1,
        setup.proposalRecoveryModel.runBehavioralFrom_add forced 1 rest.length,
        forcedHead, localPure, PMF.pure_bind]
      apply ih suffix (fun state => lift (.inr state))
        (ProtocolSuffix.commitTail fresh guard (rest.prepend suffix) origin)
        middleSource after afterTrace afterPoint (afterExcluded.trans afterEntry.symm)
        ⟨some last, lastTrace⟩ tailSupport
      rw [tailRead]
      intro joint member
      exact covered joint (List.mem_cons_of_mem _ member)

/-- The original-entry structural policy for one owner uses only that owner's
component table, including at all updated private views. -/
private theorem ordinary_block_owner_table
    (other : ∀ owner (key : setup.ProposalRecoveryComponent owner),
      PMF (setup.CommitRecoveryValueChoice owner key.1)) (who : Player)
    (same : ∀ key, values who key = other who key)
    {Γ Δ : SourceCtx Player L} {O P : Finset VarId}
    (block : SourceProgram.CommitPrefix Γ O Δ P) :
    ∀ (suffix : SourceProgram Player L Δ P)
      (embedding : OutputEmbedding (inputLayout setup.context)
        (outputLayout setup.program) (block.prepend suffix))
      (views : ∀ owner, ProtocolView owner (block.prepend suffix) →
        ProtocolView owner setup.program)
      (controls : Finset Player × Nat × Nat)
      (publicFrame : PhasePublicView (serviceGraph setup mode))
      (archive : Finset (ProposalRecoveryProposal L)),
      ordinaryBlockProfile setup mode plan values block suffix embedding views
          controls publicFrame archive who =
        ordinaryBlockProfile setup mode plan other block suffix embedding views
          controls publicFrame archive who := by
  classical
  induction block with
  | nil => intros; rfl
  | commit name owner fresh guard rest ih =>
      intro suffix embedding views controls publicFrame archive
      apply Prod.ext
      · funext owned observed
        subst who
        simp only [ordinaryBlockProfile, ordinaryBlockProfile.buildProfile]
        split
        · rfl
        · rw [same]
      · exact ih suffix _ _ controls publicFrame archive

/-- At the original saved entry, changing foreign component tables does not
change the focal chronological source word. Inherited excluded rows stay NONE. -/
private theorem ordinary_source_owned_word_law
    (other : ∀ owner (key : setup.ProposalRecoveryComponent owner),
      PMF (setup.CommitRecoveryValueChoice owner key.1)) (who : Player)
    (same : ∀ key, values who key = other who key)
    (sourceInitial : PMF (app).State) (fuel : Nat) (serviceScheduler : (app).Scheduler)
    (anchor : (app).Control)
    (anchorTrace : ((app).protocol sourceInitial fuel serviceScheduler).Trace (some anchor))
    (phase : RuntimePhase (serviceGraph setup mode))
    {Γ Δ : SourceCtx Player L} {O P : Finset VarId}
    (block : SourceProgram.CommitPrefix Γ O Δ P) (suffix : SourceProgram Player L Δ P)
    (cursor : PhaseProposalOrdinarySourceCursor setup mode runtime leaks plan anchor phase
      block suffix) :
    (setup.proposalRecoveryModel.runBehavioralFrom
      (sourceUnflaggedStrategy setup values) block.length
      ⟨some cursor.current, cursor.trace⟩).map
        (fun history => (((setup.recoveryJointRecall
          (setup.proposalRecoveryEraseTrace history.trace)).take block.length).reverse).map
            (fun joint => joint who)) =
      (setup.proposalRecoveryModel.runBehavioralFrom
        (sourceUnflaggedStrategy setup other) block.length
        ⟨some cursor.current, cursor.trace⟩).map
          (fun history => (((setup.recoveryJointRecall
            (setup.proposalRecoveryEraseTrace history.trace)).take block.length).reverse).map
              (fun joint => joint who)) := by
  classical
  have left := ordinaryBlockProfile_source_word_law setup mode runtime leaks plan
    sourceInitial fuel serviceScheduler anchor anchorTrace phase values block suffix cursor
  have right := ordinaryBlockProfile_source_word_law setup mode runtime leaks plan
    sourceInitial fuel serviceScheduler anchor anchorTrace phase other block suffix cursor
  dsimp only at left right
  have leftOwned := congrArg (fun law => law.map (fun word => word.map (fun row => row who))) left
  have rightOwned := congrArg (fun law => law.map (fun word => word.map (fun row => row who))) right
  simp only [PMF.map_comp, List.map_map, Function.comp_def] at leftOwned rightOwned
  refine leftOwned.symm.trans (Eq.trans ?_ rightOwned)
  let controls : Finset Player × Nat × Nat :=
    ((anchor.execution.application.publicView.retired.map fun record =>
      record.2.sourceFailureFootprint.2).foldr (fun first last => first ∪ last) ∅ ∪
        anchor.execution.application.current.native.publicView.sourceFailureFootprint.1
          anchor.execution.application.attempt.phase,
      anchor.execution.application.attempt.generation, anchor.execution.application.attempt.phase)
  let typed := fun table => ordinaryBlockProfile setup mode plan table block suffix cursor.embedding
    (fun owner view => cursor.views.view owner view) controls
    anchor.execution.application.publicView
    (PhaseProposal.sourceArchive anchor.execution.network.inputs)
  have ownerPolicy : typed values who = typed other who :=
    ordinary_block_owner_table setup mode plan values other who same block suffix _ _ _ _ _
  have ownerView := block.prefixLaw_view_eq suffix (typed values) (typed other) who
    ownerPolicy cursor.source cursor.source rfl
  have mapped := congrArg (fun law => law.map (fun view =>
    (List.range block.length).map fun index =>
      if who ∈ cursor.current.excluded then none else
        (block.wordAction who index view).map
          (fun action => (⟨action, false⟩ : CommitRecoveryMove Player L)))) ownerView
  simpa only [PMF.map_comp, Function.comp_def, typed, controls] using mapped

/-- Conditioning a supported ordinary prefix on its complete current word
retains its unique enriched history, with no change to the original entry. -/
private theorem ordinary_source_prefix_posterior
    {Γ Δ : SourceCtx Player L} {O P : Finset VarId}
    (block : SourceProgram.CommitPrefix Γ O Δ P) (suffix : SourceProgram Player L Δ P)
    (lift : ProtocolState (block.prepend suffix) → ProtocolState setup.program)
    (origin : ProtocolSuffix setup.program (block.prepend suffix) lift)
    (source : SourceProgram.Config Player L Γ)
    (current : CommitRecoveryState setup.program)
    (trace : setup.proposalRecoveryProtocol.Trace (some current))
    (point : current.point = lift (ProtocolState.entry (block.prepend suffix) source))
    (ordinary : current.excluded = current.entryExcluded) (positive : 0 < block.length)
    (target : setup.proposalRecoveryProtocol.History)
    (supported : target ∈ (setup.proposalRecoveryModel.runBehavioralFrom
      (sourceUnflaggedStrategy setup values) block.length ⟨some current, trace⟩).support) :
    let law := setup.proposalRecoveryModel.runBehavioralFrom
      (sourceUnflaggedStrategy setup values) block.length ⟨some current, trace⟩
    let read := fun history : setup.proposalRecoveryProtocol.History =>
      ((setup.recoveryJointRecall
        (setup.proposalRecoveryEraseTrace history.trace)).take block.length).reverse
    fiberPosterior law read (read target) = PMF.pure target := by
  classical
  intro law read
  have present : read target ∈ (law.map read).support :=
    (PMF.mem_support_map_iff ..).mpr ⟨target, supported, rfl⟩
  apply pmf_eq_pure_of_support_subset_singleton
  intro candidate admitted
  obtain ⟨same, reached⟩ := mem_support_fiberPosterior present admitted
  change candidate = target
  exact proposalRecovery_ordinary_commit_history_injective setup values block suffix
    lift origin source current trace point ordinary positive candidate target reached supported same

/-- Prefix conditioning is performed inside one genuine source run. The
remaining kernel keeps the selected enriched history and its updated queries. -/
private theorem ordinary_source_run_prefix_conditioned
    {Γ Δ Ξ : SourceCtx Player L} {O P Q : Finset VarId}
    (before : SourceProgram.CommitPrefix Γ O Δ P) (after : SourceProgram.CommitPrefix Δ P Ξ Q)
    (suffix : SourceProgram Player L Ξ Q)
    (lift : ProtocolState (before.prepend (after.prepend suffix)) →
      ProtocolState setup.program)
    (origin : ProtocolSuffix setup.program (before.prepend (after.prepend suffix)) lift)
    (source : SourceProgram.Config Player L Γ)
    (current : CommitRecoveryState setup.program)
    (trace : setup.proposalRecoveryProtocol.Trace (some current))
    (point : current.point = lift
      (ProtocolState.entry (before.prepend (after.prepend suffix)) source))
    (ordinary : current.excluded = current.entryExcluded) (positive : 0 < before.length)
    (target : setup.proposalRecoveryProtocol.History)
    (supported : target ∈ (setup.proposalRecoveryModel.runBehavioralFrom
      (sourceUnflaggedStrategy setup values) before.length ⟨some current, trace⟩).support) :
    let read := fun history : setup.proposalRecoveryProtocol.History =>
      ((setup.recoveryJointRecall
        (setup.proposalRecoveryEraseTrace history.trace)).take before.length).reverse
    let finalRead := fun history : setup.proposalRecoveryProtocol.History =>
      (((setup.recoveryJointRecall (setup.proposalRecoveryEraseTrace history.trace)).take
        (before.length + after.length)).reverse).take before.length
    fiberPosterior (setup.proposalRecoveryModel.runBehavioralFrom
      (sourceUnflaggedStrategy setup values) (before.length + after.length)
        ⟨some current, trace⟩) finalRead (read target) =
      setup.proposalRecoveryModel.runBehavioralFrom
        (sourceUnflaggedStrategy setup values) after.length target := by
  classical
  intro read finalRead
  let prior := setup.proposalRecoveryModel.runBehavioralFrom
    (sourceUnflaggedStrategy setup values) before.length ⟨some current, trace⟩
  let tail := setup.proposalRecoveryModel.runBehavioralFrom
    (sourceUnflaggedStrategy setup values) after.length
  have present : read target ∈ (prior.map read).support :=
    (PMF.mem_support_map_iff ..).mpr ⟨target, supported, rfl⟩
  have retained : ∀ middle ∈ prior.support, ∀ final ∈ (tail middle).support,
      finalRead final = read middle := by
    intro middle reached final continued
    obtain ⟨middleSource, middleState, middleTrace, firstAttempt, middleEq, middlePoint,
        middleExcluded, middleEntry, _generation, middleWord, _labels, _proper⟩ :=
      proposalRecovery_ordinary_commit_block_support setup values before (after.prepend suffix)
        lift origin source current trace point ordinary middle reached
    subst middle
    obtain ⟨lastSource, last, lastTrace, lastAttempt, finalEq, _lastPoint, _lastExcluded,
        _lastEntry, _lastGeneration, lastWord, _lastLabels, _lastProper⟩ :=
      proposalRecovery_ordinary_commit_block_support setup values after suffix
        (fun state => lift (before.liftPoint (after.prepend suffix) state))
        (origin.compose (before.protocolSuffix (after.prepend suffix)))
        middleSource middleState middleTrace middlePoint
        (middleExcluded.trans middleEntry.symm) final continued
    subst final
    have totalLength : (firstAttempt.joints ++ lastAttempt.joints).length =
        before.length + after.length := by
      rw [List.length_append, firstAttempt.joints_length, lastAttempt.joints_length]
    have joined : setup.recoveryJointRecall (setup.proposalRecoveryEraseTrace lastTrace) =
        (firstAttempt.joints ++ lastAttempt.joints).reverse ++
          setup.recoveryJointRecall (setup.proposalRecoveryEraseTrace trace) := by
      rw [lastWord, middleWord, List.reverse_append, List.append_assoc]
    have firstRead : read ⟨some middleState, middleTrace⟩ = firstAttempt.joints := by
      dsimp only [read]
      rw [middleWord, ← firstAttempt.joints_length, ← List.length_reverse,
        List.take_left, List.reverse_reverse]
    rw [firstRead]
    dsimp only [finalRead]
    rw [joined, ← totalLength, ← List.length_reverse, List.take_left, List.reverse_reverse,
      ← firstAttempt.joints_length, List.take_left]
  rw [setup.proposalRecoveryModel.runBehavioralFrom_add]
  change fiberPosterior (prior.bind tail) finalRead (read target) = tail target
  rw [fiberPosterior_bind_of_observation prior tail read finalRead retained _ present]
  have singleton := ordinary_source_prefix_posterior setup values before (after.prepend suffix)
    lift origin source current trace point ordinary positive target supported
  change fiberPosterior prior read (read target) = PMF.pure target at singleton
  rw [singleton, PMF.pure_bind]
/-- Literal prefix forcing is the positive conditional hybrid run at this
same entry. Normalization precedes any integration over source annotations. -/
private theorem source_word_run_imposed_prefix
    {baseΓ endΓ : SourceCtx Player L} {baseO endO : Finset VarId}
    (wordBlock : SourceProgram.CommitPrefix baseΓ baseO endΓ endO)
    (word : SourceProgram.History Player L) (views : ∀ owner, DecisionView owner endΓ)
    (readout : ∀ owner action, action ∈ word owner →
      ∃ index, wordBlock.wordAction owner index (views owner) = some action)
    (fullValues : ∀ owner key, FullSupport (values owner key))
    (steered : ∀ owner (key : setup.ProposalRecoveryComponent owner),
      PMF (setup.CommitRecoveryValueChoice owner key.1))
    (strategy : sourceBlockWordStrategy setup values word =
      sourceUnflaggedStrategy setup steered) (who : Player)
    {Γ Δ Ξ : SourceCtx Player L} {O P Q : Finset VarId}
    (before : SourceProgram.CommitPrefix Γ O Δ P) (after : SourceProgram.CommitPrefix Δ P Ξ Q)
    (suffix : SourceProgram Player L Ξ Q)
    (lift : ProtocolState (before.prepend (after.prepend suffix)) →
      ProtocolState setup.program)
    (origin : ProtocolSuffix setup.program (before.prepend (after.prepend suffix)) lift)
    (source : SourceProgram.Config Player L Γ)
    (current : CommitRecoveryState setup.program)
    (trace : setup.proposalRecoveryProtocol.Trace (some current))
    (point : current.point = lift
      (ProtocolState.entry (before.prepend (after.prepend suffix)) source))
    (ordinary : current.excluded = current.entryExcluded) (positive : 0 < before.length)
    (target : setup.proposalRecoveryProtocol.History)
    (supported : target ∈ (setup.proposalRecoveryModel.runBehavioralFrom
      (sourceUnflaggedStrategy setup values) before.length ⟨some current, trace⟩).support)
    (covered : ∀ joint ∈
        ((setup.proposalRecoveryJointRecall target.trace).take before.length).reverse,
      ∀ owner move, joint owner = some move →
        ∃ action ∈ word owner, move = ProposalRecoveryMove.ordinary ⟨action, false⟩)
    (past : ∀ action ∈ word who, ∃ owner name payload result,
      action = OwnAction.commit owner name payload result ∧ name ∈ Δ.map Prod.fst) :
    setup.proposalRecoveryModel.runBehavioralFrom
        (sourceBlockWordStrategy setup values word) (before.length + after.length)
        ⟨some current, trace⟩ =
      fiberPosterior (setup.proposalRecoveryModel.runBehavioralFrom
        (sourceUnflaggedStrategy setup (fun owner key =>
          if owner = who then values owner key else steered owner key))
        (before.length + after.length) ⟨some current, trace⟩)
        (fun history => (((setup.recoveryJointRecall
          (setup.proposalRecoveryEraseTrace history.trace)).take
            (before.length + after.length)).reverse).take before.length)
        (((setup.recoveryJointRecall
          (setup.proposalRecoveryEraseTrace target.trace)).take before.length).reverse) := by
  classical
  have imposed := source_word_forced_prefix setup values wordBlock word views readout before
    (after.prepend suffix) lift origin source current trace point ordinary target
    supported covered
  let hybrid := fun owner (key : setup.ProposalRecoveryComponent owner) =>
    if owner = who then values owner key else steered owner key
  have steeredSupport : target ∈ (setup.proposalRecoveryModel.runBehavioralFrom
      (sourceUnflaggedStrategy setup steered) before.length ⟨some current, trace⟩).support := by
    rw [← strategy, imposed]
    exact (PMF.mem_support_pure_iff ..).mpr rfl
  have hybridSupport := ordinary_run_supported setup hybrid steered (by
    intro owner key choice member
    by_cases own : owner = who
    · simpa only [hybrid, ite_eq_left own] using fullValues owner key choice
    · simpa only [hybrid, ite_eq_right own] using member)
      before.length ⟨some current, trace⟩ target steeredSupport
  have conditioned := ordinary_source_run_prefix_conditioned setup hybrid before after suffix
    lift origin source current trace point ordinary positive target hybridSupport
  rw [conditioned]
  rw [setup.proposalRecoveryModel.runBehavioralFrom_add, imposed, PMF.pure_bind]
  obtain ⟨finished, last, lastTrace, _attempt, targetEq, lastPoint, lastExcluded,
      lastEntry, _generation, _word, _labels, _proper⟩ :=
    proposalRecovery_ordinary_commit_block_support setup values before (after.prepend suffix)
      lift origin source current trace point ordinary target supported
  subst target
  rw [strategy]
  exact source_word_run_past setup values steered word strategy who after suffix
    (fun state => lift (before.liftPoint (after.prepend suffix) state))
    (origin.compose (before.protocolSuffix (after.prepend suffix)))
    finished last lastTrace lastPoint (lastExcluded.trans lastEntry.symm) past


/-- Complete chronological source owner words are independent at one fixed
entry. Each coordinate retains its successive updated owner queries. -/
private theorem ordinary_source_word_product
    (sourceInitial : PMF (app).State) (fuel : Nat) (serviceScheduler : (app).Scheduler)
    (anchor : (app).Control)
    (anchorTrace : ((app).protocol sourceInitial fuel serviceScheduler).Trace (some anchor))
    (phase : RuntimePhase (serviceGraph setup mode))
    {Γ Δ : SourceCtx Player L} {O P : Finset VarId}
    (block : SourceProgram.CommitPrefix Γ O Δ P) (suffix : SourceProgram Player L Δ P)
    (cursor : PhaseProposalOrdinarySourceCursor setup mode runtime leaks plan anchor phase
      block suffix) :
    let law := setup.proposalRecoveryModel.runBehavioralFrom
      (sourceUnflaggedStrategy setup values) block.length ⟨some cursor.current, cursor.trace⟩
    let word := fun history : setup.proposalRecoveryProtocol.History =>
      ((setup.recoveryJointRecall
        (setup.proposalRecoveryEraseTrace history.trace)).take block.length).reverse
    law.map (fun history owner => (word history).map (fun joint => joint owner)) =
      independentProduct (fun owner => law.map
        (fun history => (word history).map (fun joint => joint owner))) := by
  classical
  intro law word
  have baseline := ordinaryBlockProfile_source_word_law setup mode runtime leaks plan
    sourceInitial fuel serviceScheduler anchor anchorTrace phase values block suffix cursor
  dsimp only at baseline
  let controls : Finset Player × Nat × Nat :=
    ((anchor.execution.application.publicView.retired.map fun record =>
      record.2.sourceFailureFootprint.2).foldr (fun first last => first ∪ last) ∅ ∪
        anchor.execution.application.current.native.publicView.sourceFailureFootprint.1
          anchor.execution.application.attempt.phase,
      anchor.execution.application.attempt.generation, anchor.execution.application.attempt.phase)
  let typed := ordinaryBlockProfile setup mode plan values block suffix cursor.embedding
    (fun owner view => cursor.views.view owner view) controls
    anchor.execution.application.publicView
    (PhaseProposal.sourceArchive anchor.execution.network.inputs)
  let read := fun owner (view : DecisionView owner Δ) =>
    (List.range block.length).map fun index =>
      if owner ∈ cursor.current.excluded then none else
        (block.wordAction owner index view).map
          (fun action => (⟨action, false⟩ : CommitRecoveryMove Player L))
  have product := congrArg
    (fun measure => measure.map (fun views owner => read owner (views owner)))
    (block.prefixLaw_views_product suffix typed cursor.source)
  rw [independentProduct_map] at product
  simp only [PMF.map_comp, Function.comp_def] at product
  have jointRead := congrArg (fun measure =>
    measure.map (fun joints owner => joints.map (fun joint => joint owner))) baseline
  simp only [PMF.map_comp, List.map_map, Function.comp_def] at jointRead
  have ownerRead (owner : Player) := congrArg (fun measure =>
    measure.map (fun joints => joints.map (fun joint => joint owner))) baseline
  simp only [PMF.map_comp, List.map_map, Function.comp_def] at ownerRead
  change (block.prefixLaw suffix typed cursor.source).map
    (fun completed owner => read owner (completed.view owner)) =
      law.map (fun history owner => (word history).map (fun joint => joint owner)) at jointRead
  rw [← jointRead, product]
  apply congrArg independentProduct
  funext owner
  exact ownerRead owner

/-- Extending another owner's listed prefix to a complete supported word
cannot change this owner's source-word law. The covered extension is literal. -/
private theorem source_word_owned_fixed
    (sourceInitial : PMF (app).State) (fuel : Nat) (serviceScheduler : (app).Scheduler)
    (anchor : (app).Control)
    (anchorTrace : ((app).protocol sourceInitial fuel serviceScheduler).Trace (some anchor))
    (phase : RuntimePhase (serviceGraph setup mode))
    {Γ Δ : SourceCtx Player L} {O P : Finset VarId}
    (block : SourceProgram.CommitPrefix Γ O Δ P) (suffix : SourceProgram Player L Δ P)
    (cursor : PhaseProposalOrdinarySourceCursor setup mode runtime leaks plan anchor phase
      block suffix)
    (word completeWord : SourceProgram.History Player L)
    (views : ∀ owner, DecisionView owner Δ)
    (readout : ∀ owner action, action ∈ word owner →
      ∃ index, block.wordAction owner index (views owner) = some action)
    (completeReadout : ∀ owner action, action ∈ completeWord owner →
      ∃ index, block.wordAction owner index (views owner) = some action)
    (proper : ∀ owner action, action ∈ word owner → ¬ action.IsFailure)
    (completeProper : ∀ owner action, action ∈ completeWord owner → ¬ action.IsFailure)
    (owner : Player) (sameWord : word owner = completeWord owner)
    (target : setup.proposalRecoveryProtocol.History)
    (supported : target ∈ (setup.proposalRecoveryModel.runBehavioralFrom
      (sourceUnflaggedStrategy setup values) block.length
        ⟨some cursor.current, cursor.trace⟩).support)
    (covered : ∀ joint ∈
        ((setup.proposalRecoveryJointRecall target.trace).take block.length).reverse,
      ∀ player move, joint player = some move →
        ∃ action ∈ completeWord player,
          move = ProposalRecoveryMove.ordinary ⟨action, false⟩) :
    (setup.proposalRecoveryModel.runBehavioralFrom
      (sourceBlockWordStrategy setup values word) block.length
        ⟨some cursor.current, cursor.trace⟩).map
          (fun history => (((setup.recoveryJointRecall
            (setup.proposalRecoveryEraseTrace history.trace)).take block.length).reverse).map
              (fun joint => joint owner)) =
      PMF.pure ((((setup.recoveryJointRecall
        (setup.proposalRecoveryEraseTrace target.trace)).take block.length).reverse).map
          (fun joint => joint owner)) := by
  classical
  let table := fun (listed : SourceProgram.History Player L) player
      (key : setup.ProposalRecoveryComponent player) =>
    if offered : ∃ choice : setup.CommitRecoveryValueChoice player key.1,
        ∃ action ∈ listed player, choice.val.val = some ⟨action, false⟩ then
      PMF.pure (Classical.choose offered)
    else values player key
  have wordTable : sourceBlockWordStrategy setup values word =
      sourceUnflaggedStrategy setup (table word) :=
    source_word_strategy_table setup values block word views readout proper
  have completeTable : sourceBlockWordStrategy setup values completeWord =
      sourceUnflaggedStrategy setup (table completeWord) :=
    source_word_strategy_table setup values block completeWord views completeReadout completeProper
  have sameTable : ∀ key, table word owner key = table completeWord owner key := by
    intro key
    dsimp only [table]
    rw [sameWord]
  have marginal := ordinary_source_owned_word_law setup mode runtime leaks plan
    (table word) (table completeWord) owner sameTable sourceInitial fuel serviceScheduler
    anchor anchorTrace phase block suffix cursor
  rw [← wordTable, ← completeTable] at marginal
  have forced := source_word_forced_prefix setup values block completeWord views completeReadout
    block suffix cursor.lift cursor.origin cursor.source cursor.current cursor.trace cursor.point
    (cursor.excluded.trans cursor.entryExcluded.symm) target supported covered
  rw [marginal, forced, PMF.pure_map]

open Classical in
/-- Fixing the listed foreign word is conditioning the original source law
at this entry. The focal component table remains the original one. -/
private theorem source_word_foreign_conditioned
    (fullValues : ∀ owner key, FullSupport (values owner key))
    (sourceInitial : PMF (app).State) (fuel : Nat) (serviceScheduler : (app).Scheduler)
    (anchor : (app).Control)
    (anchorTrace : ((app).protocol sourceInitial fuel serviceScheduler).Trace (some anchor))
    (phase : RuntimePhase (serviceGraph setup mode))
    {Γ Δ : SourceCtx Player L} {O P : Finset VarId}
    (block : SourceProgram.CommitPrefix Γ O Δ P) (suffix : SourceProgram Player L Δ P)
    (cursor : PhaseProposalOrdinarySourceCursor setup mode runtime leaks plan anchor phase
      block suffix) (positive : 0 < block.length)
    (word completeWord : SourceProgram.History Player L)
    (views : ∀ owner, DecisionView owner Δ)
    (readout : ∀ owner action, action ∈ word owner →
      ∃ index, block.wordAction owner index (views owner) = some action)
    (completeReadout : ∀ owner action, action ∈ completeWord owner →
      ∃ index, block.wordAction owner index (views owner) = some action)
    (proper : ∀ owner action, action ∈ word owner → ¬ action.IsFailure)
    (completeProper : ∀ owner action, action ∈ completeWord owner → ¬ action.IsFailure)
    (who : Player) (sameForeign : ∀ owner, owner ≠ who → word owner = completeWord owner)
    (target : setup.proposalRecoveryProtocol.History)
    (supported : target ∈ (setup.proposalRecoveryModel.runBehavioralFrom
      (sourceUnflaggedStrategy setup values) block.length
        ⟨some cursor.current, cursor.trace⟩).support)
    (covered : ∀ joint ∈
        ((setup.proposalRecoveryJointRecall target.trace).take block.length).reverse,
      ∀ owner move, joint owner = some move →
        ∃ action ∈ completeWord owner,
          move = ProposalRecoveryMove.ordinary ⟨action, false⟩) :
    let steered := fun owner (key : setup.ProposalRecoveryComponent owner) =>
      if offered : ∃ choice : setup.CommitRecoveryValueChoice owner key.1,
          ∃ action ∈ word owner, choice.val.val = some ⟨action, false⟩ then
        PMF.pure (Classical.choose offered)
      else values owner key
    let hybrid := fun owner (key : setup.ProposalRecoveryComponent owner) =>
      if owner = who then values owner key else steered owner key
    let read := fun history : setup.proposalRecoveryProtocol.History =>
      fun owner => (((setup.recoveryJointRecall
        (setup.proposalRecoveryEraseTrace history.trace)).take block.length).reverse).map
          (fun joint => joint owner)
    setup.proposalRecoveryModel.runBehavioralFrom (sourceUnflaggedStrategy setup hybrid)
        block.length ⟨some cursor.current, cursor.trace⟩ =
      fiberPosterior (setup.proposalRecoveryModel.runBehavioralFrom
        (sourceUnflaggedStrategy setup values) block.length
          ⟨some cursor.current, cursor.trace⟩)
        (fun history => @decide
          (∀ owner : Player, owner ≠ who → read history owner = read target owner)
          (Classical.propDecidable _))
        true := by
  classical
  intro steered hybrid read
  let original := setup.proposalRecoveryModel.runBehavioralFrom
    (sourceUnflaggedStrategy setup values) block.length ⟨some cursor.current, cursor.trace⟩
  let changed := setup.proposalRecoveryModel.runBehavioralFrom
    (sourceUnflaggedStrategy setup hybrid) block.length ⟨some cursor.current, cursor.trace⟩
  let factors := fun owner => original.map (fun history => read history owner)
  let restrictions := fun owner => {word | owner ≠ who → word = read target owner}
  let observed := fun (words : Player → List (Option (CommitRecoveryMove Player L))) =>
    @decide (∀ owner : Player, owner ≠ who → words owner = read target owner)
      (Classical.propDecidable _)
  have originalProduct : original.map read = independentProduct factors :=
    ordinary_source_word_product setup mode runtime leaks plan values sourceInitial fuel
      serviceScheduler anchor anchorTrace phase block suffix cursor
  have changedProduct : changed.map read = independentProduct
      (fun owner => changed.map (fun history => read history owner)) :=
    ordinary_source_word_product setup mode runtime leaks plan hybrid sourceInitial fuel
      serviceScheduler anchor anchorTrace phase block suffix cursor
  have coordinate (owner : Player) :
      ∃ word ∈ restrictions owner, word ∈ (factors owner).support :=
    ⟨read target owner, fun _ => rfl,
      (PMF.mem_support_map_iff ..).mpr ⟨target, supported, rfl⟩⟩
  have present : true ∈ (original.map (observed ∘ read)).support :=
    (PMF.mem_support_map_iff ..).mpr ⟨target, supported, by simp [observed]⟩
  have mappedPresent : true ∈ ((original.map read).map observed).support := by
    simpa only [PMF.map_comp] using present
  have filtered : fiberPosterior (original.map read) observed true =
      independentProduct (fun owner => (factors owner).filter (restrictions owner)
        (coordinate owner)) := by
    rw [originalProduct]
    have productPresent : true ∈ ((independentProduct factors).map observed).support := by
      simpa only [originalProduct] using mappedPresent
    rw [fiberPosterior_of_mem_support _ _ productPresent]
    have eventEq : {words | observed words = true} = Set.pi Set.univ restrictions := by
      ext words
      simp only [observed, decide_eq_true_eq, Set.mem_ofPred_eq, Set.mem_pi, Set.mem_univ,
        forall_true_left, restrictions]
    simpa only [← eventEq] using
      filter_independentProduct factors restrictions coordinate
  have table : sourceBlockWordStrategy setup values word =
      sourceUnflaggedStrategy setup steered :=
    source_word_strategy_table setup values block word views readout proper
  have factor (owner : Player) : changed.map (fun history => read history owner) =
      (factors owner).filter (restrictions owner) (coordinate owner) := by
    by_cases own : owner = who
    · subst owner
      have same := ordinary_source_owned_word_law setup mode runtime leaks plan hybrid values who
        (fun _ => by simp only [hybrid, ite_eq_left rfl]) sourceInitial fuel serviceScheduler
        anchor anchorTrace phase block suffix cursor
      change changed.map (fun history => read history who) = factors who at same
      rw [same]
      symm
      exact filter_of_support_subset _ _ _ (fun _ _ different => False.elim (different rfl))
    · have same := ordinary_source_owned_word_law setup mode runtime leaks plan hybrid steered owner
        (fun _ => by simp only [hybrid, ite_eq_right own]) sourceInitial fuel serviceScheduler
        anchor anchorTrace phase block suffix cursor
      have fixed := source_word_owned_fixed setup mode runtime leaks plan values sourceInitial fuel
        serviceScheduler anchor anchorTrace phase block suffix cursor word completeWord views
        readout completeReadout proper completeProper owner (sameForeign owner own)
        target supported covered
      rw [table] at fixed
      change changed.map (fun history => read history owner) =
        (setup.proposalRecoveryModel.runBehavioralFrom (sourceUnflaggedStrategy setup steered)
          block.length ⟨some cursor.current, cursor.trace⟩).map
            (fun history => read history owner) at same
      rw [same, fixed]
      symm
      apply pmf_eq_pure_of_support_subset_singleton
      intro candidate member
      exact ((PMF.mem_support_filter_iff _).mp member).1 own
  have wordLaw : changed.map read =
      (fiberPosterior original (observed ∘ read) true).map read := by
    rw [map_fiberPosterior_readout original read observed true present,
      filtered, changedProduct]
    exact congrArg independentProduct (funext factor)
  have originalSupport : ∀ history ∈ changed.support, history ∈ original.support := by
    intro history reached
    exact ordinary_run_supported setup values hybrid
      (fun owner key choice _member => fullValues owner key choice)
      block.length ⟨some cursor.current, cursor.trace⟩ history reached
  have lifted := bind_eq_of_map_eq changed (fiberPosterior original (observed ∘ read) true)
    read read wordLaw PMF.pure PMF.pure (by
      intro left leftMember right rightMember same
      have rightSupport := (mem_support_fiberPosterior present rightMember).2
      have sameWord : ((setup.recoveryJointRecall
          (setup.proposalRecoveryEraseTrace left.trace)).take block.length).reverse =
          ((setup.recoveryJointRecall
            (setup.proposalRecoveryEraseTrace right.trace)).take block.length).reverse := by
        have lengths := congrArg List.length (congrFun same who)
        simp only [read, List.length_map] at lengths
        apply List.ext_getElem lengths
        intro index leftBound rightBound
        funext owner
        have selected := congrArg (fun items => items[index]?) (congrFun same owner)
        simpa only [read, List.getElem?_map, List.getElem?_eq_getElem leftBound,
          List.getElem?_eq_getElem rightBound, Option.map_some, Option.some.injEq] using selected
      exact congrArg PMF.pure (proposalRecovery_ordinary_commit_history_injective setup values
        block suffix cursor.lift cursor.origin cursor.source cursor.current cursor.trace
        cursor.point (cursor.excluded.trans cursor.entryExcluded.symm) positive left right
        (originalSupport left leftMember) rightSupport sameWord))
  simpa only [PMF.bind_pure, observed, Function.comp_def] using lifted

/-- The actual listed-word runner is the original full source run conditioned
first on the foreign word and then on the imposed prefix, within this one
original entry. The later focal draws retain their updated original table. -/
private theorem source_word_run_conditioned
    (fullValues : ∀ owner key, FullSupport (values owner key))
    (sourceInitial : PMF (app).State) (fuel : Nat) (serviceScheduler : (app).Scheduler)
    (anchor : (app).Control)
    (anchorTrace : ((app).protocol sourceInitial fuel serviceScheduler).Trace (some anchor))
    (phase : RuntimePhase (serviceGraph setup mode))
    {Γ Δ Ξ : SourceCtx Player L} {O P Q : Finset VarId}
    (before : SourceProgram.CommitPrefix Γ O Δ P) (after : SourceProgram.CommitPrefix Δ P Ξ Q)
    (suffix : SourceProgram Player L Ξ Q)
    (cursor : PhaseProposalOrdinarySourceCursor setup mode runtime leaks plan anchor phase
      (before.append after) suffix) (positive : 0 < before.length)
    (word completeWord : SourceProgram.History Player L)
    (views : ∀ owner, DecisionView owner Ξ)
    (readout : ∀ owner action, action ∈ word owner →
      ∃ index, (before.append after).wordAction owner index (views owner) = some action)
    (completeReadout : ∀ owner action, action ∈ completeWord owner →
      ∃ index, (before.append after).wordAction owner index (views owner) = some action)
    (proper : ∀ owner action, action ∈ word owner → ¬ action.IsFailure)
    (completeProper : ∀ owner action, action ∈ completeWord owner → ¬ action.IsFailure)
    (who : Player) (sameForeign : ∀ owner, owner ≠ who → word owner = completeWord owner)
    (reference target : setup.proposalRecoveryProtocol.History)
    (referenceSupported : reference ∈ (setup.proposalRecoveryModel.runBehavioralFrom
      (sourceUnflaggedStrategy setup values) (before.length + after.length)
        ⟨some cursor.current, cursor.trace⟩).support)
    (referenceCovered : ∀ joint ∈ ((setup.proposalRecoveryJointRecall reference.trace).take
        (before.length + after.length)).reverse,
      ∀ owner move, joint owner = some move →
        ∃ action ∈ completeWord owner, move = ProposalRecoveryMove.ordinary ⟨action, false⟩)
    (targetSupported : target ∈ (setup.proposalRecoveryModel.runBehavioralFrom
      (sourceUnflaggedStrategy setup values) before.length
        ⟨some cursor.current, cursor.trace⟩).support)
    (targetCovered : ∀ joint ∈
        ((setup.proposalRecoveryJointRecall target.trace).take before.length).reverse,
      ∀ owner move, joint owner = some move →
        ∃ action ∈ word owner, move = ProposalRecoveryMove.ordinary ⟨action, false⟩)
    (past : ∀ action ∈ word who, ∃ owner name payload result,
      action = OwnAction.commit owner name payload result ∧ name ∈ Δ.map Prod.fst) :
    let read := fun history : setup.proposalRecoveryProtocol.History =>
      ((setup.recoveryJointRecall (setup.proposalRecoveryEraseTrace history.trace)).take
        (before.length + after.length)).reverse
    setup.proposalRecoveryModel.runBehavioralFrom
        (sourceBlockWordStrategy setup values word) (before.length + after.length)
        ⟨some cursor.current, cursor.trace⟩ =
      fiberPosterior (fiberPosterior (setup.proposalRecoveryModel.runBehavioralFrom
        (sourceUnflaggedStrategy setup values) (before.length + after.length)
          ⟨some cursor.current, cursor.trace⟩)
        (fun history => @decide (∀ owner : Player, owner ≠ who →
          (read history).map (fun joint => joint owner) =
            (read reference).map (fun joint => joint owner)) (Classical.propDecidable _)) true)
        (fun history => (read history).take before.length)
        (((setup.recoveryJointRecall (setup.proposalRecoveryEraseTrace target.trace)).take
          before.length).reverse) := by
  classical
  intro read
  let table := fun owner (key : setup.ProposalRecoveryComponent owner) =>
    if offered : ∃ choice : setup.CommitRecoveryValueChoice owner key.1,
        ∃ action ∈ word owner, choice.val.val = some ⟨action, false⟩ then
      PMF.pure (Classical.choose offered)
    else values owner key
  have strategy : sourceBlockWordStrategy setup values word =
      sourceUnflaggedStrategy setup table :=
    source_word_strategy_table setup values (before.append after) word views readout proper
  have entry : ∃ lift : ProtocolState (before.prepend (after.prepend suffix)) →
      ProtocolState setup.program,
      ProtocolSuffix setup.program (before.prepend (after.prepend suffix)) lift ∧
      cursor.current.point = lift
        (ProtocolState.entry (before.prepend (after.prepend suffix)) cursor.source) := by
    rw [← before.prepend_append after suffix]
    exact ⟨cursor.lift, cursor.origin, cursor.point⟩
  obtain ⟨lift, origin, point⟩ := entry
  have forced := source_word_run_imposed_prefix setup values (before.append after) word views
    readout fullValues table strategy who before after suffix lift origin cursor.source
    cursor.current cursor.trace point (cursor.excluded.trans cursor.entryExcluded.symm)
    positive target targetSupported targetCovered past
  have wholePositive : 0 < (before.append after).length := by
    rw [SourceProgram.CommitPrefix.length_append]
    omega
  have supported : reference ∈ (setup.proposalRecoveryModel.runBehavioralFrom
      (sourceUnflaggedStrategy setup values) (before.append after).length
        ⟨some cursor.current, cursor.trace⟩).support := by
    simpa only [SourceProgram.CommitPrefix.length_append] using referenceSupported
  have covered : ∀ joint ∈ ((setup.proposalRecoveryJointRecall reference.trace).take
        (before.append after).length).reverse,
      ∀ owner move, joint owner = some move →
        ∃ action ∈ completeWord owner, move = ProposalRecoveryMove.ordinary ⟨action, false⟩ := by
    simpa only [SourceProgram.CommitPrefix.length_append] using referenceCovered
  have foreign := source_word_foreign_conditioned setup mode runtime leaks plan values fullValues
    sourceInitial fuel serviceScheduler anchor anchorTrace phase (before.append after) suffix cursor
    wholePositive word completeWord views readout completeReadout proper completeProper who
    sameForeign reference supported covered
  simp only [SourceProgram.CommitPrefix.length_append] at foreign
  change setup.proposalRecoveryModel.runBehavioralFrom
      (sourceUnflaggedStrategy setup (fun owner key =>
        if owner = who then values owner key else table owner key))
      (before.length + after.length) ⟨some cursor.current, cursor.trace⟩ = _ at foreign
  rw [foreign] at forced
  convert forced using 1
  congr 2
  funext history
  exact decide_eq_decide.mpr Iff.rfl

omit [Fintype Player] in
/-- An actual closing word transports the full erased source history,
including its proposal deltas, from the retained original entry. -/
private theorem binding_close_erased_history
    (first : setup.proposalRecoveryProtocol.History)
    (current : CommitRecoveryState setup.program)
    (trace : setup.proposalRecoveryProtocol.Trace (some current))
    (same : setup.proposalRecoveryErasedHistory first =
      setup.proposalRecoveryErasedHistory ⟨some current, trace⟩)
    (committing : ProtocolState.atCommit setup.program current.point = true)
    (left right : setup.proposalRecoveryProtocol.History)
    (leftPrefix : TracePrefix first.trace left.trace)
    (rightPrefix : TracePrefix trace right.trace)
    (word : List (Player → Option (ProposalRecoveryMove Player L)))
    (leftWord : setup.proposalRecoveryJointRecall left.trace =
      word ++ setup.proposalRecoveryJointRecall first.trace)
    (rightWord : setup.proposalRecoveryJointRecall right.trace =
      word ++ setup.proposalRecoveryJointRecall trace)
    (within : word.length + ProtocolState.commitEnd setup.program current.point ≤
      ProtocolState.remaining setup.program current.point) :
    setup.proposalRecoveryErasedHistory left = setup.proposalRecoveryErasedHistory right := by
  obtain ⟨replayed, emitted, retained, erased, originalWord, replayedWord,
      _originalLength, replayedLength⟩ :=
    setup.proposalRecovery_supported_suffix_of_erased_history_eq first
      ⟨some current, trace⟩ same left.trace leftPrefix
  have sameWord : emitted = word := List.append_cancel_right (originalWord.symm.trans leftWord)
  subst emitted
  have labeled : setup.proposalRecoveryJointRecall replayed.trace =
      setup.proposalRecoveryJointRecall right.trace := replayedWord.trans rightWord.symm
  have semanticWord : setup.recoveryJointRecall (setup.proposalRecoveryEraseTrace replayed.trace) =
      setup.recoveryJointRecall (setup.proposalRecoveryEraseTrace right.trace) := by
    rw [← setup.proposalRecoveryJointRecall_semantic,
      ← setup.proposalRecoveryJointRecall_semantic, labeled]
  have bounded : (setup.proposalRecoveryEraseTrace replayed.trace).length +
      ProtocolState.commitEnd setup.program current.point ≤
        (setup.proposalRecoveryEraseTrace trace).length +
          ProtocolState.remaining setup.program current.point := by
    simp only [setup.proposalRecoveryEraseTrace_length]
    change replayed.trace.length = trace.length + word.length at replayedLength
    omega
  have semantic := setup.commitRecovery_history_eq_of_commit_window current
    (setup.proposalRecoveryEraseTrace trace) committing
    (setup.proposalRecoveryEraseTrace replayed.trace) (setup.proposalRecoveryEraseTrace right.trace)
    (proposalRecovery_reaches_semantic setup retained.reachesWithin)
    (proposalRecovery_reaches_semantic setup rightPrefix.reachesWithin) semanticWord bounded
  have equal : replayed = right :=
    setup.proposalRecoveryHistory_eq_of_semantic_word replayed right semantic labeled
  exact erased.trans (congrArg setup.proposalRecoveryErasedHistory equal)

open scoped ENNReal

attribute [local implicit_reducible] InformationModel.InformationSite

section ForeignPosterior

variable (implementation : ReservedConcurrentImplementation setup)

local notation "nativeApplication" => implementation.application
local notation "nativeMenu" => PhaseCount.onePacketMenu implementation.runtime
  implementation.leaks implementation.bounds
local notation "nativeInitial" => implementation.initial
local notation "nativeProtocol" => ReactiveApplication.ResponseMenu.protocol
  (PhaseCount.onePacketMenu implementation.runtime implementation.leaks implementation.bounds)
  implementation.initial implementation.horizon implementation.scheduler

private theorem transport_indexed
    {α : Type} {β : α → Type} (predicate : (a : α) → β a → Prop)
    {a b : α} (same : a = b) (value : β b) (proof : predicate b value) :
    predicate a (same.symm ▸ value) := by
  cases same
  exact proof

private theorem transport_two_indexed
    {α : Type} {β γ : α → Type}
    (relation : (a : α) → β a → γ a → Prop)
    {a b : α} (same : a = b) (first : β b) (second : γ b)
    (proof : relation b first second) :
    relation a (same.symm ▸ first) (same.symm ▸ second) := by
  cases same
  exact proof

private theorem transport_two_indexed_value
    {α : Type} {β γ : α → Type} {δ : Type}
    (function : (a : α) → β a → γ a → δ)
    {a b : α} (same : a = b) (first : β b) (second : γ b) :
    function a (same.symm ▸ first) (same.symm ▸ second) = function b first second := by
  cases same
  rfl

private theorem cast_roundtrip {α : Type} {β : α → Type}
    {a b : α} (same : a = b) (value : β b) :
    same ▸ (same.symm ▸ value) = value := by
  cases same
  rfl

def issuedBindingObservation
    (control : (nativeApplication).Control)
    (phase : RuntimePhase (serviceGraph setup .concurrent))
    (key : (serviceGraph setup .concurrent).SemanticKey) : Bool := by
  classical
  exact decide (∀ message ∈ control.execution.network.inputs,
    message.payload.attempt = control.execution.application.attempt →
    ∀ event ∈ phase.events, ∀ candidate,
      message.payload.packet.call = .commitment event candidate →
      ∀ owner payload (binding :
          (serviceGraph setup .concurrent).outputLayout event = .binding owner payload),
        (⟨.inr event, binding⟩ : FieldRef (serviceGraph setup .concurrent).layout
          (.binding owner payload)).get? key.2.1 =
            some (control.execution.application.current.native.bindingResult candidate payload))

/-- Every proper selected value has a positive issued-ledger cylinder at
the original frozen graph entry. Its conditional law is the completed emitted
frontier, independently of the historical probability of that response. -/
theorem binding_value_frontier_posterior
    (operational : implementation.Operational)
    (fullValues : ∀ owner key, FullSupport (values owner key))
    (control : (nativeApplication).Control)
    (trace : (nativeProtocol).Trace (some control))
    (who : Player) (active : control.actor = some who)
    (event : (serviceGraph setup .concurrent).EventId) (payload : L.Ty)
    (unsentBinding : CleanUnsentBinding setup implementation who (control.execution.recall who)
      (control.execution.observe nativeApplication who) event payload)
    (foreign : ∀ owner, owner ≠ who →
      ¬ PhaseProposal.GeneratedUnusableBindingHistory implementation.runtime implementation.leaks
        implementation.bounds nativeInitial implementation.horizon implementation.scheduler owner
          ⟨some control, trace⟩)
    (entry : NativeBindingEntry setup implementation operational control trace who event)
    (value : L.Val payload) :
    let profile := phaseProposalBindingPotentialProfile setup .concurrent implementation.runtime
      implementation.leaks implementation.plan entry.entry.execution entry.phase values
    let original := (serviceGraph setup .concurrent).canonicalContinuation profile
      entry.entry.execution.application.current.native.config
    let observed := fun key => issuedBindingObservation setup implementation control entry.phase
      key &&
      decide ((⟨.inr event, unsentBinding.binding⟩ :
        FieldRef (serviceGraph setup .concurrent).layout
        (.binding who payload)).get? key.2.1 = some (.success value))
    let frontier := phaseProposalEmissionFrontier setup .concurrent implementation.runtime
      implementation.leaks entry.entry.execution entry.phase entry.entryTrace.length
        entry.entry.execution.application.current.native.config nativeInitial implementation.horizon
          implementation.scheduler ((nativeMenu).toRawTrace nativeInitial implementation.horizon
            implementation.scheduler trace)
    ∃ ready : frontier.cut.Ready event,
      true ∈ (original.map observed).support ∧
        (serviceGraph setup .concurrent).canonicalContinuation profile
          (phaseProposalBindingFrontierDrain setup .concurrent implementation.runtime
            implementation.leaks entry.entry.execution entry.phase
              (frontier.complete event ready
                (cast (congrArg EventField.Action unsentBinding.binding.symm) (.success value))
                (cast (congrArg EventField.Value unsentBinding.binding.symm) (.success value)))) =
          fiberPosterior original observed true := by
  classical
  intro profile original observed frontier
  let derivedInitial := (setup.initialLaw.map encodeInputs).map
    (PhaseRuntimeState.initial implementation.plan)
  have initialEq : derivedInitial = nativeInitial := PMF.map_comp _ _ _
  let counted : ((nativeMenu).protocol derivedInitial implementation.horizon
      implementation.scheduler).Trace (some control) := initialEq.symm ▸ trace
  let earlier : ((nativeMenu).protocol derivedInitial implementation.horizon
      implementation.scheduler).Trace (some entry.entry) := initialEq.symm ▸ entry.entryTrace
  have frame := entry.callback_frame setup implementation operational control trace who event
  have proper := entry.frontier_proper setup implementation operational control trace who
    event payload unsentBinding foreign
  have retainedCast : TracePrefix earlier counted :=
    transport_two_indexed
      (fun law
        (before : ((nativeMenu).protocol law implementation.horizon
          implementation.scheduler).Trace (some entry.entry))
        (after : ((nativeMenu).protocol law implementation.horizon
          implementation.scheduler).Trace (some control)) => TracePrefix before after)
      initialEq entry.entryTrace trace entry.retained
  have properCast : ∀ named ∈ entry.phase.events,
      ∀ owner ∉ entry.entry.execution.application.current.excluded,
        ∀ (domain : L.Ty)
          (binding : (serviceGraph setup .concurrent).outputLayout named =
            .binding owner domain) result,
          (⟨.inr named, binding⟩ : FieldRef (serviceGraph setup .concurrent).layout
            (.binding owner domain)).get? (phaseProposalEmissionFrontier setup .concurrent
              implementation.runtime implementation.leaks entry.entry.execution entry.phase
              earlier.length entry.entry.execution.application.current.native.config
              derivedInitial implementation.horizon implementation.scheduler
              ((nativeMenu).toRawTrace derivedInitial implementation.horizon
                implementation.scheduler counted)).store = some result →
            ∃ value, result = .success value :=
    transport_two_indexed
      (fun law
        (before : ((nativeMenu).protocol law implementation.horizon
          implementation.scheduler).Trace (some entry.entry))
        (after : ((nativeMenu).protocol law implementation.horizon
          implementation.scheduler).Trace (some control)) =>
        ∀ named ∈ entry.phase.events,
          ∀ owner ∉ entry.entry.execution.application.current.excluded,
            ∀ (domain : L.Ty)
              (binding : (serviceGraph setup .concurrent).outputLayout named =
                .binding owner domain) result,
              (⟨.inr named, binding⟩ : FieldRef (serviceGraph setup .concurrent).layout
                (.binding owner domain)).get? (phaseProposalEmissionFrontier setup .concurrent
                  implementation.runtime implementation.leaks entry.entry.execution entry.phase
                  before.length entry.entry.execution.application.current.native.config
                  law implementation.horizon implementation.scheduler
                  ((nativeMenu).toRawTrace law implementation.horizon
                    implementation.scheduler after)).store = some result →
                ∃ value, result = .success value)
      initialEq entry.entryTrace trace proper
  obtain ⟨oldPresent, oldLaw⟩ := emitted_frontier_conditional setup .concurrent
    implementation.runtime implementation.leaks implementation.bounds implementation.plan values
      operational.completePending operational.maximalPhases fullValues implementation.horizon
      implementation.scheduler entry.entry earlier entry.phase entry.entryInstalled entry.commitment
      entry.entryExcluded entry.fresh control counted retainedCast
      entry.sameAttempt.symm entry.excluded properCast
  have frontierEq : frontier = phaseProposalEmissionFrontier setup .concurrent
      implementation.runtime implementation.leaks entry.entry.execution entry.phase
      entry.entryTrace.length entry.entry.execution.application.current.native.config
      nativeInitial implementation.horizon implementation.scheduler
      ((nativeMenu).toRawTrace nativeInitial implementation.horizon
        implementation.scheduler trace) := by
    simp only [frontier]
  have request : control.execution.application.SeedRequest who
      ⟨control.execution.application.attempt, event⟩ := by
    obtain ⟨_draw, invariant⟩ := phaseNativeInvariant_history implementation.runtime
      implementation.leaks implementation.plan (setup.initialLaw.map encodeInputs)
        implementation.horizon implementation.scheduler
          ((nativeMenu).toRawTrace derivedInitial implementation.horizon
            implementation.scheduler counted)
    exact (control.execution.application.requests_publicView invariant who _).mp
      unsentBinding.request
  have code : cast (congrArg (EventCode (serviceGraph setup .concurrent).layout)
      unsentBinding.binding) ((serviceGraph setup .concurrent).nodes event) =
        .bind who payload := by
    cases nodeView (serviceGraph setup .concurrent) event with
    | bind owner domain shape code =>
        obtain ⟨rfl, rfl⟩ := EventField.binding.inj (shape.symm.trans unsentBinding.binding)
        exact code
    | resolve owner domain source checks shape code => cases shape.symm.trans unsentBinding.binding
    | sample domain law shape code => cases shape.symm.trans unsentBinding.binding
  have nativeActive : who ∉ entry.entry.execution.application.current.excluded := by
    rw [← entry.excluded]
    exact request.2.2.2.2
  have unsent : ∀ message ∈ (nativeApplication).outputs (control.execution.recall who),
      PhaseCount.event? message.payload ≠ some ⟨control.execution.application.attempt, event⟩ := by
    have attemptEq : (control.execution.observe nativeApplication who).application.2.attempt =
        control.execution.application.attempt := rfl
    simpa only [attemptEq] using unsentBinding.unsent
  have traceActive : ((nativeMenu).protocol nativeInitial implementation.horizon
      implementation.scheduler).Trace
        (some ⟨control.remaining, some who, control.execution⟩) := by
    simpa only [← active] using trace
  have frameActive : PhaseProposalBindingCallbackFrame setup .concurrent implementation.runtime
      implementation.leaks entry.entry.execution entry.phase control.execution frontier
        (some who) := by
    simpa only [frontier, active] using frame
  obtain ⟨ready, rowPresent, rowLaw⟩ := binding_frontier_proper_posterior setup .concurrent
    implementation.runtime implementation.leaks implementation.bounds implementation.plan values
      operational.completePending operational.maximalPhases fullValues implementation.horizon
      implementation.scheduler control.remaining who control.execution entry.entry.execution
      traceActive entry.phase entry.commitment frontier frameActive entry.sameAttempt.symm
      event payload unsentBinding.binding code entry.inside nativeActive request unsent value
  refine ⟨ready, ?_⟩
  apply posterior_append_observation original
    (issuedBindingObservation setup implementation control entry.phase) observed
    (fun key => (⟨.inr event, unsentBinding.binding⟩ :
      FieldRef (serviceGraph setup .concurrent).layout
      (.binding who payload)).get? key.2.1) (some (.success value))
    ((serviceGraph setup .concurrent).canonicalContinuation profile frontier)
    ((serviceGraph setup .concurrent).canonicalContinuation profile
      (phaseProposalBindingFrontierDrain setup .concurrent implementation.runtime
        implementation.leaks entry.entry.execution entry.phase
          (frontier.complete event ready
            (cast (congrArg EventField.Action unsentBinding.binding.symm) (.success value))
            (cast (congrArg EventField.Value unsentBinding.binding.symm) (.success value)))))
    (by simpa [original, profile, issuedBindingObservation] using oldPresent)
    (by
      have transported := transport_two_indexed
        (fun law
          (before : ((nativeMenu).protocol law implementation.horizon
            implementation.scheduler).Trace (some entry.entry))
          (after : ((nativeMenu).protocol law implementation.horizon
            implementation.scheduler).Trace (some control)) =>
          (serviceGraph setup .concurrent).canonicalContinuation profile
            (phaseProposalEmissionFrontier setup .concurrent implementation.runtime
              implementation.leaks entry.entry.execution entry.phase before.length
              entry.entry.execution.application.current.native.config law
              implementation.horizon implementation.scheduler
              ((nativeMenu).toRawTrace law implementation.horizon
                implementation.scheduler after)) =
            fiberPosterior original
              (issuedBindingObservation setup implementation control entry.phase) true)
        initialEq.symm earlier counted
        (by
          unfold issuedBindingObservation
          simpa [profile, original, entry.phase.mem_events, Prod.forall,
            derivedInitial] using oldLaw)
      have earlierBack : initialEq ▸ earlier = entry.entryTrace := by
        simpa only [earlier] using cast_roundtrip
          (β := fun law => ((nativeMenu).protocol law implementation.horizon
            implementation.scheduler).Trace (some entry.entry)) initialEq entry.entryTrace
      have countedBack : initialEq ▸ counted = trace := by
        simpa only [counted] using cast_roundtrip
          (β := fun law => ((nativeMenu).protocol law implementation.horizon
            implementation.scheduler).Trace (some control)) initialEq trace
      simpa only [earlierBack, countedBack, profile, original, frontier]
        using transported)
    rowPresent rowLaw.symm
  intro key _
  simp only [observed, Bool.and_eq_true, decide_eq_true_eq]

/-- The maximal ordinary cursor at the callback uses the literal selected
checkpoint's block, maps and views. Its graph configuration remains the
original frozen entry configuration. -/
theorem selected_binding_cursor
    (operational : implementation.Operational)
    (who : Player) (control : (nativeApplication).Control)
    (trace : (nativeProtocol).Trace (some control))
    (event : (serviceGraph setup .concurrent).EventId)
    (entry : NativeBindingEntry setup implementation operational control trace who event)
    (atCallback : Bool) :
    let anchor := if atCallback then control else entry.entry
    let checkpoint := (checkpointSelection setup implementation operational trace).val.checkpoint
    let block := SourceProgram.commitPhase checkpoint.residual.tail
    ∃ cursor : PhaseProposalOrdinarySourceCursor setup .concurrent implementation.runtime
        implementation.leaks implementation.plan anchor entry.phase block.block block.suffix,
      (⟨some cursor.current, cursor.trace⟩ : setup.proposalRecoveryProtocol.History) =
        canonicalSource setup implementation operational ⟨some control, trace⟩ ∧
      cursor.offset = control.execution.application.attempt.phase ∧
      cursor.source = checkpoint.source ∧ cursor.refs = checkpoint.refs ∧
      cursor.embedding = cast (congrArg (fun program => OutputEmbedding
        (inputLayout setup.context) (outputLayout setup.program) program)
          block.reconstruct.symm) checkpoint.embedding ∧
      (∀ point, cursor.lift point = checkpoint.residual.lift
        (cast (congrArg ProtocolState block.reconstruct) point)) ∧
      (∀ owner view, cursor.views.view owner view = checkpoint.views.view owner
        (cast (congrArg (ProtocolView owner) block.reconstruct) view)) ∧
      cursor.config = entry.cursor.config ∧
      block.block.length = entry.phase.high - entry.phase.low := by
  classical
  intro anchor checkpoint block
  let cursorFor := fun checkpoint : RecoverySourceCheckpoint setup .concurrent
      entry.entry.execution.application =>
    let block := SourceProgram.commitPhase checkpoint.residual.tail
    ∃ cursor : PhaseProposalOrdinarySourceCursor setup .concurrent implementation.runtime
        implementation.leaks implementation.plan anchor entry.phase block.block block.suffix,
      (⟨some cursor.current, cursor.trace⟩ : setup.proposalRecoveryProtocol.History) =
        canonicalSource setup implementation operational ⟨some control, trace⟩ ∧
      cursor.offset = control.execution.application.attempt.phase ∧
      cursor.source = checkpoint.source ∧ cursor.refs = checkpoint.refs ∧
      cursor.embedding = cast (congrArg (fun program => OutputEmbedding
        (inputLayout setup.context) (outputLayout setup.program) program)
          block.reconstruct.symm) checkpoint.embedding ∧
      (∀ point, cursor.lift point = checkpoint.residual.lift
        (cast (congrArg ProtocolState block.reconstruct) point)) ∧
      (∀ owner view, cursor.views.view owner view = checkpoint.views.view owner
        (cast (congrArg (ProtocolView owner) block.reconstruct) view)) ∧
      cursor.config = entry.cursor.config ∧
      block.block.length = entry.phase.high - entry.phase.low
  have prior : cursorFor entry.witness.checkpoint := by
    have maximum (program : SourceProgram Player L entry.witness.checkpoint.residual.context
        entry.witness.checkpoint.residual.names)
        (reconstruct : entry.block.prepend entry.suffix = program) :
        SourceProgram.commitPhase program =
          ⟨entry.targetContext, entry.targetNames, entry.suffix, entry.block,
            reconstruct, entry.boundary⟩ := by
      cases reconstruct
      exact maximal_commit_phase entry.block entry.suffix entry.boundary
    dsimp only [cursorFor]
    rw [maximum entry.witness.checkpoint.residual.tail entry.reconstruct]
    have low : control.execution.application.attempt.phase = entry.phase.low := by
      obtain ⟨rest, phases⟩ := List.head?_eq_some_iff.mp entry.installed
      simp only [PhaseRuntimeState.attempt, phases, List.head?_cons, Option.map_some,
        Option.getD_some]
    cases atCallback with
    | false =>
        exact ⟨entry.cursor, entry.canonicalHistory, entry.offset.trans low.symm, entry.source,
          entry.refs, entry.embedding, entry.lift, entry.views, rfl, entry.size⟩
    | true =>
        exact ⟨entry.decision_cursor setup implementation operational control trace who
          event,
          entry.canonicalHistory, entry.offset.trans low.symm, entry.source, entry.refs,
          entry.embedding, entry.lift, entry.views, rfl, entry.size⟩
  obtain ⟨saved, represented⟩ := entry.selected
  have transported : cursorFor (checkpoint.transfer saved
      (congrArg CommitAttemptId.generation entry.sameAttempt)
      (congrArg CommitAttemptId.phase entry.sameAttempt)) := represented ▸ prior
  exact transported

/-- Every history with the selected entry's closed key retains its complete
erased source history. Its ordinary cursor uses the same physical anchor and
compiler references; only hidden publication memories can change. -/
theorem closed_key_entry_erased_history
    (operational : implementation.Operational)
    (who : Player) (control : (nativeApplication).Control)
    (trace : (nativeProtocol).Trace (some control))
    (event : (serviceGraph setup .concurrent).EventId)
    (entry : NativeBindingEntry setup implementation operational control trace who event)
    (target : setup.proposalRecoveryProtocol.History)
    (foreign : ∀ owner, owner ≠ who →
      ¬ PhaseProposal.GeneratedUnusableBindingHistory implementation.runtime
        implementation.leaks implementation.bounds nativeInitial implementation.horizon
          implementation.scheduler owner ⟨some control, trace⟩)
    (sameKey : setup.proposalRecoveryClosedKey who target =
      setup.proposalRecoveryClosedKey who
        (canonicalSource setup implementation operational ⟨some control, trace⟩)) :
    ∃ (current : CommitRecoveryState setup.program)
        (targetTrace : setup.proposalRecoveryProtocol.Trace (some current)),
        target = ⟨some current, targetTrace⟩ ∧
        setup.proposalRecoveryForeignGood who target ∧
        setup.proposalRecoveryErasedHistory ⟨some entry.cursor.current, entry.cursor.trace⟩ =
          setup.proposalRecoveryErasedHistory ⟨some current, targetTrace⟩ := by
  classical
  have canonicalGood := canonicalSource_foreignGood setup implementation operational who
    ⟨some control, trace⟩ foreign
  have same : setup.proposalRecoveryClosedKey who target =
      setup.proposalRecoveryClosedKey who ⟨some entry.cursor.current, entry.cursor.trace⟩ :=
    sameKey.trans (congrArg (setup.proposalRecoveryClosedKey who) entry.canonicalHistory.symm)
  have entryGood : setup.proposalRecoveryForeignGood who
      ⟨some entry.cursor.current, entry.cursor.trace⟩ :=
    entry.canonicalHistory.symm ▸ canonicalGood
  have targetGood : setup.proposalRecoveryForeignGood who target := by
    have bit := congrArg (fun key => key.2.2.2) same
    simpa only [Setup.proposalRecoveryClosedKey, entryGood, decide_true,
      decide_eq_true_eq] using bit
  rcases target with ⟨state, targetTrace⟩
  cases state with
  | none =>
      have base := congrArg Prod.fst same
      simp only [Setup.proposalRecoveryClosedKey, Option.map_none, Option.map_some] at base
      cases base
  | some current =>
      obtain ⟨first, prior, refines⟩ := setup.proposalRecovery_refinement_of_closed_key who
        operational.wellFormed entry.cursor.current current entry.cursor.trace targetTrace
          same.symm entryGood targetGood
      exact ⟨current, targetTrace, rfl, targetGood, refines.erasedHistory⟩

/-- A positive annotation supplies the same whole-history cursor transfer,
without an assumption on the historical policy outside its actual support. -/
theorem annotated_entry_erased_history
    (operational : implementation.Operational)
    (sourceProfile : ∀ owner, setup.proposalRecoveryModel.BehavioralPolicy owner)
    (nativeProfile : ∀ owner,
      ((nativeMenu).information nativeInitial implementation.horizon
        implementation.scheduler).BehavioralPolicy owner)
    (who : Player) (control : (nativeApplication).Control)
    (trace : (nativeProtocol).Trace (some control))
    (tape : ReservedEpoch.Tape Player implementation.tapeLength)
    (target : setup.proposalRecoveryProtocol.History)
    (word : SourceProgram.History Player L)
    (canonicalSupported : setup.proposalRecoveryModel.historyReachWeight sourceProfile
      (canonicalSource setup implementation operational ⟨some control, trace⟩) ≠ 0)
    (positive : annotatedPrefixWeight setup values implementation operational sourceProfile
      nativeProfile who ⟨some control, trace⟩ tape target word ≠ 0)
    (event : (serviceGraph setup .concurrent).EventId) (payload : L.Ty)
    (unsentBinding : CleanUnsentBinding setup implementation who (control.execution.recall who)
      (control.execution.observe nativeApplication who) event payload) :
    ∃ entry : NativeBindingEntry setup implementation operational control trace who event,
      ∃ (current : CommitRecoveryState setup.program)
        (targetTrace : setup.proposalRecoveryProtocol.Trace (some current)),
        target = ⟨some current, targetTrace⟩ ∧
        setup.proposalRecoveryForeignGood who target ∧
        setup.proposalRecoveryErasedHistory ⟨some entry.cursor.current, entry.cursor.trace⟩ =
          setup.proposalRecoveryErasedHistory ⟨some current, targetTrace⟩ := by
  have foreign : ∀ owner, owner ≠ who →
      ¬ PhaseProposal.GeneratedUnusableBindingHistory implementation.runtime
        implementation.leaks implementation.bounds nativeInitial implementation.horizon
          implementation.scheduler owner ⟨some control, trace⟩ := by
    unfold annotatedPrefixWeight at positive
    dsimp only at positive
    have selected := (mul_ne_zero_iff.mp positive).2
    split at selected
    · rename_i qualified
      exact qualified.1
    · simp only [ne_eq, not_true_eq_false] at selected
  have support := annotatedPrefixWeight_support setup values implementation operational
    sourceProfile nativeProfile who ⟨some control, trace⟩ tape target word canonicalSupported
      positive
  obtain ⟨entry⟩ := qualified_binding_entry setup implementation operational control
    trace who event payload unsentBinding foreign
  obtain ⟨current, targetTrace, targetEq, good, erased⟩ :=
    closed_key_entry_erased_history setup implementation operational who control trace
      event entry target foreign support.1
  exact ⟨entry, current, targetTrace, targetEq, good, erased⟩

open Classical in
/-- The actual foreign joint is the structural ordinary law at the pulled
source entry. The selected residual, compiler codec and native callback frame
are used literally, so neither posterior fallback branch is invoked. -/
theorem ordinaryForeignJoint_of_selected_cursor
    (operational : implementation.Operational)
    (who : Player) (control : (nativeApplication).Control)
    (trace : (nativeProtocol).Trace (some control))
    (phase : RuntimePhase (serviceGraph setup .concurrent)) :
    let checkpoint := (checkpointSelection setup implementation operational trace).val.checkpoint
    let block := SourceProgram.commitPhase checkpoint.residual.tail
    ∀ cursor : PhaseProposalOrdinarySourceCursor setup .concurrent implementation.runtime
        implementation.leaks implementation.plan control phase block.block block.suffix,
      0 < block.block.length →
      cursor.embedding = cast (congrArg (fun program => OutputEmbedding
        (inputLayout setup.context) (outputLayout setup.program) program)
          block.reconstruct.symm) checkpoint.embedding →
      (∀ point, cursor.lift point = checkpoint.residual.lift
        (cast (congrArg ProtocolState block.reconstruct) point)) →
      (∀ owner view, cursor.views.view owner view = checkpoint.views.view owner
        (cast (congrArg (ProtocolView owner) block.reconstruct) view)) →
      ordinaryForeignJoint setup values implementation operational who ⟨some control, trace⟩
          ⟨some cursor.current, cursor.trace⟩ =
        (block.block.prefixLaw block.suffix
          (ordinaryBlockProfile setup .concurrent implementation.plan values block.block
            block.suffix cursor.embedding (fun owner view => cursor.views.view owner view)
              (control.execution.application.entry.excluded,
                control.execution.application.generation,
                  control.execution.application.attempt.phase)
              control.execution.application.publicView
              (PhaseProposal.sourceArchive control.execution.network.inputs)) cursor.source).map
            (fun final => ((fun owner => if owner = who then [] else final.history owner),
              decide (∀ owner, owner ≠ who → issuedLedger setup implementation block.block
                control.execution.application.attempt.phase control
                  (control.execution.application.attempt.phase + block.block.length) owner
                    (final.view owner)))) := by
  classical
  intro checkpoint block cursor positive embedding lift views
  have entryCast (first second : SourceProgram Player L checkpoint.residual.context
      checkpoint.residual.names) (same : first = second)
      (source : SourceProgram.Config Player L checkpoint.residual.context) :
      cast (congrArg ProtocolState same) (ProtocolState.entry first source) =
        ProtocolState.entry second source := by
    cases same
    rfl
  have lifted : checkpoint.residual.lift
      (ProtocolState.entry checkpoint.residual.tail cursor.source) = cursor.current.point := by
    calc
      checkpoint.residual.lift (ProtocolState.entry checkpoint.residual.tail cursor.source) =
          checkpoint.residual.lift (cast (congrArg ProtocolState block.reconstruct)
            (ProtocolState.entry (block.block.prepend block.suffix) cursor.source)) :=
        congrArg checkpoint.residual.lift
          (entryCast _ _ block.reconstruct cursor.source).symm
      _ = cursor.lift (ProtocolState.entry (block.block.prepend block.suffix) cursor.source) :=
        (lift _).symm
      _ = cursor.current.point := cursor.point.symm
  have pulled : residualEntry? checkpoint.residual.tail checkpoint.residual.lift
      cursor.current.point = some cursor.source :=
    (residualEntry?_eq_some_iff checkpoint.origin cursor.current.point cursor.source).mpr lifted
  have committingPrefix {Γ Δ : SourceCtx Player L} {O P : Finset VarId}
      (commitBlock : SourceProgram.CommitPrefix Γ O Δ P) (suffix : SourceProgram Player L Δ P)
      (source : SourceProgram.Config Player L Γ) (nonempty : 0 < commitBlock.length) :
      ProtocolState.atCommit (commitBlock.prepend suffix)
        (ProtocolState.entry (commitBlock.prepend suffix) source) = true := by
    cases commitBlock with
    | nil =>
        simp only [SourceProgram.CommitPrefix.length] at nonempty
        omega
    | commit => rfl
  have commitCast (first second : SourceProgram Player L checkpoint.residual.context
      checkpoint.residual.names) (same : first = second)
      (source : SourceProgram.Config Player L checkpoint.residual.context) :
      ProtocolState.atCommit first (ProtocolState.entry first source) =
        ProtocolState.atCommit second (ProtocolState.entry second source) := by
    cases same
    rfl
  have committing : ProtocolState.atCommit checkpoint.residual.tail
      (ProtocolState.entry checkpoint.residual.tail cursor.source) = true :=
    (commitCast _ _ block.reconstruct cursor.source).symm.trans
      (committingPrefix block.block block.suffix cursor.source positive)
  have wholeViews : (fun owner view => cursor.views.view owner view) =
      (fun owner view => checkpoint.views.view owner
        (cast (congrArg (ProtocolView owner) block.reconstruct) view)) := by
    funext owner view
    exact views owner view
  simp [ordinaryForeignJoint, checkpoint, block, pulled, committing, embedding, wholeViews]

open Classical in
/-- Conditioning the complete source/graph coupling on all literal issued
bindings and a proper selected value retains the whole chronological block
word on both marginals. Already excluded rows remain automatic source slots. -/
theorem ordinary_binding_conditioned_word_coupling
    (control : (nativeApplication).Control)
    (trace : (nativeProtocol).Trace (some control))
    (anchor : (nativeApplication).Control)
    (anchorTrace : (nativeProtocol).Trace (some anchor))
    (phase : RuntimePhase (serviceGraph setup .concurrent))
    {Γ Δ : SourceCtx Player L} {O P : Finset VarId}
    (block : SourceProgram.CommitPrefix Γ O Δ P)
    (suffix : SourceProgram Player L Δ P)
    (cursor : PhaseProposalOrdinarySourceCursor setup .concurrent implementation.runtime
      implementation.leaks implementation.plan anchor phase block suffix)
    (entryExcluded : cursor.current.excluded = control.execution.application.entry.excluded)
    (phaseLow : phase.low = cursor.offset)
    (phaseHigh : phase.high = cursor.offset + block.length)
    (who : Player) (active : who ∉ control.execution.application.entry.excluded)
    (index : Fin (eventCount (block.prepend suffix))) (inside : index.val < block.length)
    (payload : L.Ty)
    (binding : (serviceGraph setup .concurrent).outputLayout (cursor.embedding.event index) =
      .binding who payload) (value : L.Val payload) :
    let completed := fun history : setup.proposalRecoveryProtocol.History =>
      history.state.bind fun current => residualEntry? suffix
        (fun point => cursor.lift (block.liftPoint suffix point)) current.point
    let sourceObserved := fun history : setup.proposalRecoveryProtocol.History =>
      match completed history with
      | none => false
      | some finished => decide (
          (∀ owner, issuedLedger setup implementation block cursor.offset control
            (cursor.offset + block.length) owner (finished.view owner)) ∧
          block.wordAction who index.val (finished.view who) =
            decodeEventAction setup.program (cursor.embedding.event index)
              (cast (congrArg EventField.Action binding.symm) (PublicationResult.success value)))
    let graphObserved := fun key : (serviceGraph setup .concurrent).SemanticKey =>
      decide ((∀ message ∈ control.execution.network.inputs,
        message.payload.attempt = control.execution.application.attempt →
        ∀ event ∈ phase.events, ∀ candidate,
          message.payload.packet.call = .commitment event candidate →
          ∀ owner domain (shape : (serviceGraph setup .concurrent).outputLayout event =
              .binding owner domain),
            (⟨.inr event, shape⟩ : FieldRef (graphLayout setup.program)
              (.binding owner domain)).get? key.2.1 =
                some (control.execution.application.current.native.bindingResult candidate
                  domain)) ∧
        (⟨.inr (cursor.embedding.event index), binding⟩ :
          FieldRef (graphLayout setup.program) (.binding who payload)).get? key.2.1 =
            some (.success value))
    true ∈ (((serviceGraph setup .concurrent).canonicalContinuation
      (phaseProposalBindingPotentialProfile setup .concurrent implementation.runtime
        implementation.leaks implementation.plan anchor.execution phase values)
      cursor.config).map graphObserved).support →
    ∃ joint : PMF (setup.proposalRecoveryProtocol.History ×
        (serviceGraph setup .concurrent).SemanticKey),
      joint.map Prod.fst = fiberPosterior
        (setup.proposalRecoveryModel.runBehavioralFrom
          (sourceUnflaggedStrategy setup values) block.length
            ⟨some cursor.current, cursor.trace⟩) sourceObserved true ∧
      joint.map Prod.snd = fiberPosterior
        ((serviceGraph setup .concurrent).canonicalContinuation
          (phaseProposalBindingPotentialProfile setup .concurrent implementation.runtime
            implementation.leaks implementation.plan anchor.execution phase values)
          cursor.config) graphObserved true ∧
      ∀ pair ∈ joint.support,
        PhaseProposalOrdinarySourceBlockResult setup .concurrent block suffix cursor.refs
          cursor.embedding cursor.lift cursor.source cursor.current cursor.trace pair ∧
        sourceObserved pair.1 = true ∧ graphObserved pair.2 = true ∧
        ((setup.recoveryJointRecall (setup.proposalRecoveryEraseTrace pair.1.trace)).take
          block.length).reverse =
          phaseProposalBindingWord setup.program block suffix cursor.embedding
            cursor.current.excluded pair.2.2.1 cursor.source := by
    classical
  intro completed sourceObserved graphObserved present
  have observes (pair : setup.proposalRecoveryProtocol.History ×
      (serviceGraph setup .concurrent).SemanticKey)
      (related : PhaseProposalOrdinarySourceBlockResult setup .concurrent block suffix
        cursor.refs cursor.embedding cursor.lift cursor.source cursor.current cursor.trace pair) :
      sourceObserved pair.1 = graphObserved pair.2 := by
    obtain ⟨finished, last, lastTrace, attempt, history, point, excluded, _generation,
      _live, agreement, _word, _labels⟩ := related
    have pulled : residualEntry? suffix
        (fun point => cursor.lift (block.liftPoint suffix point)) last.point = some finished :=
      (residualEntry?_eq_some_iff (cursor.origin.compose (block.protocolSuffix suffix))
        last.point finished).mpr point.symm
    rw [entryExcluded] at attempt excluded
    have ledger := issuedLedger_iff_emitted_bindings setup implementation block suffix
      cursor.embedding cursor.refs cursor.offset cursor.compiled.rankEq cursor.views.actionEq
        control trace phase phaseLow phaseHigh pair.2.2.1 cursor.source finished last.excluded
          attempt excluded agreement
    have selected := commitAttempt_selected_binding setup block suffix cursor.embedding
      cursor.refs cursor.views.actionEq pair.2.2.1 cursor.source
        control.execution.application.entry.excluded finished last.excluded attempt excluded
          agreement who active index inside payload binding value
    simp only [sourceObserved, completed, history, Option.bind_some, pulled]
    exact decide_eq_decide.mpr (and_congr ledger selected)
  obtain ⟨joint, sourceMarginal, graphMarginal, supported⟩ :=
    phaseProposalBindingPotentialProfile_conditioned_source_block_coupling setup .concurrent
      implementation.runtime implementation.leaks implementation.plan values nativeInitial
        implementation.horizon implementation.scheduler anchor
          ((nativeMenu).toRawTrace nativeInitial implementation.horizon
            implementation.scheduler anchorTrace) phase block suffix cursor sourceObserved
              graphObserved observes present
  refine ⟨joint, sourceMarginal, graphMarginal, ?_⟩
  intro pair member
  obtain ⟨related, sourceTrue, graphTrue⟩ := supported pair member
  refine ⟨related, sourceTrue, graphTrue, ?_⟩
  obtain ⟨finished, last, lastTrace, attempt, history, _point, excluded, _generation,
    _live, agreement, word, _labels⟩ := related
  have read := phaseProposalBindingWord_of_ordinary_attempt setup.program block suffix
    cursor.embedding cursor.refs pair.2.2.1 cursor.source cursor.source cursor.current.excluded
      finished last.excluded attempt excluded agreement
  rw [read, history, word]
  rw [← attempt.joints_length, ← List.length_reverse, List.take_left, List.reverse_reverse]

/-- The original source run and its structural owner words have one joint
law. The structural coordinate is the actual attempt with synthetic excluded
rows inserted; the source coordinate keeps its automatic NONE instructions. -/
private theorem ordinary_source_structural_joint
    (anchor : (nativeApplication).Control)
    (anchorTrace : (nativeProtocol).Trace (some anchor))
    (phase : RuntimePhase (serviceGraph setup .concurrent))
    {Γ Δ : SourceCtx Player L} {O P : Finset VarId}
    (block : SourceProgram.CommitPrefix Γ O Δ P)
    (suffix : SourceProgram Player L Δ P)
    (cursor : PhaseProposalOrdinarySourceCursor setup .concurrent implementation.runtime
      implementation.leaks implementation.plan anchor phase block suffix) :
    let controls : Finset Player × Nat × Nat :=
      ((anchor.execution.application.publicView.retired.map fun record =>
        record.2.sourceFailureFootprint.2).foldr (fun first last => first ∪ last) ∅ ∪
          anchor.execution.application.current.native.publicView.sourceFailureFootprint.1
            anchor.execution.application.attempt.phase,
        anchor.execution.application.attempt.generation,
        anchor.execution.application.attempt.phase)
    let profile := ordinaryBlockProfile setup .concurrent implementation.plan values
      block suffix cursor.embedding (fun owner view => cursor.views.view owner view)
        controls anchor.execution.application.publicView
          (PhaseProposal.sourceArchive anchor.execution.network.inputs)
    ∃ joint : PMF (setup.proposalRecoveryProtocol.History × SourceProgram.Config Player L Δ),
      joint.map Prod.fst = setup.proposalRecoveryModel.runBehavioralFrom
        (sourceUnflaggedStrategy setup values) block.length
          ⟨some cursor.current, cursor.trace⟩ ∧
      joint.map Prod.snd = block.prefixLaw suffix profile cursor.source ∧
      ∀ pair ∈ joint.support,
        ∃ (finished : SourceProgram.Config Player L Δ)
          (last : CommitRecoveryState setup.program)
          (lastTrace : setup.proposalRecoveryProtocol.Trace (some last))
          (attempt : block.Attempt cursor.source cursor.current.excluded finished last.excluded),
          pair.1 = ⟨some last, lastTrace⟩ ∧
          pair.2 = attempt.withoutMisses ∅ cursor.source ∧
          last.point = cursor.lift (block.liftPoint suffix (ProtocolState.entry suffix finished)) ∧
          last.excluded = cursor.current.excluded ∧ last.generation = cursor.current.generation ∧
          setup.recoveryJointRecall (setup.proposalRecoveryEraseTrace lastTrace) =
            attempt.joints.reverse ++ setup.recoveryJointRecall
              (setup.proposalRecoveryEraseTrace cursor.trace) ∧
          setup.proposalRecoveryJointRecall lastTrace =
            attempt.joints.reverse.map
              (fun row owner => (row owner).map ProposalRecoveryMove.ordinary) ++
                setup.proposalRecoveryJointRecall cursor.trace ∧
          ∀ owner, owner ∉ last.excluded → finished.view owner = pair.2.view owner := by
  classical
  intro controls profile
  obtain ⟨coupling, sourceMarginal, graphMarginal, supported, fillMarginal⟩ :=
    phaseProposalBindingPotentialProfile_source_block_coupling setup .concurrent
      implementation.runtime implementation.leaks implementation.plan nativeInitial
        implementation.horizon implementation.scheduler anchor
          ((nativeMenu).toRawTrace nativeInitial implementation.horizon
            implementation.scheduler anchorTrace) phase values block suffix cursor
  let project := fun pair : setup.proposalRecoveryProtocol.History ×
      (serviceGraph setup .concurrent).SemanticKey =>
    (pair.1, fillCommitPrefix setup.program block suffix cursor.embedding pair.2.2.1 cursor.source)
  let joint := coupling.map project
  refine ⟨joint, ?_, ?_, ?_⟩
  · simpa only [joint, project, PMF.map_comp, Function.comp_def,
      sourceUnflaggedStrategy] using sourceMarginal
  · have marginal := fillMarginal cursor.source (fun _ _ => rfl)
    simpa only [joint, project, PMF.map_comp, Function.comp_def, profile, controls] using marginal
  · intro pair member
    obtain ⟨original, reached, rfl⟩ := (PMF.mem_support_map_iff ..).mp member
    obtain ⟨finished, last, lastTrace, attempt, history, point, excluded, generation,
      _live, agreement, word, labeled⟩ := supported original reached
    refine ⟨finished, last, lastTrace, attempt, history, ?_, point, excluded,
      generation, word, labeled, ?_⟩
    · exact fillCommitPrefix_eq_withoutMisses setup.program block suffix cursor.embedding
        cursor.refs original.2.2.1 cursor.source cursor.current.excluded finished last.excluded
          attempt cursor.source agreement
    · intro owner active
      exact fillCommitPrefix_view_of_attempt_agrees setup.program block suffix cursor.embedding
        cursor.refs original.2.2.1 cursor.source cursor.current.excluded finished last.excluded
          attempt agreement owner active

private def residualBindingObservation
    (residual : ResidualProgram setup.program)
    (control : (nativeApplication).Control) (who : Player)
    (event : (serviceGraph setup .concurrent).EventId) (payload : L.Ty)
    (binding : (serviceGraph setup .concurrent).outputLayout event = .binding who payload)
    (value : L.Val payload) (completed : setup.proposalRecoveryProtocol.History) : Bool := by
  classical
  let block := SourceProgram.commitPhase residual.tail
  exact match completed.state.bind (fun current => residualEntry? block.suffix
      (fun point => residual.lift
        (cast (congrArg ProtocolState block.reconstruct)
          (block.block.liftPoint block.suffix point))) current.point) with
    | none => false
    | some finished => decide (
        (∀ owner, issuedLedger setup implementation block.block
          control.execution.application.attempt.phase control
          (control.execution.application.attempt.phase + block.block.length) owner
          (finished.view owner)) ∧
        block.block.wordAction who (event.val - control.execution.application.attempt.phase)
          (finished.view who) = decodeEventAction setup.program event
            (cast (congrArg EventField.Action binding.symm) (.success value)))

private def bindingCompletedObservation
    {state : PhaseRuntimeState (serviceGraph setup .concurrent)}
    (checkpoint : RecoverySourceCheckpoint setup .concurrent state)
    (control : (nativeApplication).Control) (who : Player)
    (event : (serviceGraph setup .concurrent).EventId) (payload : L.Ty)
    (binding : (serviceGraph setup .concurrent).outputLayout event = .binding who payload)
    (value : L.Val payload) (completed : setup.proposalRecoveryProtocol.History) : Bool :=
  residualBindingObservation setup implementation checkpoint.residual control who event payload
    binding value completed

open Classical in
/-- The literal selected checkpoint and its backward-transferred entry
checkpoint parse precisely the same maximal complete binding observation. -/
private theorem selected_binding_observation
    (operational : implementation.Operational)
    (control : (nativeApplication).Control) (trace : (nativeProtocol).Trace (some control))
    (who : Player) (event : (serviceGraph setup .concurrent).EventId) (payload : L.Ty)
    (binding : (serviceGraph setup .concurrent).outputLayout event = .binding who payload)
    (entry : NativeBindingEntry setup implementation operational control trace who event)
    (value : L.Val payload) :
    let checkpoint := (checkpointSelection setup implementation operational trace).val.checkpoint
    (SourceProgram.commitPhase checkpoint.residual.tail).block.length = entry.block.length ∧
    bindingCompletedObservation setup implementation checkpoint control who event payload binding
      value =
      (fun completed : setup.proposalRecoveryProtocol.History =>
        match completed.state.bind (fun current => residualEntry? entry.suffix
            (fun point => entry.cursor.lift (entry.block.liftPoint entry.suffix point))
              current.point) with
        | none => false
        | some finished => decide (
            (∀ owner, issuedLedger setup implementation entry.block
              control.execution.application.attempt.phase control
              (control.execution.application.attempt.phase + entry.block.length) owner
              (finished.view owner)) ∧
            entry.block.wordAction who (event.val - control.execution.application.attempt.phase)
              (finished.view who) = decodeEventAction setup.program event
                (cast (congrArg EventField.Action binding.symm) (.success value)))) := by
  classical
  intro checkpoint
  have maximum (program : SourceProgram Player L entry.witness.checkpoint.residual.context
      entry.witness.checkpoint.residual.names)
      (reconstruct : entry.block.prepend entry.suffix = program) :
      SourceProgram.commitPhase program =
        ⟨entry.targetContext, entry.targetNames, entry.suffix, entry.block, reconstruct,
          entry.boundary⟩ := by
    cases reconstruct
    exact maximal_commit_phase entry.block entry.suffix entry.boundary
  obtain ⟨saved, represented⟩ := entry.selected
  have length : (SourceProgram.commitPhase checkpoint.residual.tail).block.length =
      (SourceProgram.commitPhase entry.witness.checkpoint.residual.tail).block.length := by
    rw [represented]
    rfl
  have observed : bindingCompletedObservation setup implementation checkpoint control who event
      payload binding value = bindingCompletedObservation setup implementation
        entry.witness.checkpoint
        control who event payload binding value := by
    rw [represented]
    unfold bindingCompletedObservation
    rfl
  refine ⟨length.trans ?_, observed.trans ?_⟩
  · rw [maximum _ entry.reconstruct]
  · unfold bindingCompletedObservation
    let evaluate := fun phase : SourceProgram.CommitPhase
        entry.witness.checkpoint.residual.tail =>
      fun completed : setup.proposalRecoveryProtocol.History =>
        match completed.state.bind (fun current => residualEntry? phase.suffix
            (fun point => entry.witness.checkpoint.residual.lift
              (cast (congrArg ProtocolState phase.reconstruct)
                (phase.block.liftPoint phase.suffix point))) current.point) with
        | none => false
        | some finished => decide (
            (∀ owner, issuedLedger setup implementation phase.block
              control.execution.application.attempt.phase control
              (control.execution.application.attempt.phase + phase.block.length) owner
              (finished.view owner)) ∧
            phase.block.wordAction who (event.val - control.execution.application.attempt.phase)
              (finished.view who) = decodeEventAction setup.program event
                (cast (congrArg EventField.Action binding.symm) (.success value)))
    have identity : residualBindingObservation setup implementation
        entry.witness.checkpoint.residual control who event payload binding value =
          evaluate (SourceProgram.commitPhase entry.witness.checkpoint.residual.tail) := by
      funext completed
      unfold residualBindingObservation
      dsimp only [evaluate]
      split <;> split
      all_goals simp_all only [Option.some.injEq, reduceCtorEq]
    have moved := congrArg evaluate (maximum _ entry.reconstruct)
    rw [identity, moved]
    have lift : (fun point => entry.witness.checkpoint.residual.lift
        (cast (congrArg ProtocolState entry.reconstruct)
          (entry.block.liftPoint entry.suffix point))) =
        (fun point => entry.cursor.lift (entry.block.liftPoint entry.suffix point)) := by
      funext point
      exact (entry.lift _).symm
    funext completed
    dsimp only [evaluate]
    rw [lift]
    split <;> split
    all_goals simp_all only [Option.some.injEq, reduceCtorEq]

omit [Fintype Player] in
private theorem binding_word_entry_independent
    {Γ Δ : SourceCtx Player L} {O P : Finset VarId}
    (block : SourceProgram.CommitPrefix Γ O Δ P) (suffix : SourceProgram Player L Δ P)
    (embedding : OutputEmbedding (inputLayout setup.context) (outputLayout setup.program)
      (block.prepend suffix))
    (actions : ∀ index action, decodeEventAction setup.program (embedding.event index) action =
      decodeEventAction (block.prepend suffix) index
        (cast (congrArg EventField.Action (embedding.layout_eq index)) action))
    (excluded : Finset Player) (store : Store (graphLayout setup.program))
    (first second : SourceProgram.Config Player L Γ) :
    phaseProposalBindingWord setup.program block suffix embedding excluded store first =
      phaseProposalBindingWord setup.program block suffix embedding excluded store second := by
  classical
  unfold phaseProposalBindingWord
  apply List.map_congr_left
  intro position member
  have inside := List.mem_range.mp member
  let index : Fin (eventCount (block.prepend suffix)) :=
    ⟨position, by have count := block.eventCount_prepend suffix; omega⟩
  funext who
  by_cases inactive : who ∈ excluded
  · simp only [inactive, ↓reduceIte]
  · simp only [inactive, ↓reduceIte]
    obtain ⟨owner, payload, _member, layout⟩ := block.binding_before_length suffix index inside
    by_cases same : owner = who
    · subst owner
      have binding := (embedding.layout_eq index).trans layout
      rw [fillCommitPrefix_wordAction setup.program block suffix embedding actions store first who
        index inside payload binding,
        fillCommitPrefix_wordAction setup.program block suffix embedding actions store second who
          index inside payload binding]
    · have unowned : eventOwner? (block.prepend suffix) index ≠ some who := by
        rw [eventOwner?_eq_actor, EventGraph.actor?_of_outputLayout_binding _ layout]
        exact fun equal => same (Option.some.inj equal)
      rw [compiledCommitPrefix_wordAction_none_of_unowned block suffix who index
        unowned, compiledCommitPrefix_wordAction_none_of_unowned block suffix who
          index unowned]

open Classical in
/-- Every compatible closed entry has the same conditional complete-word
law, obtained by conditioning one source/graph joint before the static cut. -/
private theorem closed_entry_binding_word
    (operational : implementation.Operational)
    (control : (nativeApplication).Control) (trace : (nativeProtocol).Trace (some control))
    (who : Player) (event : (serviceGraph setup .concurrent).EventId) (payload : L.Ty)
    (binding : (serviceGraph setup .concurrent).outputLayout event = .binding who payload)
    (alive : who ∉ control.execution.application.entry.excluded)
    (entry : NativeBindingEntry setup implementation operational control trace who event)
    (value : L.Val payload)
    (current : CommitRecoveryState setup.program)
    (targetTrace : setup.proposalRecoveryProtocol.Trace (some current))
    (erased : setup.proposalRecoveryErasedHistory ⟨some entry.cursor.current, entry.cursor.trace⟩ =
      setup.proposalRecoveryErasedHistory ⟨some current, targetTrace⟩)
    (present : true ∈ (((serviceGraph setup .concurrent).canonicalContinuation
      (phaseProposalBindingPotentialProfile setup .concurrent implementation.runtime
        implementation.leaks implementation.plan entry.entry.execution entry.phase values)
      entry.entry.execution.application.current.native.config).map
      (fun key => issuedBindingObservation setup implementation control entry.phase key &&
        decide ((⟨.inr event, binding⟩ : FieldRef (graphLayout setup.program)
          (.binding who payload)).get? key.2.1 = some (.success value)))).support) :
    let checkpoint := (checkpointSelection setup implementation operational trace).val.checkpoint
    let observed := bindingCompletedObservation setup implementation checkpoint control who event
      payload binding value
    let ordinary := setup.proposalRecoveryModel.runBehavioralFrom
      (sourceUnflaggedStrategy setup values) entry.block.length ⟨some current, targetTrace⟩
    let sourceLaw := fiberPosterior ordinary observed true
    let graphLaw := fiberPosterior
      ((serviceGraph setup .concurrent).canonicalContinuation
        (phaseProposalBindingPotentialProfile setup .concurrent implementation.runtime
          implementation.leaks implementation.plan entry.entry.execution entry.phase values)
        entry.entry.execution.application.current.native.config)
      (fun key => issuedBindingObservation setup implementation control entry.phase key &&
        decide ((⟨.inr event, binding⟩ : FieldRef (graphLayout setup.program)
          (.binding who payload)).get? key.2.1 = some (.success value))) true
    true ∈ (ordinary.map observed).support ∧
      sourceLaw.map (fun completed =>
        ((setup.recoveryJointRecall (setup.proposalRecoveryEraseTrace completed.trace)).take
          entry.block.length).reverse) =
        graphLaw.map (fun key => phaseProposalBindingWord setup.program entry.block entry.suffix
          entry.cursor.embedding control.execution.application.current.excluded key.2.1
            entry.cursor.source) ∧
      ∀ completed ∈ sourceLaw.support,
        ∃ (last : CommitRecoveryState setup.program)
          (lastTrace : setup.proposalRecoveryProtocol.Trace (some last)),
          completed = ⟨some last, lastTrace⟩ ∧ TracePrefix targetTrace lastTrace ∧
          setup.recoveryJointRecall (setup.proposalRecoveryEraseTrace lastTrace) =
            (setup.recoveryJointRecall (setup.proposalRecoveryEraseTrace lastTrace)).take
              entry.block.length ++
                setup.recoveryJointRecall (setup.proposalRecoveryEraseTrace targetTrace) ∧
          ∀ owner, owner ∉ control.execution.application.current.excluded →
            ProtocolState.BindingsHoldValues owner setup.program last.point := by
  classical
  intro checkpoint observed ordinary sourceLaw graphLaw
  let cursor := PhaseProposalOrdinarySourceCursor.of_erasedHistory setup .concurrent
    implementation.runtime implementation.leaks implementation.plan entry.entry entry.phase
    entry.block entry.suffix entry.cursor current targetTrace erased
  have cursorEmbedding : cursor.embedding = entry.cursor.embedding := rfl
  have cursorLift : cursor.lift = entry.cursor.lift := rfl
  have cursorConfig : cursor.config = entry.cursor.config := rfl
  have cursorOffset : cursor.offset = entry.cursor.offset := rfl
  have low : control.execution.application.attempt.phase = entry.phase.low := by
    obtain ⟨rest, phases⟩ := List.head?_eq_some_iff.mp entry.installed
    simp only [PhaseRuntimeState.attempt, phases, List.head?_cons, Option.map_some,
      Option.getD_some]
  have offset : cursor.offset = control.execution.application.attempt.phase := entry.offset.trans
    low.symm
  have originalOffset : entry.cursor.offset = control.execution.application.attempt.phase :=
    entry.offset.trans low.symm
  have length : entry.phase.high = cursor.offset + entry.block.length := by
    have size := entry.size
    have nonempty := entry.phase.nonempty
    have start : cursor.offset = entry.phase.low := entry.offset
    omega
  have selectedInside : event.val - cursor.offset < entry.block.length := by
    have bounds := (entry.phase.mem_events event).mp entry.inside
    have start := entry.offset
    change cursor.offset = entry.phase.low at start
    omega
  let index : Fin (eventCount (entry.block.prepend entry.suffix)) :=
    ⟨event.val - cursor.offset, by have count := entry.block.eventCount_prepend entry.suffix; omega⟩
  have named : cursor.embedding.event index = event := by
    apply Fin.ext
    rw [cursor.compiled.rankEq]
    have bounds := (entry.phase.mem_events event).mp entry.inside
    have start := entry.offset
    change cursor.offset = entry.phase.low at start
    dsimp only [index]
    omega
  have originalNamed : entry.cursor.embedding.event index = event := by
    simpa only [cursorEmbedding] using named
  have saved := Classical.choose entry.selected
  have cursorExcluded : cursor.current.excluded = control.execution.application.entry.excluded :=
    cursor.excluded.trans (entry.entryExcluded.symm.trans (congrArg RecoveryState.excluded saved))
  have selectedBinding : (serviceGraph setup .concurrent).outputLayout
      (cursor.embedding.event index) = .binding who payload := by
    rw [named]
    exact binding
  let sourceObserved := fun completed : setup.proposalRecoveryProtocol.History =>
    match completed.state.bind (fun last => residualEntry? entry.suffix
        (fun point => cursor.lift (entry.block.liftPoint entry.suffix point)) last.point) with
    | none => false
    | some finished => decide (
        (∀ owner, issuedLedger setup implementation entry.block cursor.offset control
          (cursor.offset + entry.block.length) owner (finished.view owner)) ∧
        entry.block.wordAction who index.val (finished.view who) =
          decodeEventAction setup.program (cursor.embedding.event index)
            (cast (congrArg EventField.Action selectedBinding.symm) (.success value)))
  have observation : observed = sourceObserved := by
    have equal := (selected_binding_observation setup implementation operational control
      trace
      who event payload binding entry value).2
    change bindingCompletedObservation setup implementation checkpoint control who event
      payload binding value = sourceObserved
    rw [equal]
    funext completed
    dsimp only [sourceObserved]
    split <;> split
    all_goals simp_all only [Option.some.injEq, reduceCtorEq]
    all_goals
      apply decide_eq_decide.mpr
      have decodeTransport {first second : (serviceGraph setup .concurrent).EventId}
          (same : first = second)
          (layout : (serviceGraph setup .concurrent).outputLayout second = .binding who payload)
          (result : PublicationResult (L.Val payload)) :
          decodeEventAction setup.program first
              (cast (congrArg EventField.Action (same.symm ▸ layout).symm) result) =
            decodeEventAction setup.program second
              (cast (congrArg EventField.Action layout.symm) result) := by
        cases same
        rfl
      have decoded : decodeEventAction setup.program (cursor.embedding.event index)
          (cast (congrArg EventField.Action selectedBinding.symm) (.success value)) =
            decodeEventAction setup.program event
              (cast (congrArg EventField.Action binding.symm) (.success value)) :=
        decodeTransport (show cursor.embedding.event index = event from originalNamed)
          binding (.success value)
      have rankEq : index.val = event.val - entry.phase.low := by
        change event.val - cursor.offset = event.val - entry.phase.low
        exact congrArg (fun low => event.val - low) offset
      rw [decoded, rankEq]
  obtain ⟨joint, sourceMarginal, graphMarginal, supported⟩ :=
    ordinary_binding_conditioned_word_coupling setup values implementation control trace
      entry.entry entry.entryTrace entry.phase entry.block entry.suffix cursor cursorExcluded
      entry.offset.symm length who alive index selectedInside payload selectedBinding value (by
        simpa [issuedBindingObservation, cursorConfig, cursorEmbedding,
          originalNamed, entry.config] using
          present)
  have sourceMarginal' : joint.map Prod.fst = sourceLaw := by
    dsimp only [sourceLaw]
    rw [observation]
    dsimp only [ordinary, cursor, PhaseProposalOrdinarySourceCursor.of_erasedHistory]
      at sourceMarginal ⊢
    refine sourceMarginal.trans ?_
    apply congrArg (fun test : setup.proposalRecoveryProtocol.History → Bool =>
      fiberPosterior ordinary test true)
    funext completed
    dsimp only [sourceObserved]
    split <;> split
    all_goals simp_all only [Option.some.injEq, reduceCtorEq]
    all_goals
      exact decide_eq_decide.mpr Iff.rfl
  have graphMarginal' : joint.map Prod.snd = graphLaw := by
    simpa [graphLaw, cursorConfig, cursorEmbedding, originalNamed,
      issuedBindingObservation, entry.config]
      using graphMarginal
  have sourcePresent : true ∈ (ordinary.map observed).support := by
    obtain ⟨pair, member⟩ := joint.support_nonempty
    have reached : pair.1 ∈ sourceLaw.support := by
      rw [← sourceMarginal']
      exact (PMF.mem_support_map_iff ..).mpr ⟨pair, member, rfl⟩
    have observedTrue : observed pair.1 = true := by
      rw [observation]
      apply Eq.trans ?_ (supported pair member).2.1
      dsimp only [sourceObserved]
      split <;> split
      all_goals simp_all only [Option.some.injEq, reduceCtorEq]
    by_contra absent
    change pair.1 ∈ (fiberPosterior ordinary observed true).support at reached
    rw [fiberPosterior_of_not_mem_support ordinary observed absent] at reached
    exact absent ((PMF.mem_support_map_iff ..).mpr ⟨pair.1, reached, observedTrue⟩)
  refine ⟨sourcePresent, ?_, ?_⟩
  · rw [← sourceMarginal', ← graphMarginal', PMF.map_comp, PMF.map_comp]
    apply map_congr_on_support joint
    intro pair member
    have read := (supported pair member).2.2.2
    have sameSource := binding_word_entry_independent setup entry.block entry.suffix
      entry.cursor.embedding entry.cursor.views.actionEq cursor.current.excluded pair.2.2.1
      cursor.source entry.cursor.source
    exact read.trans (by simpa [cursor,
      PhaseProposalOrdinarySourceCursor.of_erasedHistory, Function.comp_def,
      ← cursor.excluded, entry.excluded] using sameSource)
  · intro completed completedSupported
    have original := (mem_support_fiberPosterior sourcePresent completedSupported).2
    have member : completed ∈ (joint.map Prod.fst).support := by
      rw [sourceMarginal']
      exact completedSupported
    obtain ⟨pair, pairSupported, equal⟩ := (PMF.mem_support_map_iff ..).mp member
    obtain ⟨finished, last, lastTrace, attempt, stateEq, point, excluded, _generation,
      live, _agreement, word, _labels⟩ := (supported pair pairSupported).1
    have completedEq : completed = ⟨some last, lastTrace⟩ := equal.symm.trans stateEq
    have past := (setup.proposalRecoveryModel.runBehavioralFrom_reachesWithin
      (sourceUnflaggedStrategy setup values) entry.block.length ⟨some current, targetTrace⟩
      completed original).tracePrefix
    refine ⟨last, lastTrace, completedEq, ?_, ?_, ?_⟩
    · cases completedEq
      exact past
    · have take : (setup.recoveryJointRecall (setup.proposalRecoveryEraseTrace lastTrace)).take
          entry.block.length = attempt.joints.reverse := by
        rw [word, ← attempt.joints_length, ← List.length_reverse, List.take_left]
      rw [take]
      exact word
    · intro owner active
      rw [point]
      apply (cursor.origin.bindingsHoldValues_lift owner _).mpr
      apply ((entry.block.protocolSuffix entry.suffix).bindingsHoldValues_lift owner _).mpr
      apply (ProtocolState.bindingsHoldValues_entry owner entry.suffix finished).mpr
      exact live owner (by
        rw [excluded, cursor.excluded, ← entry.excluded]
        exact active)

omit [Fintype Player] [L.ResultTypes] in
private theorem structural_replay_eq_of_joints
    {Γ Δ : SourceCtx Player L} {O P : Finset VarId}
    (block : SourceProgram.CommitPrefix Γ O Δ P)
    (entry : SourceProgram.Config Player L Γ) (excluded : Finset Player)
    (first second : SourceProgram.Config Player L Δ) (firstAfter secondAfter : Finset Player)
    (left : block.Attempt entry excluded first firstAfter)
    (right : block.Attempt entry excluded second secondAfter)
    (same : left.joints = right.joints)
    (replacement : SourceProgram.Config Player L Γ) :
    left.withoutMisses ∅ replacement = right.withoutMisses ∅ replacement := by
  induction block generalizing excluded with
  | nil => cases left; cases right; rfl
  | @commit Γ O Δ P name owner payload fresh guard rest ih =>
    cases left with
    | active active result missed valid later =>
      cases right with
      | excluded inactive other => exact (active inactive).elim
      | active otherActive otherResult otherMissed otherValid other =>
        have heads := congrFun (List.cons.inj same).1 owner
        simp only [ite_true,
          Option.some.injEq, CommitRecoveryMove.mk.injEq, OwnAction.commit.injEq,
          heq_eq_eq, true_and] at heads
        obtain ⟨rfl, rfl⟩ := heads
        exact ih _ _ _ _ later other (List.cons.inj same).2 _
    | excluded inactive later =>
      cases right with
      | active active result missed valid other => exact (active inactive).elim
      | excluded otherInactive other =>
        simpa only [SourceProgram.CommitPrefix.Attempt.withoutMisses,
          Finset.notMem_empty, ↓reduceIte] using
            ih _ _ _ _ later other (List.cons.inj same).2 _

/-- At a fixed ordinary entry, the complete retained source word determines
the structural block configuration. Automatic excluded instructions determine
their synthetic structural failures without changing the actual source word. -/
private theorem ordinary_source_structural_projection
    (anchor : (nativeApplication).Control)
    (anchorTrace : (nativeProtocol).Trace (some anchor))
    (phase : RuntimePhase (serviceGraph setup .concurrent))
    {Γ Δ : SourceCtx Player L} {O P : Finset VarId}
    (block : SourceProgram.CommitPrefix Γ O Δ P) (suffix : SourceProgram Player L Δ P)
    (cursor : PhaseProposalOrdinarySourceCursor setup .concurrent implementation.runtime
      implementation.leaks implementation.plan anchor phase block suffix) :
    let law := setup.proposalRecoveryModel.runBehavioralFrom
      (sourceUnflaggedStrategy setup values) block.length ⟨some cursor.current, cursor.trace⟩
    let controls : Finset Player × Nat × Nat :=
      ((anchor.execution.application.publicView.retired.map fun record =>
        record.2.sourceFailureFootprint.2).foldr (fun first last => first ∪ last) ∅ ∪
          anchor.execution.application.current.native.publicView.sourceFailureFootprint.1
            anchor.execution.application.attempt.phase,
        anchor.execution.application.attempt.generation,
        anchor.execution.application.attempt.phase)
    let profile := ordinaryBlockProfile setup .concurrent implementation.plan values
      block suffix cursor.embedding (fun owner view => cursor.views.view owner view)
        controls anchor.execution.application.publicView
          (PhaseProposal.sourceArchive anchor.execution.network.inputs)
    ∃ reconstruct : setup.proposalRecoveryProtocol.History → SourceProgram.Config Player L Δ,
      law.map reconstruct = block.prefixLaw suffix profile cursor.source ∧
      ∀ history ∈ law.support,
        ∃ (finished : SourceProgram.Config Player L Δ)
          (last : CommitRecoveryState setup.program)
          (lastTrace : setup.proposalRecoveryProtocol.Trace (some last))
          (attempt : block.Attempt cursor.source cursor.current.excluded finished last.excluded),
          history = ⟨some last, lastTrace⟩ ∧
          reconstruct history = attempt.withoutMisses ∅ cursor.source ∧
          last.point = cursor.lift (block.liftPoint suffix (ProtocolState.entry suffix finished)) ∧
          last.excluded = cursor.current.excluded ∧
          setup.recoveryJointRecall (setup.proposalRecoveryEraseTrace lastTrace) =
            attempt.joints.reverse ++ setup.recoveryJointRecall
              (setup.proposalRecoveryEraseTrace cursor.trace) ∧
          setup.proposalRecoveryJointRecall lastTrace =
            attempt.joints.reverse.map
              (fun row owner => (row owner).map ProposalRecoveryMove.ordinary) ++
                setup.proposalRecoveryJointRecall cursor.trace ∧
          (∀ owner, owner ∉ last.excluded →
            finished.view owner = (reconstruct history).view owner) ∧
          ∀ row ∈ attempt.joints, ∀ owner move, row owner = some move →
            move.missing = false ∧ ¬ move.action.IsFailure := by
  classical
  intro law controls profile
  obtain ⟨joint, sourceMarginal, structuralMarginal, related⟩ :=
    ordinary_source_structural_joint setup values implementation anchor anchorTrace phase
      block suffix cursor
  have functional (history : setup.proposalRecoveryProtocol.History)
      (first second : SourceProgram.Config Player L Δ)
      (left : (history, first) ∈ joint.support)
      (right : (history, second) ∈ joint.support) : first = second := by
    obtain ⟨firstConfig, firstState, firstTrace, firstAttempt, firstHistory, firstReplay,
      _firstPoint, _firstExcluded, _firstGeneration, firstWord, _firstLabels, _firstViews⟩ :=
        related (history, first) left
    obtain ⟨secondConfig, secondState, secondTrace, secondAttempt, secondHistory, secondReplay,
      _secondPoint, _secondExcluded, _secondGeneration, secondWord, _secondLabels, _secondViews⟩ :=
        related (history, second) right
    have words : firstAttempt.joints = secondAttempt.joints := by
      have read : setup.recoveryJointRecall
          (setup.proposalRecoveryEraseTrace firstTrace) =
            setup.recoveryJointRecall (setup.proposalRecoveryEraseTrace secondTrace) :=
        congrArg (fun retained : setup.proposalRecoveryProtocol.History =>
          setup.recoveryJointRecall (setup.proposalRecoveryEraseTrace retained.trace))
            (firstHistory.symm.trans secondHistory)
      rw [firstWord, secondWord] at read
      exact List.reverse_injective (List.append_cancel_right read)
    exact firstReplay.trans ((structural_replay_eq_of_joints block cursor.source
      cursor.current.excluded firstConfig secondConfig firstState.excluded secondState.excluded
        firstAttempt secondAttempt words cursor.source).trans secondReplay.symm)
  let default := Classical.choose joint.support_nonempty
  let reconstruct := fun history : setup.proposalRecoveryProtocol.History =>
    if witness : ∃ finished, (history, finished) ∈ joint.support then Classical.choose witness
    else default.2
  have reconstructEq (pair : setup.proposalRecoveryProtocol.History ×
      SourceProgram.Config Player L Δ) (member : pair ∈ joint.support) :
      reconstruct pair.1 = pair.2 := by
    have witness : ∃ finished, (pair.1, finished) ∈ joint.support := ⟨pair.2, member⟩
    dsimp only [reconstruct]
    split
    · next present =>
        exact functional pair.1 _ pair.2 (Classical.choose_spec present) member
    · next absent => exact (absent witness).elim
  refine ⟨reconstruct, ?_, ?_⟩
  · calc
      law.map reconstruct = (joint.map Prod.fst).map reconstruct :=
        congrArg (PMF.map reconstruct) sourceMarginal.symm
      _ = joint.map (reconstruct ∘ Prod.fst) := PMF.map_comp _ _ _
      _ = joint.map Prod.snd :=
        map_congr_on_support joint (fun pair member => reconstructEq pair member)
      _ = block.prefixLaw suffix profile cursor.source := structuralMarginal
  · intro history member
    have mapped : history ∈ (joint.map Prod.fst).support := sourceMarginal.symm ▸ member
    obtain ⟨pair, reached, sourceEq⟩ := (PMF.mem_support_map_iff ..).mp mapped
    obtain ⟨finished, last, lastTrace, attempt, historyEq, replay, point, excluded,
      _generation, word, labels, views⟩ := related pair reached
    refine ⟨finished, last, lastTrace, attempt, sourceEq.symm.trans historyEq,
      ?_, point, excluded, word, labels, ?_, ?_⟩
    · rw [← sourceEq, reconstructEq pair reached]
      exact replay
    · intro owner active
      rw [← sourceEq, reconstructEq pair reached]
      exact views owner active
    · obtain ⟨actual, actualState, actualTrace, actualAttempt, actualHistory,
        _actualPoint, _actualExcluded, _actualEntry, _actualGeneration, actualWord,
        _actualLabels, actualProper⟩ :=
        proposalRecovery_ordinary_commit_block_support setup values block suffix cursor.lift
          cursor.origin cursor.source cursor.current cursor.trace cursor.point
            (cursor.excluded.trans cursor.entryExcluded.symm) history member
      have words : attempt.joints = actualAttempt.joints := by
        have equal := congrArg (fun retained : setup.proposalRecoveryProtocol.History =>
          setup.recoveryJointRecall (setup.proposalRecoveryEraseTrace retained.trace))
            ((sourceEq.symm.trans historyEq).symm.trans actualHistory)
        rw [word, actualWord] at equal
        exact List.reverse_injective (List.append_cancel_right equal)
      simpa only [words] using actualProper

open Classical in
/-- A supported actual source completion retaining the issued ledgers gives
a positive foreign cylinder in the literal ordinary joint. This implication
is proved before annotation normalization and also applies to every supported
closed-key history. -/
theorem ordinaryForeignJoint_positive_of_source_ledger
    (operational : implementation.Operational)
    (who : Player) (control : (nativeApplication).Control)
    (trace : (nativeProtocol).Trace (some control))
    (phase : RuntimePhase (serviceGraph setup .concurrent))
    (saved : control.execution.application.current.excluded =
      control.execution.application.entry.excluded) :
    let checkpoint := (checkpointSelection setup implementation operational trace).val.checkpoint
    let block := SourceProgram.commitPhase checkpoint.residual.tail
    ∀ cursor : PhaseProposalOrdinarySourceCursor setup .concurrent implementation.runtime
        implementation.leaks implementation.plan control phase block.block block.suffix,
      0 < block.block.length →
      cursor.embedding = cast (congrArg (fun program => OutputEmbedding
        (inputLayout setup.context) (outputLayout setup.program) program)
          block.reconstruct.symm) checkpoint.embedding →
      (∀ point, cursor.lift point = checkpoint.residual.lift
        (cast (congrArg ProtocolState block.reconstruct) point)) →
      (∀ owner view, cursor.views.view owner view = checkpoint.views.view owner
        (cast (congrArg (ProtocolView owner) block.reconstruct) view)) →
    let observed := fun history : setup.proposalRecoveryProtocol.History =>
      match history.state.bind (fun current => residualEntry? block.suffix
          (fun point => cursor.lift (block.block.liftPoint block.suffix point)) current.point) with
      | none => false
      | some finished => decide (∀ owner, issuedLedger setup implementation block.block
          control.execution.application.attempt.phase control
            (control.execution.application.attempt.phase + block.block.length) owner
              (finished.view owner))
    true ∈ ((setup.proposalRecoveryModel.runBehavioralFrom (sourceUnflaggedStrategy setup values)
      block.block.length ⟨some cursor.current, cursor.trace⟩).map observed).support →
    true ∈ ((ordinaryForeignJoint setup values implementation operational who
      ⟨some control, trace⟩ ⟨some cursor.current, cursor.trace⟩).map Prod.snd).support := by
  classical
  intro checkpoint block cursor positive embedding lift views observed present
  obtain ⟨joint, sourceMarginal, structuralMarginal, supported⟩ :=
    ordinary_source_structural_joint setup values implementation control trace phase block.block
      block.suffix cursor
  obtain ⟨history, reached, measured⟩ := (PMF.mem_support_map_iff ..).mp present
  have reachedJoint : history ∈ (joint.map Prod.fst).support := by
    rw [sourceMarginal]
    exact reached
  obtain ⟨pair, member, sourceEq⟩ := (PMF.mem_support_map_iff ..).mp reachedJoint
  obtain ⟨finished, last, lastTrace, attempt, historyEq, structuralEq, point,
    excluded, _generation, _word, _labels, activeViews⟩ := supported pair member
  have pulled : residualEntry? block.suffix
      (fun point => cursor.lift (block.block.liftPoint block.suffix point)) last.point =
        some finished :=
    (residualEntry?_eq_some_iff (cursor.origin.compose (block.block.protocolSuffix block.suffix))
      last.point finished).mpr point.symm
  have sourceObserved : observed pair.1 = true := (congrArg observed sourceEq).trans measured
  have sourceLedger : ∀ owner, issuedLedger setup implementation block.block
      control.execution.application.attempt.phase control
        (control.execution.application.attempt.phase + block.block.length) owner
          (finished.view owner) := by
    simpa only [observed, historyEq, Option.bind_some, pulled, decide_eq_true_eq]
      using sourceObserved
  have actualLedger : ∀ owner, issuedLedger setup implementation block.block
      control.execution.application.attempt.phase control
        (control.execution.application.attempt.phase + block.block.length) owner
          (pair.2.view owner) := by
    intro owner
    by_cases omitted : owner ∈ control.execution.application.entry.excluded
    · intro event payload binding candidate message emitted attemptMatch packetMatch interval
      have raw := (nativeMenu).toRawTrace nativeInitial implementation.horizon
        implementation.scheduler trace
      have inputRecall := (nativeApplication).history_inputRecall nativeInitial
        implementation.horizon
        implementation.scheduler raw owner
      have input : message ∈ control.execution.network.inputs := by
        rw [← inputRecall] at emitted
        exact (List.mem_filter.mp emitted).1
      have active := issued_binding_owner_active setup implementation control trace owner event
        payload binding candidate message input attemptMatch packetMatch
      exact (active omitted).elim
    · have live : owner ∉ last.excluded := by
        rw [excluded, cursor.excluded, saved]
        exact omitted
      rw [← activeViews owner live]
      exact sourceLedger owner
  have footprint :
      (control.execution.application.publicView.retired.map fun record =>
        record.2.sourceFailureFootprint.2).foldr (fun first last => first ∪ last) ∅ ∪
          control.execution.application.current.native.publicView.sourceFailureFootprint.1
            control.execution.application.attempt.phase =
        control.execution.application.entry.excluded := by
    have current := congrArg Prod.fst (cursor.controls positive)
    change cursor.current.excluded = _ at current
    exact current.symm.trans (cursor.excluded.trans saved)
  have structuralSupport : pair.2 ∈
      (block.block.prefixLaw block.suffix
        (ordinaryBlockProfile setup .concurrent implementation.plan values block.block block.suffix
          cursor.embedding (fun owner view => cursor.views.view owner view)
            (control.execution.application.entry.excluded, control.execution.application.generation,
              control.execution.application.attempt.phase) control.execution.application.publicView
                (PhaseProposal.sourceArchive control.execution.network.inputs))
                  cursor.source).support := by
    have mapped : pair.2 ∈ (joint.map Prod.snd).support :=
      (PMF.mem_support_map_iff ..).mpr ⟨pair, member, rfl⟩
    rw [structuralMarginal] at mapped
    rw [footprint] at mapped
    simpa only [PhaseRuntimeState.attempt] using mapped
  rw [ordinaryForeignJoint_of_selected_cursor setup values implementation operational who control
    trace phase cursor positive embedding lift views, PMF.map_comp]
  exact (PMF.mem_support_map_iff ..).mpr
    ⟨pair.2, structuralSupport, decide_eq_true (fun owner _ => actualLedger owner)⟩

omit [Fintype Player] in
/-- A complete history determines its retained cut at a fixed literal depth.
This lifts equality of completion marginals to equality of both coordinates. -/
private theorem source_pair_eq_of_completed
    (left right : PMF
      (setup.proposalRecoveryProtocol.History × setup.proposalRecoveryProtocol.History))
    (depth : Nat)
    (leftPrefix : ∀ pair ∈ left.support, TracePrefix pair.1.trace pair.2.trace)
    (rightPrefix : ∀ pair ∈ right.support, TracePrefix pair.1.trace pair.2.trace)
    (leftDepth : ∀ pair ∈ left.support, pair.1.trace.length = depth)
    (rightDepth : ∀ pair ∈ right.support, pair.1.trace.length = depth)
    (completed : left.map Prod.snd = right.map Prod.snd) : left = right := by
  have lifted := bind_eq_of_map_eq left right Prod.snd Prod.snd completed PMF.pure PMF.pure (by
    intro first firstMember second secondMember same
    apply congrArg PMF.pure
    apply Prod.ext
    · have firstKept := leftPrefix first firstMember
      have secondKept := rightPrefix second secondMember
      rw [← same] at secondKept
      exact firstKept.eq_of_same_length secondKept
        ((leftDepth first firstMember).trans (rightDepth second secondMember).symm)
    · exact same)
  simpa only [PMF.bind_pure] using lifted

/-- The split ordinary run retains the literal cut as a prefix of its
completion, at the exact depth of the first commitment segment. Empty first
segments are included. -/
private theorem ordinary_source_pair_geometry
    (anchor : (nativeApplication).Control)
    (phase : RuntimePhase (serviceGraph setup .concurrent))
    {Γ Δ Ξ : SourceCtx Player L} {O P Q : Finset VarId}
    (before : SourceProgram.CommitPrefix Γ O Δ P)
    (after : SourceProgram.CommitPrefix Δ P Ξ Q)
    (suffix : SourceProgram Player L Ξ Q)
    (cursor : PhaseProposalOrdinarySourceCursor setup .concurrent implementation.runtime
      implementation.leaks implementation.plan anchor phase (before.append after) suffix) :
    let profile := sourceUnflaggedStrategy setup values
    let law := (setup.proposalRecoveryModel.runBehavioralFrom profile before.length
      ⟨some cursor.current, cursor.trace⟩).bind fun cut =>
        (setup.proposalRecoveryModel.runBehavioralFrom profile after.length cut).map (Prod.mk cut)
    ∀ pair ∈ law.support, TracePrefix pair.1.trace pair.2.trace ∧
      pair.1.trace.length = cursor.trace.length + before.length := by
  classical
  intro profile law pair member
  obtain ⟨cut, first, continued⟩ := (PMF.mem_support_bind_iff ..).mp member
  obtain ⟨completed, last, rfl⟩ := (PMF.mem_support_map_iff ..).mp continued
  refine ⟨(setup.proposalRecoveryModel.runBehavioralFrom_reachesWithin
    profile after.length cut completed last).tracePrefix, ?_⟩
  obtain ⟨lift, origin, point⟩ :
      ∃ lift : ProtocolState (before.prepend (after.prepend suffix)) →
          ProtocolState setup.program,
        ProtocolSuffix setup.program (before.prepend (after.prepend suffix)) lift ∧
        cursor.current.point = lift
          (ProtocolState.entry (before.prepend (after.prepend suffix)) cursor.source) := by
    rw [← before.prepend_append after suffix]
    exact ⟨cursor.lift, cursor.origin, cursor.point⟩
  obtain ⟨finished, current, trace, attempt, same, _point, _excluded, _entry,
      _generation, word, _labels, _proper⟩ :=
    proposalRecovery_ordinary_commit_block_support setup values before (after.prepend suffix)
      lift origin cursor.source cursor.current cursor.trace point
        (cursor.excluded.trans cursor.entryExcluded.symm) cut first
  change cut.trace.length = cursor.trace.length + before.length
  rw [same]
  have length := congrArg List.length word
  simpa only [setup.recoveryJointRecall_length, setup.proposalRecoveryEraseTrace_length,
    List.length_append, List.length_reverse, attempt.joints_length,
    Nat.add_comm] using length

/-- The dynamic completion fuel of a listed proper ordinary word is exactly
the remaining length of the original maximal commitment telescope. The cut
may precede its first row. -/
private theorem source_word_pair_fuel
    (anchor : (nativeApplication).Control)
    (phase : RuntimePhase (serviceGraph setup .concurrent))
    {Γ Δ Ξ : SourceCtx Player L} {O P Q : Finset VarId}
    (before : SourceProgram.CommitPrefix Γ O Δ P)
    (after : SourceProgram.CommitPrefix Δ P Ξ Q) (suffix : SourceProgram Player L Ξ Q)
    (boundary : IsCommitBoundary suffix)
    (cursor : PhaseProposalOrdinarySourceCursor setup .concurrent implementation.runtime
      implementation.leaks implementation.plan anchor phase (before.append after) suffix)
    (word : SourceProgram.History Player L) (views : ∀ owner, DecisionView owner Ξ)
    (readout : ∀ owner action, action ∈ word owner →
      ∃ index, (before.append after).wordAction owner index (views owner) = some action)
    (proper : ∀ owner action, action ∈ word owner → ¬ action.IsFailure) :
    let profile := sourceBlockWordStrategy setup values word
    let varying := (setup.proposalRecoveryModel.runBehavioralFrom profile before.length
      ⟨some cursor.current, cursor.trace⟩).bind fun cut =>
        (setup.proposalRecoveryModel.runBehavioralFrom profile (sourceCommitFuel setup cut) cut).map
          (Prod.mk cut)
    let fixed := (setup.proposalRecoveryModel.runBehavioralFrom profile before.length
      ⟨some cursor.current, cursor.trace⟩).bind fun cut =>
        (setup.proposalRecoveryModel.runBehavioralFrom profile after.length cut).map (Prod.mk cut)
    varying = fixed ∧ ∀ pair ∈ varying.support,
      TracePrefix pair.1.trace pair.2.trace ∧
        pair.1.trace.length = cursor.trace.length + before.length := by
  classical
  intro profile varying fixed
  let table := fun owner (key : setup.ProposalRecoveryComponent owner) =>
    if offered : ∃ choice : setup.CommitRecoveryValueChoice owner key.1,
        ∃ action ∈ word owner, choice.val.val = some ⟨action, false⟩ then
      PMF.pure (Classical.choose offered)
    else values owner key
  have strategy : profile = sourceUnflaggedStrategy setup table :=
    source_word_strategy_table setup values (before.append after) word views readout proper
  obtain ⟨lift, origin, point⟩ :
      ∃ lift : ProtocolState (before.prepend (after.prepend suffix)) →
          ProtocolState setup.program,
        ProtocolSuffix setup.program (before.prepend (after.prepend suffix)) lift ∧
        cursor.current.point = lift
          (ProtocolState.entry (before.prepend (after.prepend suffix)) cursor.source) := by
    rw [← before.prepend_append after suffix]
    exact ⟨cursor.lift, cursor.origin, cursor.point⟩
  have remaining (cut : setup.proposalRecoveryProtocol.History)
      (member : cut ∈ (setup.proposalRecoveryModel.runBehavioralFrom profile before.length
        ⟨some cursor.current, cursor.trace⟩).support) : sourceCommitFuel setup cut = after.length
          := by
    rw [strategy] at member
    obtain ⟨finished, last, lastTrace, _attempt, history, lastPoint, _excluded, _entry,
      _generation, _word, _labels, _proper⟩ :=
      proposalRecovery_ordinary_commit_block_support setup table before (after.prepend suffix)
        lift origin cursor.source cursor.current cursor.trace point
          (cursor.excluded.trans cursor.entryExcluded.symm) cut member
    let tailOrigin := origin.compose (before.protocolSuffix (after.prepend suffix))
    rw [history]
    change ProtocolState.remaining setup.program last.point -
      ProtocolState.commitEnd setup.program last.point = after.length
    rw [lastPoint, tailOrigin.remaining_lift, tailOrigin.commitEnd_lift,
      ProtocolState.remaining_entry, after.commitEnd_entry_prepend suffix boundary]
    have length := after.instructionCount_prepend suffix
    omega
  have equality : varying = fixed := by
    apply bind_congr_on_support
    intro cut member
    rw [remaining cut member]
  refine ⟨equality, ?_⟩
  rw [equality]
  simpa only [fixed, strategy] using ordinary_source_pair_geometry setup table implementation
    anchor phase before after suffix cursor

omit [Fintype Player] in
private theorem binding_material_action
    (owner : Player) (event : (serviceGraph setup .concurrent).EventId) (payload : L.Ty)
    (binding : (serviceGraph setup .concurrent).outputLayout event = .binding owner payload)
    (response : (nativeApplication).Action)
    (material : WitnessedSubmission (serviceGraph setup .concurrent))
    (transmitted : response.transmission = some material)
    (candidate : Handle (serviceGraph setup .concurrent))
    (named : material.call.packet = .commitment event candidate) :
    phaseBindingAction? setup.program .concurrent implementation.runtime implementation.leaks
      response = decodeEventAction setup.program event
        (cast (congrArg EventField.Action binding.symm)
          ((material.call.opening.bind fun raw => raw.as? payload).elim
            .failure PublicationResult.success)) := by
  simp only [phaseBindingAction?, transmitted, named]
  split
  · rename_i other domain shape
    cases shape.symm.trans binding
    cases decoded : material.call.opening.bind (fun raw => raw.as? payload) <;> rfl
  · rename_i _ shape
    exact (shape owner payload binding).elim

/-- The actions mentioned in the focal raw recall are exactly the earlier
owned rows of any retained source ledger. This uses the actual signed records
and readiness, and permits arbitrary inherited exclusions. -/
private theorem issued_ledger_recall_actions
    {Γ Δ : SourceCtx Player L} {O P : Finset VarId}
    (block : SourceProgram.CommitPrefix Γ O Δ P) (suffix : SourceProgram Player L Δ P)
    (embedding : OutputEmbedding (inputLayout setup.context) (outputLayout setup.program)
      (block.prepend suffix)) (low : Nat)
    (rank : ∀ index, (embedding.event index).val = low + index.val)
    (actions : ∀ index action, decodeEventAction setup.program (embedding.event index) action =
      decodeEventAction (block.prepend suffix) index
        (cast (congrArg EventField.Action (embedding.layout_eq index)) action))
    (control : (nativeApplication).Control) (trace : (nativeProtocol).Trace (some control))
    (phase : RuntimePhase (serviceGraph setup .concurrent))
    (installed : control.execution.application.phases.head? = some phase)
    (phaseLow : phase.low = low) (phaseHigh : phase.high = low + block.length)
    (owner : Player) (selected : (serviceGraph setup .concurrent).EventId) (payload : L.Ty)
    (binding : (serviceGraph setup .concurrent).outputLayout selected = .binding owner payload)
    (request : control.execution.application.SeedRequest owner
      ⟨control.execution.application.attempt, selected⟩)
    (selectedInside : low ≤ selected.val ∧ selected.val < low + block.length)
    (reference : DecisionView owner Δ)
    (retained : issuedLedger setup implementation block low control (low + block.length)
      owner reference) :
    ∀ action, action ∈ phaseCommitRecallWord setup.program .concurrent implementation.runtime
        implementation.leaks low selected.val control.execution.application.generation
          (control.execution.recall owner) ↔
      ∃ position < selected.val - low, block.wordAction owner position reference = some action := by
  classical
  let inputs := setup.initialLaw.map encodeInputs
  let initialLaw := inputs.map (PhaseRuntimeState.initial implementation.plan)
  have initialEq : initialLaw = nativeInitial := PMF.map_comp _ _ _
  have counted : ((nativeMenu).protocol initialLaw implementation.horizon
      implementation.scheduler).Trace (some control) := initialEq.symm ▸ trace
  have raw := (nativeMenu).toRawTrace nativeInitial implementation.horizon
    implementation.scheduler trace
  have inputRecall := (nativeApplication).history_inputRecall nativeInitial implementation.horizon
    implementation.scheduler raw owner
  have address : control.execution.application.attempt =
      ⟨low, control.execution.application.generation⟩ := by
    have phaseEq : control.execution.application.attempt.phase = low := by
      simp only [PhaseRuntimeState.attempt, installed, Option.map_some, Option.getD_some, phaseLow]
    exact congrArg (fun phase =>
      (⟨phase, control.execution.application.generation⟩ : CommitAttemptId)) phaseEq
  have clean := (PhaseCount.onePacketMenu_countClean implementation.runtime implementation.leaks
    implementation.bounds implementation.scheduler).history nativeInitial implementation.horizon
      (fun state _ => PhaseCount.countClean_initial implementation.runtime implementation.leaks
        state) trace
  have emissionAction
      (event : (serviceGraph setup .concurrent).EventId) (domain : L.Ty)
      (shape : (serviceGraph setup .concurrent).outputLayout event = .binding owner domain)
      (candidate : Handle (serviceGraph setup .concurrent))
      (message : Message Player (CommitAttemptPacket (serviceGraph setup .concurrent)))
      (emitted : message ∈ (nativeApplication).outputs (control.execution.recall owner))
      (attemptMatch : message.payload.attempt = control.execution.application.attempt)
      (call : message.payload.packet.call = .commitment event candidate)
      (interval : low ≤ event.val ∧ event.val < low + block.length) :
      ∃ record ∈ control.execution.recall owner,
        record.emitted = some message ∧
        phaseBindingAction? setup.program .concurrent implementation.runtime implementation.leaks
          record.action = block.wordAction owner (event.val - low) reference := by
    obtain ⟨serial, opening, evidence, record, slot, recorded, sent, declared, _fresh, result⟩ :=
      retained event domain shape candidate message emitted attemptMatch call interval
    let material : WitnessedSubmission (serviceGraph setup .concurrent) :=
      ⟨⟨.commitment event (owner, .prepared serial), opening⟩, evidence⟩
    have decoded := binding_material_action setup implementation owner event domain shape
      record.action material (by rw [declared]) (owner, .prepared serial) rfl
    have inside : event.val - low < block.length := by omega
    let index : Fin (eventCount (block.prepend suffix)) :=
      ⟨event.val - low, by have count := block.eventCount_prepend suffix; omega⟩
    have named : embedding.event index = event := by
      apply Fin.ext
      rw [rank]
      dsimp only [index]
      omega
    have codec := phaseCommitWordAction_decode setup .concurrent block suffix embedding actions
      owner index inside domain (named.symm ▸ shape) reference
    have dataTransport {first second : (serviceGraph setup .concurrent).EventId}
        (same : first = second)
        (layout : (serviceGraph setup .concurrent).outputLayout second = .binding owner domain)
        (word : Option (OwnAction Player L)) :
        (phaseRecoveryBindingData setup .concurrent first owner domain
          (same.symm ▸ layout) (CommitRecoveryMove.lift word)).1 =
        (phaseRecoveryBindingData setup .concurrent second owner domain
          layout (CommitRecoveryMove.lift word)).1 := by
      cases same
      rfl
    have decodeTransport {first second : (serviceGraph setup .concurrent).EventId}
        (same : first = second)
        (layout : (serviceGraph setup .concurrent).outputLayout second = .binding owner domain)
        (result : PublicationResult (L.Val domain)) :
        decodeEventAction setup.program first
            (cast (congrArg EventField.Action (same.symm ▸ layout).symm) result) =
          decodeEventAction setup.program second
            (cast (congrArg EventField.Action layout.symm) result) := by
      cases same
      rfl
    have codec' : decodeEventAction setup.program event
      (cast (congrArg EventField.Action shape.symm)
        (phaseRecoveryBindingData setup .concurrent event owner domain shape
          (CommitRecoveryMove.lift
            (block.wordAction owner (event.val - low) reference))).1) =
        block.wordAction owner (event.val - low) reference := by
      calc
        _ = decodeEventAction setup.program event
            (cast (congrArg EventField.Action shape.symm)
              (phaseRecoveryBindingData setup .concurrent (embedding.event index) owner domain
                (named.symm ▸ shape) (CommitRecoveryMove.lift
                  (block.wordAction owner (event.val - low) reference))).1) := by
              rw [← dataTransport named shape]
        _ = decodeEventAction setup.program (embedding.event index)
            (cast (congrArg EventField.Action (named.symm ▸ shape).symm)
              (phaseRecoveryBindingData setup .concurrent (embedding.event index) owner domain
                (named.symm ▸ shape) (CommitRecoveryMove.lift
                  (block.wordAction owner (event.val - low) reference))).1) :=
            (decodeTransport named shape _).symm
        _ = block.wordAction owner (event.val - low) reference := by
          simpa only [index] using codec
    refine ⟨record, recorded, sent, decoded.trans ?_⟩
    exact (congrArg (fun value => decodeEventAction setup.program event
      (cast (congrArg EventField.Action shape.symm) value)) result).trans codec'
  intro action
  constructor
  · intro member
    obtain ⟨record, recorded, parsed⟩ := List.mem_filterMap.mp member
    split at parsed
    · rename_i attempt
      cases transmitted : record.action.transmission with
      | none => simp only [transmitted, reduceCtorEq] at parsed
      | some material =>
        simp only [transmitted] at parsed
        cases packet : material.call.packet with
        | opening | malformed => simp only [packet, reduceCtorEq] at parsed
        | commitment event candidate =>
          simp only [packet] at parsed
          split at parsed
          · rename_i interval
            obtain ⟨message, emitted, sender, emittedCall⟩ :=
              PhaseCount.recalled_submission_emitted implementation.runtime implementation.leaks
                nativeInitial implementation.horizon implementation.scheduler raw owner record
                  recorded material transmitted
            have output : message ∈ (nativeApplication).outputs (control.execution.recall owner) :=
              List.mem_filterMap.mpr ⟨record, recorded, emitted⟩
            have input : message ∈ control.execution.network.inputs := by
              rw [← inputRecall] at output
              exact (List.mem_filter.mp output).1
            have call : message.payload.packet.call = .commitment event candidate :=
              emittedCall.trans packet
            have correct := ((PhaseCount.permits_eq_true_iff _ _).mp (clean.2 message input)).2.1
            change CountCallCorrect _ (PhaseCount.nativeMessage message) at correct
            simp only [CountCallCorrect, PhaseCount.nativeMessage, call] at correct
            obtain ⟨owned, _evidence, _candidateOwner, _prepared, _unused⟩ := correct
            have typed : ∃ domain,
                (serviceGraph setup .concurrent).outputLayout event = .binding owner domain := by
              cases shape : (serviceGraph setup .concurrent).outputLayout event <;>
                simp only [bindingOwnedBy, shape, Bool.false_eq_true, decide_eq_true_eq] at owned
              rename_i actor domain
              subst actor
              exact ⟨domain, by
                have senderShape := congrArg (fun actor => EventField.binding actor domain) sender
                simpa only [Message.sender] using senderShape⟩
            obtain ⟨domain, shape⟩ := typed
            have attemptMatch : message.payload.attempt = control.execution.application.attempt :=
              (phase_recalled_emission_attempt implementation.runtime implementation.leaks
                nativeInitial implementation.horizon implementation.scheduler raw owner record
                  recorded message emitted).trans (attempt.trans address.symm)
            obtain ⟨actual, actualMember, actualSent, decoded⟩ := emissionAction event domain shape
              candidate message output attemptMatch call ⟨interval.1, by omega⟩
            have same := recorded_emission_unique setup implementation trace owner actual record
              actualMember recorded message actualSent emitted
            rw [same, parsed] at decoded
            exact ⟨event.val - low, by omega, decoded.symm⟩
          · cases parsed
    · cases parsed
  · rintro ⟨position, before, selectedAction⟩
    have inside : position < block.length := by omega
    let index : Fin (eventCount (block.prepend suffix)) :=
      ⟨position, by have count := block.eventCount_prepend suffix; omega⟩
    have owns : eventOwner? (block.prepend suffix) index = some owner := by
      by_contra absent
      have none := compiledCommitPrefix_wordAction_none_of_unowned block suffix owner index
        absent reference
      rw [selectedAction] at none
      cases none
    obtain ⟨actor, domain, _member, layout⟩ := block.binding_before_length suffix index inside
    have sameOwner : actor = owner := by
      have actorEq := EventGraph.actor?_of_outputLayout_binding
        (toEventGraph (block.prepend suffix)) layout
      rw [eventOwner?_eq_actor, actorEq] at owns
      exact Option.some.inj owns
    subst actor
    have shape : (serviceGraph setup .concurrent).outputLayout (embedding.event index) =
        .binding owner domain := (embedding.layout_eq index).trans layout
    have interval : low ≤ (embedding.event index).val ∧
        (embedding.event index).val < low + block.length := by
      rw [rank]
      dsimp only [index]
      omega
    have phaseMember : embedding.event index ∈ phase.events := (phase.mem_events _).mpr (by
      simpa only [phaseLow, phaseHigh] using interval)
    have earlier : (embedding.event index).val < selected.val := by
      rw [rank]
      dsimp only [index]
      omega
    obtain ⟨candidate, owned, accepted, _read⟩ := phase_ready_earlier_binding_read
      implementation.runtime implementation.leaks implementation.bounds implementation.plan inputs
        implementation.horizon implementation.scheduler counted
          (serviceGraph_revealRelaxedOrdered setup .concurrent) phase installed owner selected
            payload binding request.2.2.1 request.2.2.2.2 (embedding.event index) domain shape
              phaseMember earlier
    have stamped := phaseLiveBindingStamp_history implementation.runtime implementation.leaks
      implementation.plan inputs implementation.horizon implementation.scheduler
        ((nativeMenu).toRawTrace initialLaw implementation.horizon implementation.scheduler counted)
    rcases stamped (embedding.event index) candidate accepted with old |
        ⟨message, output, _sender, call, attemptMatch⟩
    · have lower : control.execution.application.attempt.phase = low :=
        congrArg CommitAttemptId.phase address
      rw [lower] at old
      omega
    · rw [owned] at output
      obtain ⟨record, recorded, emitted, decoded⟩ := emissionAction (embedding.event index)
        domain shape candidate message output attemptMatch call interval
      obtain ⟨serial, opening, evidence, actual, slot, actualMember, actualSent, declared,
          _fresh, _result⟩ := retained (embedding.event index) domain shape candidate message
            output attemptMatch call interval
      have same := recorded_emission_unique setup implementation trace owner actual record
        actualMember recorded message actualSent emitted
      subst actual
      have atRecord := phase_recalled_emission_attempt implementation.runtime implementation.leaks
        nativeInitial implementation.horizon implementation.scheduler raw owner record recorded
          message emitted
      have offset : (embedding.event index).val - low = position := by
        rw [rank]
        dsimp only [index]
        omega
      apply phaseCommitRecallWord_mem setup.program .concurrent implementation.runtime
        implementation.leaks low selected.val control.execution.application.generation
          (control.execution.recall owner) record recorded
            (atRecord.symm.trans (attemptMatch.trans address))
              ⟨⟨.commitment (embedding.event index) (owner, .prepared serial), opening⟩, evidence⟩
                (by rw [declared]) (embedding.event index) (owner, .prepared serial) rfl
                  ⟨interval.1, earlier⟩ action
      exact decoded.trans (offset ▸ selectedAction)

/-- Keeping the completed coordinate of a conditioned split run gives the
conditioned unsplit source continuation. Both histories in the split run
start from the same original source entry. -/
theorem source_split_pair_completed_posterior
    (profile : ∀ owner, setup.proposalRecoveryModel.BehavioralPolicy owner)
    (before after : Nat) (entry : setup.proposalRecoveryProtocol.History)
    (observed : setup.proposalRecoveryProtocol.History → Bool)
    (present : true ∈ ((setup.proposalRecoveryModel.runBehavioralFrom profile
      (before + after) entry).map observed).support) :
    (fiberPosterior
      ((setup.proposalRecoveryModel.runBehavioralFrom profile before entry).bind fun cut =>
        (setup.proposalRecoveryModel.runBehavioralFrom profile after cut).map (Prod.mk cut))
      (observed ∘ Prod.snd) true).map Prod.snd =
      fiberPosterior (setup.proposalRecoveryModel.runBehavioralFrom profile
        (before + after) entry) observed true := by
  let pair := (setup.proposalRecoveryModel.runBehavioralFrom profile before entry).bind
    fun cut => (setup.proposalRecoveryModel.runBehavioralFrom profile after cut).map (Prod.mk cut)
  have completed : pair.map Prod.snd =
      setup.proposalRecoveryModel.runBehavioralFrom profile (before + after) entry := by
    dsimp only [pair]
    simp only [PMF.map_bind, PMF.map_comp, Function.comp_def]
    simp only [show (fun x : setup.proposalRecoveryProtocol.History => x) = id from rfl,
      PMF.map_id]
    exact (setup.proposalRecoveryModel.runBehavioralFrom_add profile before after entry).symm
  have paired : true ∈ (pair.map (observed ∘ Prod.snd)).support := by
    rw [← PMF.map_comp, completed]
    exact present
  change (fiberPosterior pair (observed ∘ Prod.snd) true).map Prod.snd = _
  rw [map_fiberPosterior_readout pair Prod.snd observed true paired, completed]

/-- A positive finite restricted mass identifies the actual posterior without
ever choosing a value on a zero conditioning fiber. -/
private theorem posterior_of_scaled_restriction
    {Point : Type*} (law conditional : PMF Point) (observed : Point → Bool)
    (mass : ℝ≥0∞) (positive : mass ≠ 0) (finite : mass ≠ ⊤)
    (restriction : ∀ point, (if observed point then law point else 0) =
      mass * conditional point) :
    true ∈ (law.map observed).support ∧
      fiberPosterior law observed true = conditional := by
  classical
  have normalizer : (law.map observed) true = mass := by
    rw [PMF.map_apply]
    calc
      _ =
          ∑' point, mass * conditional point := by
        apply tsum_congr
        intro point
        convert restriction point using 1
        cases observed point <;> simp
      _ = mass := by rw [ENNReal.tsum_mul_left, conditional.tsum_coe, mul_one]
  have present : true ∈ (law.map observed).support := by
    apply (PMF.mem_support_iff _ _).mpr
    rwa [normalizer]
  refine ⟨present, ?_⟩
  ext point
  rw [fiberPosterior_apply law observed true present, normalizer]
  have indicator : {point | observed point = true}.indicator law point =
      if observed point then law point else 0 := by
    cases selected : observed point <;> simp [Set.indicator, selected]
  rw [indicator, restriction, mul_right_comm mass (conditional point),
    ENNReal.mul_inv_cancel positive finite, one_mul]

open Classical in
/-- The same unnormalized owner-word atoms give both the all-ledger and
own-ledger posteriors. The foreign cylinder stays inside its original law. -/
private theorem pair_posteriors_of_word_atoms
    {Point Word : Type*} (law : PMF Point) (words : PMF Word)
    (read : Point → Word) (own : Point → Bool) (admitted : Word → Bool)
    (forced : Word → PMF Point) (ownMass : ℝ≥0∞)
    (ownPositive : ownMass ≠ 0) (ownFinite : ownMass ≠ ⊤)
    (foreignPositive : true ∈ (words.map admitted).support)
    (atoms : ∀ word point,
      ownMass * words word * forced word point =
        if own point = true ∧ read point = word then law point else 0) :
    let foreign := words.map (fun word => (word, admitted word))
    true ∈ (law.map (fun point => own point && admitted (read point))).support ∧
      true ∈ (foreign.map Prod.snd).support ∧
      fiberPosterior law (fun point => own point && admitted (read point)) true =
        (fiberPosterior foreign Prod.snd true).bind (fun word => forced word.1) ∧
      true ∈ (law.map own).support ∧
      fiberPosterior law own true = words.bind forced := by
  classical
  intro foreign
  let foreignMass := (words.map admitted) true
  have foreignNonzero : foreignMass ≠ 0 :=
    (PMF.mem_support_iff _ _).mp foreignPositive
  have foreignFinite : foreignMass ≠ ⊤ := PMF.apply_ne_top _ _
  have ownRestriction (point : Point) :
      (if own point then law point else 0) = ownMass * (words.bind forced) point := by
    rw [PMF.bind_apply, ← ENNReal.tsum_mul_left]
    symm
    calc
      (∑' word, ownMass * (words word * forced word point)) =
          ∑' word, if own point = true ∧ read point = word then law point else 0 := by
        apply tsum_congr
        intro word
        exact (mul_assoc ownMass (words word) (forced word point)).symm.trans (atoms word point)
      _ = if own point then law point else 0 := by
        rw [tsum_eq_single (read point)]
        · cases own point <;> simp
        · intro word different
          have distinct : read point ≠ word := Ne.symm different
          simp [distinct]
  have ownPosterior := posterior_of_scaled_restriction law (words.bind forced) own ownMass
    ownPositive ownFinite ownRestriction
  have conditionalForeign : (fiberPosterior foreign Prod.snd true).bind
      (fun word => forced word.1) = (fiberPosterior words admitted true).bind forced := by
    have mapped := map_fiberPosterior_readout words (fun word => (word, admitted word))
      Prod.snd true foreignPositive
    change (fiberPosterior words admitted true).map (fun word => (word, admitted word)) =
      fiberPosterior foreign Prod.snd true at mapped
    rw [← mapped, PMF.bind_map]
    simp only [Function.comp_def]
  have foreignRestriction (point : Point) :
      foreignMass * ((fiberPosterior words admitted true).bind forced) point =
        ∑' word, if admitted word then words word * forced word point else 0 := by
    rw [PMF.bind_apply, ← ENNReal.tsum_mul_left]
    apply tsum_congr
    intro word
    rw [← mul_assoc]
    change (words.map admitted) true * fiberPosterior words admitted true word *
      forced word point = _
    rw [fiberPosterior_disintegrate words admitted true foreignPositive]
    cases selected : admitted word <;> simp [Set.indicator, selected]
  have ledgerRestriction (point : Point) :
      (if own point && admitted (read point) then law point else 0) =
        (ownMass * foreignMass) *
          ((fiberPosterior words admitted true).bind forced) point := by
    rw [mul_assoc, foreignRestriction, ← ENNReal.tsum_mul_left]
    symm
    calc
      (∑' word, ownMass * (if admitted word then words word * forced word point else 0)) =
          ∑' word, if admitted word then
            if own point = true ∧ read point = word then law point else 0 else 0 := by
        apply tsum_congr
        intro word
        cases selected : admitted word with
        | false => exact mul_zero ownMass
        | true =>
          exact (mul_assoc ownMass (words word) (forced word point)).symm.trans (atoms word point)
      _ = if own point && admitted (read point) then law point else 0 := by
        rw [tsum_eq_single (read point)]
        · cases own point <;> cases admitted (read point) <;> simp
        · intro word different
          have distinct : read point ≠ word := Ne.symm different
          simp [distinct]
  have ledgerPosterior := posterior_of_scaled_restriction law
    ((fiberPosterior words admitted true).bind forced)
    (fun point => own point && admitted (read point)) (ownMass * foreignMass)
    (mul_ne_zero ownPositive foreignNonzero) (ENNReal.mul_ne_top ownFinite foreignFinite)
    ledgerRestriction
  refine ⟨ledgerPosterior.1, ?_, ledgerPosterior.2.trans conditionalForeign.symm,
    ownPosterior.1, ownPosterior.2⟩
  simpa only [foreign, PMF.map_comp, Function.comp_def] using foreignPositive

private theorem owner_and_foreign_word_law
    {Point Owned : Type*} (law : PMF Point) (read : Point → Player → Owned)
    (who : Player) (empty : Owned) (own : Owned → Bool)
    (product : law.map read = independentProduct
      (fun owner => law.map (fun point => read point owner))) :
    let foreign := fun point : Point => fun owner =>
      if owner = who then empty else read point owner
    law.map (fun point => (own (read point who), foreign point)) =
      bindPairLaw (law.map (fun point => own (read point who)))
        (fun _ => law.map foreign) := by
  classical
  intro foreign
  let factors := fun owner => law.map (fun point => read point owner)
  let others := independentProduct (fun owner : {owner : Player // owner ≠ who} =>
    factors owner.val)
  let restore := fun word : (∀ owner : {owner : Player // owner ≠ who}, Owned) =>
    fun owner => if different : owner = who then empty else word ⟨owner, different⟩
  have split : law.map (fun point =>
      (read point who, fun owner : {owner : Player // owner ≠ who} => read point owner.val)) =
        bindPairLaw (factors who) (fun _ => others) := by
    have mapped := congrArg (fun measure => measure.map
      (Equiv.piSplitAt who (fun _ : Player => Owned))) product
    rw [independentProduct_splitAt _ who] at mapped
    simpa only [PMF.map_comp, PMF.map_bind, Function.comp_def, Equiv.apply_symm_apply,
      Equiv.piSplitAt_apply, factors, others, bindPairLaw] using mapped
  have foreignLaw : law.map foreign = others.map restore := by
    have marginal := congrArg (fun measure => measure.map (fun pair => restore pair.2)) split
    simpa [PMF.map_comp, bindPairLaw, PMF.map_bind, PMF.bind_const,
      Function.comp_def, restore, foreign] using marginal
  have mapped := congrArg (fun measure => measure.map
    (fun pair => (own pair.1, restore pair.2))) split
  simp only [bindPairLaw, PMF.map_bind, PMF.map_comp, Function.comp_def] at mapped
  rw [foreignLaw]
  simpa [PMF.bind_map, PMF.map_comp, PMF.map_bind, bindPairLaw,
    Function.comp_def, factors, foreign, restore] using mapped

/-- Conditioning a whole source word at one focal observation leaves the
original foreign-word distribution as its mixture coefficient. Both restricted
masses include the same positive focal factor. -/
private theorem pair_posteriors_of_word_conditionals
    {Point Word : Type*} (law : PMF Point) (words : PMF Word) (ownLaw : PMF Bool)
    (read : Point → Word) (own : Point → Bool) (admitted : Word → Bool)
    (forced : Word → PMF Point)
    (ownPositive : true ∈ ownLaw.support)
    (foreignPositive : true ∈ (words.map admitted).support)
    (joint : law.map (fun point => (own point, read point)) =
      bindPairLaw ownLaw (fun _ => words))
    (conditional : ∀ word ∈ words.support,
      forced word = fiberPosterior law (fun point => (own point, read point)) (true, word)) :
    let foreign := words.map (fun word => (word, admitted word))
    true ∈ (law.map (fun point => own point && admitted (read point))).support ∧
      true ∈ (foreign.map Prod.snd).support ∧
      fiberPosterior law (fun point => own point && admitted (read point)) true =
        (fiberPosterior foreign Prod.snd true).bind (fun word => forced word.1) ∧
      true ∈ (law.map own).support ∧
      fiberPosterior law own true = words.bind forced := by
  classical
  apply pair_posteriors_of_word_atoms law words read own admitted forced (ownLaw true)
    ((PMF.mem_support_iff _ _).mp ownPositive) (PMF.apply_ne_top _ _) foreignPositive
  intro word point
  by_cases supported : word ∈ words.support
  · have present : (true, word) ∈
        (law.map (fun point => (own point, read point))).support := by
      rw [joint, PMF.mem_support_iff, bindPairLaw_apply]
      exact mul_ne_zero ((PMF.mem_support_iff _ _).mp ownPositive)
        ((PMF.mem_support_iff _ _).mp supported)
    have mass : (law.map (fun point => (own point, read point))) (true, word) =
        ownLaw true * words word := by rw [joint, bindPairLaw_apply]
    rw [conditional word supported, ← mass]
    have disintegrated := fiberPosterior_disintegrate law
      (fun point => (own point, read point)) (true, word) present point
    simpa only [Set.indicator, Set.mem_ofPred_eq, Prod.mk.injEq] using disintegrated
  · have zero := (PMF.apply_eq_zero_iff _ _).mpr supported
    rw [zero, mul_zero, zero_mul]
    by_cases selected : own point = true ∧ read point = word
    · have lawZero : law point = 0 := by
        apply (PMF.apply_eq_zero_iff _ _).mpr
        intro member
        have mapped : (true, word) ∈
            (law.map (fun point => (own point, read point))).support :=
          (PMF.mem_support_map_iff ..).mpr ⟨point, member, Prod.ext selected.1 selected.2⟩
        rw [joint, PMF.mem_support_iff, bindPairLaw_apply, zero, mul_zero] at mapped
        exact mapped rfl
      simp [selected, lawZero]
    · simp only [selected, ite_false]

open Classical in
/-- The actual ordinary source cut and completion under the issued ledger,
and under the focal ledger alone, use the same original foreign-word kernel. -/
def ForeignPosteriorCutPair : Prop :=
  ∀ (operational : implementation.Operational)
    (_fullValues : ∀ owner key, FullSupport (values owner key))
    (sourceProfile : ∀ owner, setup.proposalRecoveryModel.BehavioralPolicy owner)
    (nativeProfile : ∀ owner,
      ((nativeMenu).information nativeInitial implementation.horizon
        implementation.scheduler).BehavioralPolicy owner)
    (who : Player) (control : (nativeApplication).Control)
    (trace : (nativeProtocol).Trace (some control))
    (tape : ReservedEpoch.Tape Player implementation.tapeLength)
    (target : setup.proposalRecoveryProtocol.History)
    (supportedWord : SourceProgram.History Player L)
    (_canonicalSupported : setup.proposalRecoveryModel.historyReachWeight sourceProfile
      (canonicalSource setup implementation operational ⟨some control, trace⟩) ≠ 0)
    (_positive : annotatedPrefixWeight setup values implementation operational sourceProfile
      nativeProfile who ⟨some control, trace⟩ tape target supportedWord ≠ 0)
    (past : List (nativeApplication).PlayerEntry) (view : (nativeApplication).PlayerView)
    (_information : ((nativeMenu).information nativeInitial implementation.horizon
      implementation.scheduler).infoOf who trace = some (past, view))
    (event : (serviceGraph setup .concurrent).EventId) (payload : L.Ty)
    (cleanSite : CleanUnsentBinding setup implementation who past view event payload)
    (_admitted : bindingAdmissionBit setup implementation who event
      ⟨some control, trace⟩ tape = true)
    (value : L.Val payload),
    let checkpoint := (checkpointSelection setup implementation operational trace).val.checkpoint
    let block := SourceProgram.commitPhase checkpoint.residual.tail
    let low := control.execution.application.attempt.phase
    let high := low + block.block.length
    let k := event.val - low
    let q0 := sourceUnflaggedStrategy setup values
    let pair := (setup.proposalRecoveryModel.runBehavioralFrom q0 k target).bind fun cut =>
      (setup.proposalRecoveryModel.runBehavioralFrom q0 (block.block.length - k) cut).map
        (Prod.mk cut)
    let completed := fun history : setup.proposalRecoveryProtocol.History =>
      history.state.bind fun current => residualEntry? block.suffix
        (fun point => checkpoint.residual.lift
          (cast (congrArg ProtocolState block.reconstruct)
            (block.block.liftPoint block.suffix point))) current.point
    let observed := fun pair : setup.proposalRecoveryProtocol.History ×
        setup.proposalRecoveryProtocol.History =>
      match completed pair.2 with
      | none => false
      | some finished => decide (
          issuedLedger setup implementation block.block low control high who
            (finished.view who) ∧
          block.block.wordAction who k (finished.view who) =
            decodeEventAction setup.program event
              (cast (congrArg EventField.Action cleanSite.binding.symm)
                (PublicationResult.success value)) ∧
          ∀ owner, owner ≠ who → issuedLedger setup implementation block.block low
            control high owner (finished.view owner))
    let foreign := ordinaryForeignJoint setup values implementation operational who
      ⟨some control, trace⟩ target
    let ownObserved := fun pair : setup.proposalRecoveryProtocol.History ×
        setup.proposalRecoveryProtocol.History =>
      match completed pair.2 with
      | none => false
      | some finished => decide (
          issuedLedger setup implementation block.block low control high who
            (finished.view who) ∧
          block.block.wordAction who k (finished.view who) =
            decodeEventAction setup.program event
              (cast (congrArg EventField.Action cleanSite.binding.symm)
                (PublicationResult.success value)))
    true ∈ (pair.map observed).support ∧
      true ∈ (foreign.map Prod.snd).support ∧
      (fiberPosterior pair observed true =
        (fiberPosterior foreign Prod.snd true).bind fun word =>
          sourceForcedBlockJoint setup values implementation who ⟨some control, trace⟩
            event payload target word.1 value) ∧
      true ∈ (pair.map ownObserved).support ∧
      fiberPosterior pair ownObserved true =
        (foreign.map Prod.fst).bind fun word =>
          sourceForcedBlockJoint setup values implementation who ⟨some control, trace⟩
            event payload target word value

omit [Fintype Player] [L.ResultTypes] in
private theorem structural_owned_history_of_joints
    {Γ Δ : SourceCtx Player L} {O P : Finset VarId}
    (block : SourceProgram.CommitPrefix Γ O Δ P) (who : Player)
    (first second : SourceProgram.Config Player L Γ) (excluded : Finset Player)
    (leftFinal rightFinal : SourceProgram.Config Player L Δ)
    (left : block.Attempt first excluded leftFinal excluded)
    (right : block.Attempt second excluded rightFinal excluded)
    (entryHistory : first.history who = second.history who)
    (same : left.joints.map (fun joint => joint who) =
      right.joints.map (fun joint => joint who)) :
    (left.withoutMisses ∅ first).history who =
      (right.withoutMisses ∅ second).history who := by
  have replay : ∀ {Α Β : SourceCtx Player L} {R S : Finset VarId}
      (segment : SourceProgram.CommitPrefix Α R Β S)
      (sourceFirst sourceSecond replacementFirst replacementSecond :
        SourceProgram.Config Player L Α) (saved : Finset Player)
      (finalFirst finalSecond : SourceProgram.Config Player L Β)
      (attemptFirst : segment.Attempt sourceFirst saved finalFirst saved)
      (attemptSecond : segment.Attempt sourceSecond saved finalSecond saved),
      replacementFirst.history who = replacementSecond.history who →
      attemptFirst.joints.map (fun joint => joint who) =
        attemptSecond.joints.map (fun joint => joint who) →
      (attemptFirst.withoutMisses ∅ replacementFirst).history who =
        (attemptSecond.withoutMisses ∅ replacementSecond).history who := by
    intro Α Β R S segment
    induction segment with
    | nil =>
      intro sourceFirst sourceSecond replacementFirst replacementSecond saved finalFirst
        finalSecond attemptFirst attemptSecond sameHistory _
      cases attemptFirst
      cases attemptSecond
      exact sameHistory
    | @commit Α R Β S name actor payload fresh guard rest ih =>
      intro sourceFirst sourceSecond replacementFirst replacementSecond saved finalFirst
        finalSecond attemptFirst attemptSecond sameHistory sameJoints
      cases attemptFirst with
      | active active result missed valid later =>
        have noMiss : missed = false := by
          cases missed with
          | false => rfl
          | true =>
            have added : actor ∈ excludeCommit saved actor true := by
              simp only [excludeCommit, ↓reduceIte, Finset.mem_insert, true_or]
            exact (active (later.excluded_subset added)).elim
        subst missed
        cases attemptSecond with
        | excluded inactive other => exact (active inactive).elim
        | active otherActive otherResult otherMissed otherValid other =>
          have noOtherMiss : otherMissed = false := by
            cases otherMissed with
            | false => rfl
            | true =>
              have added : actor ∈ excludeCommit saved actor true := by
                simp only [excludeCommit, ↓reduceIte, Finset.mem_insert, true_or]
              exact (otherActive (other.excluded_subset added)).elim
          subst otherMissed
          have heads := (List.cons.inj sameJoints).1
          have tails := (List.cons.inj sameJoints).2
          apply ih _ _ _ _ saved _ _ later other ?_ tails
          by_cases own : who = actor
          · subst who
            have resultEq : result = otherResult := by
              simpa only [SourceProgram.CommitPrefix.Attempt.joints, ↓reduceIte,
                Option.some.injEq, CommitRecoveryMove.mk.injEq, OwnAction.commit.injEq,
                heq_eq_eq, true_and, and_true] using heads
            simp only [commitSuccessor, Function.update_self, resultEq, sameHistory]
          · simpa only [commitSuccessor, Function.update_of_ne own] using sameHistory
      | excluded inactive later =>
        cases attemptSecond with
        | active active result missed valid other => exact (active inactive).elim
        | excluded otherInactive other =>
          have tails := (List.cons.inj sameJoints).2
          simp only [SourceProgram.CommitPrefix.Attempt.withoutMisses,
            Finset.notMem_empty, ↓reduceIte]
          apply ih _ _ _ _ saved _ _ later other ?_ tails
          by_cases own : who = actor
          · subst who
            simp only [commitSuccessor, Function.update_self, sameHistory]
          · simpa only [commitSuccessor, Function.update_of_ne own] using sameHistory
  exact replay block first second first second excluded leftFinal rightFinal left right
    entryHistory same

omit [Fintype Player] [L.ResultTypes] in
private theorem word_action_name_in_context
    {Γ Δ : SourceCtx Player L} {O P : Finset VarId}
    (block : SourceProgram.CommitPrefix Γ O Δ P) (who : Player) (position : Nat)
    (view : DecisionView who Δ) (owner : Player) (name : VarId) (payload : L.Ty)
    (result : PublicationResult (L.Val payload))
    (read : block.wordAction who position view = some (.commit owner name payload result)) :
    name ∈ Δ.map Prod.fst := by
  induction block generalizing position with
  | nil => cases read
  | @commit Γ O Δ P head actor domain fresh guard rest ih =>
    cases position with
    | zero =>
      simp only [SourceProgram.CommitPrefix.wordAction] at read
      split at read
      · have names : head = name := congrArg (fun action : OwnAction Player L =>
          match action with
          | .commit _ named _ _ => named
          | .reveal _ named _ => named) (Option.some.inj read)
        subst name
        have included : ((head, .commitment actor domain) :: Γ).map Prod.fst ⊆
            Δ.map Prod.fst := by
          let rec namesMono : ∀ {Θ : SourceCtx Player L} {R : Finset VarId}
              (segment : SourceProgram.CommitPrefix Θ R Δ P),
              Θ.map Prod.fst ⊆ Δ.map Prod.fst
            | _, _, .nil => fun _ member => member
            | _, _, .commit _ _ _ _ rest =>
              fun _ member => namesMono rest (List.mem_cons_of_mem _ member)
          exact namesMono rest
        exact included (List.mem_cons_self ..)
      · cases read
    | succ position => exact ih position view read

/-- The actual ordinary source continuation has both binding posterior laws. -/
theorem foreign_posterior_cut_pair :
    ForeignPosteriorCutPair setup values implementation := by
  classical
  intro operational fullValues sourceProfile nativeProfile who control trace tape target
    supportedWord canonicalSupported positive past view information event payload cleanSite
    admitted value checkpoint block low high k q0 pair completed observed foreign ownObserved
  have active : control.actor = some who := by
    by_contra inactive
    have observedInfo := (nativeMenu).info nativeInitial implementation.horizon
      implementation.scheduler who trace
    simp only [ReactiveApplication.observe, inactive, ↓reduceIte] at observedInfo
    change ((nativeMenu).signals nativeInitial implementation.horizon
      implementation.scheduler).infoOf who trace = some (past, view) at information
    rw [observedInfo] at information
    cases information
  have actualInfo : ((nativeMenu).information nativeInitial implementation.horizon
      implementation.scheduler).infoOf who trace =
        some (control.execution.recall who, control.execution.observe nativeApplication who) := by
    change ((nativeMenu).signals nativeInitial implementation.horizon
      implementation.scheduler).infoOf who trace = _
    have observedInfo := (nativeMenu).info nativeInitial implementation.horizon
      implementation.scheduler who trace
    simpa only [ReactiveApplication.observe, active, ↓reduceIte] using observedInfo
  have actualViews := Option.some.inj (actualInfo.symm.trans information)
  have cleanSiteProof : CleanUnsentBinding setup implementation who (control.execution.recall who)
      (control.execution.observe nativeApplication who) event payload := by
    obtain ⟨pastEq, viewEq⟩ := Prod.mk.inj actualViews
    rw [pastEq, viewEq]
    exact cleanSite
  have nativeForeign : ∀ owner, owner ≠ who →
      ¬ PhaseProposal.GeneratedUnusableBindingHistory implementation.runtime
        implementation.leaks implementation.bounds nativeInitial implementation.horizon
          implementation.scheduler owner ⟨some control, trace⟩ := by
    unfold annotatedPrefixWeight at positive
    dsimp only at positive
    have qualified := (mul_ne_zero_iff.mp positive).2
    split at qualified
    · rename_i good
      exact good.1
    · simp only [ne_eq, not_true_eq_false] at qualified
  obtain ⟨entry, current, targetTrace, targetEq, _targetGood, erased⟩ :=
    annotated_entry_erased_history setup values implementation operational sourceProfile
      nativeProfile who control trace tape target supportedWord canonicalSupported positive
        event payload cleanSiteProof
  subst target
  have saved := cleanSiteProof.excluded_eq setup implementation control
    (checkpointSelection setup implementation operational trace).val entry.phase entry.installed
  have request : control.execution.application.SeedRequest who
      ⟨control.execution.application.attempt, event⟩ := by
    have initialEq : (setup.initialLaw.map encodeInputs).map
        (PhaseRuntimeState.initial implementation.plan) = nativeInitial := PMF.map_comp _ _ _
    have raw := (nativeMenu).toRawTrace nativeInitial implementation.horizon
      implementation.scheduler trace
    rw [← initialEq] at raw
    obtain ⟨_draw, invariant⟩ := phaseNativeInvariant_history implementation.runtime
      implementation.leaks implementation.plan (setup.initialLaw.map encodeInputs)
        implementation.horizon implementation.scheduler raw
    exact (control.execution.application.requests_publicView invariant who _).mp
      cleanSiteProof.request
  have alive : who ∉ control.execution.application.entry.excluded := by
    rw [← saved]
    exact request.2.2.2.2
  obtain ⟨baseCursor, canonical, offset, _source, _refs, embedding, lift, views,
      _config, size⟩ :=
    selected_binding_cursor setup implementation operational who control trace event
      entry true
  let cursor := PhaseProposalOrdinarySourceCursor.of_erasedHistory setup .concurrent
    implementation.runtime implementation.leaks implementation.plan control entry.phase
      block.block block.suffix baseCursor current targetTrace
        ((congrArg setup.proposalRecoveryErasedHistory canonical).trans
          ((congrArg setup.proposalRecoveryErasedHistory entry.canonicalHistory).symm.trans erased))
  have cursorCurrent : cursor.current = current := rfl
  have cursorTrace : cursor.trace = targetTrace := rfl
  have cursorStart : (⟨some cursor.current, cursor.trace⟩ :
      setup.proposalRecoveryProtocol.History) = ⟨some current, targetTrace⟩ := rfl
  have cursorExcluded : current.excluded = control.execution.application.entry.excluded :=
    cursor.excluded.trans saved
  have phaseLow : entry.phase.low = low := by
    obtain ⟨rest, phases⟩ := List.head?_eq_some_iff.mp entry.installed
    simp only [low, PhaseRuntimeState.attempt, phases, List.head?_cons,
      Option.map_some, Option.getD_some]
  have phaseHigh : entry.phase.high = high := by
    have nonempty := entry.phase.nonempty
    have blockSize := size
    change block.block.length = entry.phase.high - entry.phase.low at blockSize
    have lowEq := phaseLow
    dsimp only [high]
    omega
  have inside : k < block.block.length := by
    have bounds := (entry.phase.mem_events event).mp entry.inside
    dsimp only [k]
    omega
  have blockPositive : 0 < block.block.length := by omega
  have rank : ∀ index, (cursor.embedding.event index).val = low + index.val := by
    intro index
    simpa only [cursor, PhaseProposalOrdinarySourceCursor.of_erasedHistory, offset] using
      baseCursor.compiled.rankEq index
  have footprint :
      (control.execution.application.publicView.retired.map fun record =>
        record.2.sourceFailureFootprint.2).foldr (fun first last => first ∪ last) ∅ ∪
          control.execution.application.current.native.publicView.sourceFailureFootprint.1
            control.execution.application.attempt.phase =
        control.execution.application.entry.excluded := by
    have controls := congrArg Prod.fst (cursor.controls blockPositive)
    exact controls.symm.trans cursorExcluded
  let profile := ordinaryBlockProfile setup .concurrent implementation.plan values block.block
    block.suffix cursor.embedding (fun owner view => cursor.views.view owner view)
      (control.execution.application.entry.excluded, control.execution.application.generation, low)
        control.execution.application.publicView
          (PhaseProposal.sourceArchive control.execution.network.inputs)
  let ordinary := setup.proposalRecoveryModel.runBehavioralFrom q0 block.block.length
    ⟨some current, targetTrace⟩
  let structural := block.block.prefixLaw block.suffix profile cursor.source
  obtain ⟨reconstruct, projected, related⟩ :=
    ordinary_source_structural_projection setup values implementation control trace entry.phase
      block.block block.suffix cursor
  have project : ordinary.map reconstruct = structural := by
    rw [cursorStart] at projected
    rw [footprint] at projected
    have generationEq : control.execution.application.attempt.generation =
        control.execution.application.generation := rfl
    simpa only [ordinary, q0, profile, structural, generationEq, low] using projected
  have pairComplete : pair.map Prod.snd = ordinary := by
    simp only [pair, PMF.map_bind, PMF.map_comp, Function.comp_def]
    simp only [show (fun x : setup.proposalRecoveryProtocol.History => x) = id from rfl,
      PMF.map_id]
    rw [← setup.proposalRecoveryModel.runBehavioralFrom_add, Nat.add_sub_of_le inside.le]
  let ownTest := fun final : SourceProgram.Config Player L block.context => decide (
    issuedLedger setup implementation block.block low control high who (final.view who) ∧
      block.block.wordAction who k (final.view who) =
        decodeEventAction setup.program event
          (cast (congrArg EventField.Action cleanSiteProof.binding.symm) (.success value)))
  let foreignTest := fun final : SourceProgram.Config Player L block.context =>
    decide (∀ owner, owner ≠ who → issuedLedger setup implementation block.block low
      control high owner (final.view owner))
  let ownGate := fun word : List (OwnAction Player L) => decide (∃ final ∈ structural.support,
    final.history who = word ∧ ownTest final = true)
  let foreignRead := fun final : SourceProgram.Config Player L block.context =>
    fun owner => if owner = who then [] else final.history owner
  let foreignGate := fun word : SourceProgram.History Player L =>
    decide (∃ final ∈ structural.support, foreignRead final = word ∧ foreignTest final = true)
  let read := fun history : setup.proposalRecoveryProtocol.History =>
    foreignRead (reconstruct history)
  let own := fun history : setup.proposalRecoveryProtocol.History =>
    ownGate ((reconstruct history).history who)
  let words := ordinary.map read
  let ownLaw := ordinary.map own
  have ownGateEq (final : SourceProgram.Config Player L block.context)
      (member : final ∈ structural.support) : ownGate (final.history who) = ownTest final := by
    apply Bool.eq_iff_iff.mpr
    simp only [ownGate, decide_eq_true_eq]
    constructor
    · rintro ⟨other, supported, same, good⟩
      have viewEq := block.block.prefixLaw_view_eq_of_history_eq block.suffix profile profile
        cursor.source cursor.source who rfl other final supported member same
      simpa only [ownTest, viewEq] using good
    · exact fun good => ⟨final, member, rfl, good⟩
  have foreignGateEq (final : SourceProgram.Config Player L block.context)
      (member : final ∈ structural.support) :
      foreignGate (foreignRead final) = foreignTest final := by
    apply Bool.eq_iff_iff.mpr
    simp only [foreignGate, decide_eq_true_eq]
    constructor
    · rintro ⟨other, supported, same, good⟩
      simp only [foreignTest, decide_eq_true_eq] at good ⊢
      intro owner different
      have historyEq : other.history owner = final.history owner := by
        simpa only [foreignRead, ite_eq_right different] using congrFun same owner
      have viewEq := block.block.prefixLaw_view_eq_of_history_eq block.suffix profile profile
        cursor.source cursor.source owner rfl other final supported member historyEq
      rw [← viewEq]
      exact good owner different
    · exact fun good => ⟨final, member, rfl, good⟩
  have reconstructedSupport (history : setup.proposalRecoveryProtocol.History)
      (member : history ∈ ordinary.support) : reconstruct history ∈ structural.support := by
    rw [← project]
    exact (PMF.mem_support_map_iff ..).mpr ⟨history, member, rfl⟩
  have actualTests (history : setup.proposalRecoveryProtocol.History)
      (member : history ∈ ordinary.support) :
      (match completed history with
      | none => false
      | some final => ownTest final) = own history ∧
      (match completed history with
      | none => false
      | some final => foreignTest final) = foreignGate (read history) := by
    obtain ⟨final, last, lastTrace, attempt, historyEq, _replay, point, excluded,
      _word, _labels, activeViews, _proper⟩ := related history member
    have pulled : completed history = some final := by
      rw [historyEq]
      change residualEntry? block.suffix
        (fun point => checkpoint.residual.lift
          (cast (congrArg ProtocolState block.reconstruct)
            (block.block.liftPoint block.suffix point))) last.point = some final
      have exactLift : (fun point => checkpoint.residual.lift
          (cast (congrArg ProtocolState block.reconstruct)
            (block.block.liftPoint block.suffix point))) =
          (fun point => cursor.lift (block.block.liftPoint block.suffix point)) := by
        funext point
        exact (lift _).symm
      rw [exactLift]
      exact (residualEntry?_eq_some_iff
        (cursor.origin.compose (block.block.protocolSuffix block.suffix)) _ _).mpr point.symm
    have ledgerEq (owner : Player) :
        issuedLedger setup implementation block.block low control high owner (final.view owner) ↔
          issuedLedger setup implementation block.block low control high owner
            ((reconstruct history).view owner) := by
      by_cases inactive : owner ∈ control.execution.application.entry.excluded
      · have vacuous (word : DecisionView owner block.context) :
            issuedLedger setup implementation block.block low control high owner word := by
          intro named domain shape candidate message emitted attemptMatch call interval
          have inputRecall := (nativeApplication).history_inputRecall nativeInitial
            implementation.horizon implementation.scheduler
              ((nativeMenu).toRawTrace nativeInitial implementation.horizon
                implementation.scheduler trace) owner
          have input : message ∈ control.execution.network.inputs := by
            rw [← inputRecall] at emitted
            exact (List.mem_filter.mp emitted).1
          exact (issued_binding_owner_active setup implementation control trace owner named
            domain shape candidate message input attemptMatch call inactive).elim
        exact iff_of_true (vacuous _) (vacuous _)
      · rw [activeViews owner (by rw [excluded, cursorCurrent, cursorExcluded]; exact inactive)]
    have ownView : final.view who = (reconstruct history).view who :=
      activeViews who (by rw [excluded, cursorCurrent, cursorExcluded]; exact alive)
    dsimp only [own, read]
    rw [pulled, ownGateEq _ (reconstructedSupport history member),
      foreignGateEq _ (reconstructedSupport history member)]
    constructor
    · exact decide_eq_decide.mpr (and_congr (ledgerEq who) (by rw [ownView]))
    · exact decide_eq_decide.mpr (forall_congr' fun owner =>
        imp_congr_right fun _ => ledgerEq owner)
  have pairOwn (point : setup.proposalRecoveryProtocol.History ×
      setup.proposalRecoveryProtocol.History) (member : point ∈ pair.support) :
      ownObserved point = own point.2 := by
    have reached : point.2 ∈ ordinary.support := by
      rw [← pairComplete]
      exact (PMF.mem_support_map_iff ..).mpr ⟨point, member, rfl⟩
    exact (actualTests point.2 reached).1
  have pairObserved (point : setup.proposalRecoveryProtocol.History ×
      setup.proposalRecoveryProtocol.History) (member : point ∈ pair.support) :
      observed point = (own point.2 && foreignGate (read point.2)) := by
    have reached : point.2 ∈ ordinary.support := by
      rw [← pairComplete]
      exact (PMF.mem_support_map_iff ..).mpr ⟨point, member, rfl⟩
    have tests := actualTests point.2 reached
    calc
      observed point = (match completed point.2 with
          | none => false
          | some final => ownTest final && foreignTest final) := by
        dsimp only [observed]
        split
        · rfl
        · rename_i final
          apply Bool.eq_iff_iff.mpr
          simp only [ownTest, foreignTest, Bool.and_eq_true, decide_eq_true_eq,
            and_assoc]
      _ = (own point.2 && foreignGate (read point.2)) := by
        rw [← tests.1, ← tests.2]
        cases completion : completed point.2 <;> rfl
  have foreignEq : foreign = words.map (fun word => (word, foreignGate word)) := by
    have selected := ordinaryForeignJoint_of_selected_cursor setup values implementation
      operational who control trace entry.phase cursor blockPositive embedding lift views
    rw [cursorStart] at selected
    have selected' : foreign = structural.map (fun final =>
        (foreignRead final, foreignTest final)) := by
      simpa only [foreign, structural, profile, foreignRead, foreignTest,
        low, high] using selected
    rw [selected']
    rw [← project, PMF.map_comp]
    change ordinary.map (fun history => (read history, foreignTest (reconstruct history))) = _
    rw [show words.map (fun word => (word, foreignGate word)) =
        ordinary.map (fun history => (read history, foreignGate (read history))) by
      simp only [words, PMF.map_comp, Function.comp_def]]
    exact map_congr_on_support ordinary (fun history member =>
      Prod.ext rfl (foreignGateEq _ (reconstructedSupport history member)).symm)
  have product : ordinary.map (fun history => (reconstruct history).history) =
      independentProduct (fun owner => ordinary.map
        (fun history => (reconstruct history).history owner)) := by
    have all := block.block.prefixLaw_histories_product block.suffix profile cursor.source
    calc
      ordinary.map (fun history => (reconstruct history).history) =
          (ordinary.map reconstruct).map (fun final => final.history) := by
            rw [PMF.map_comp]
            rfl
      _ = structural.map (fun final => final.history) := by rw [project]
      _ = independentProduct (fun owner => structural.map (fun final => final.history owner)) := all
      _ = independentProduct (fun owner => ordinary.map
          (fun history => (reconstruct history).history owner)) := by
            congr 1
            funext owner
            rw [← project, PMF.map_comp]
            rfl
  have independent : ordinary.map (fun history => (own history, read history)) =
      bindPairLaw ownLaw (fun _ => words) :=
    owner_and_foreign_word_law ordinary (fun history => (reconstruct history).history)
      who [] ownGate product
  obtain ⟨_ready, graphPresent, _graphLaw⟩ :=
    binding_value_frontier_posterior setup values implementation operational fullValues
      control trace who active event payload cleanSiteProof nativeForeign entry value
  obtain ⟨sourcePresent, _wordLaw, _supported⟩ := closed_entry_binding_word setup values
    implementation operational control trace who event payload cleanSiteProof.binding alive entry
      value
      current targetTrace erased graphPresent
  have lengthEq := (selected_binding_observation setup implementation operational
    control trace who event payload cleanSiteProof.binding entry value).1
  have present : true ∈ (ordinary.map (bindingCompletedObservation setup implementation checkpoint
      control who event payload cleanSiteProof.binding value)).support := by
    simpa only [ordinary, q0, ← lengthEq] using sourcePresent
  obtain ⟨positiveHistory, positiveMember, positiveObservation⟩ :=
    (PMF.mem_support_map_iff ..).mp present
  have positiveOwn : own positiveHistory = true := by
    have tests := (actualTests positiveHistory positiveMember).1
    unfold bindingCompletedObservation residualBindingObservation at positiveObservation
    cases parsed : positiveHistory.state.bind (fun current => residualEntry? block.suffix
        (fun point => checkpoint.residual.lift
          (cast (congrArg ProtocolState block.reconstruct)
            (block.block.liftPoint block.suffix point))) current.point) with
    | none =>
      simp only [checkpoint, block, parsed] at positiveObservation
      cases positiveObservation
    | some final =>
      have good : (∀ owner, issuedLedger setup implementation block.block low control high
          owner (final.view owner)) ∧
            block.block.wordAction who k (final.view who) =
              decodeEventAction setup.program event
                (cast (congrArg EventField.Action cleanSiteProof.binding.symm)
                  (.success value)) := by
        simpa only [checkpoint, block, parsed, decide_eq_true_eq, low, high, k]
          using positiveObservation
      have completedFinal : completed positiveHistory = some final := by
        simpa only [completed] using parsed
      rw [completedFinal] at tests
      rw [← tests]
      exact decide_eq_true ⟨good.1 who, good.2⟩
  have ownPositive : true ∈ ownLaw.support :=
    (PMF.mem_support_map_iff ..).mpr ⟨positiveHistory, positiveMember, positiveOwn⟩
  have annotationSupport := annotatedPrefixWeight_support setup values implementation operational
    sourceProfile nativeProfile who ⟨some control, trace⟩ tape ⟨some current, targetTrace⟩
      supportedWord canonicalSupported positive
  have foreignPositive : true ∈ (words.map foreignGate).support := by
    have given : (supportedWord, true) ∈ foreign.support := annotationSupport.2.2
    have projected : true ∈ (foreign.map Prod.snd).support :=
      (PMF.mem_support_map_iff ..).mpr ⟨(supportedWord, true), given, rfl⟩
    simpa only [foreignEq, PMF.map_comp, Function.comp_def] using projected
  have pairJoint : pair.map (fun point => (own point.2, read point.2)) =
      bindPairLaw ownLaw (fun _ => words) := by
    have mapped := congrArg (fun law => law.map (fun history => (own history, read history)))
      pairComplete
    simpa only [PMF.map_comp, Function.comp_def, independent] using mapped
  have conditional : ∀ word ∈ words.support,
      sourceForcedBlockJoint setup values implementation who ⟨some control, trace⟩ event payload
        ⟨some current, targetTrace⟩ word value =
      fiberPosterior pair (fun point => (own point.2, read point.2)) (true, word) := by
    intro word wordSupported
    have jointPresent : (true, word) ∈
        (ordinary.map (fun history => (own history, read history))).support := by
      rw [independent, PMF.mem_support_iff, bindPairLaw_apply]
      exact mul_ne_zero ((PMF.mem_support_iff ..).mp ownPositive)
        ((PMF.mem_support_iff ..).mp wordSupported)
    obtain ⟨reference, referenceSupported, referenceObservation⟩ :=
      (PMF.mem_support_map_iff ..).mp jointPresent
    have referenceOwn := (Prod.mk.inj referenceObservation).1
    have referenceForeign := (Prod.mk.inj referenceObservation).2
    let final := reconstruct reference
    have finalSupported : final ∈ structural.support :=
      reconstructedSupport reference referenceSupported
    have referenceGood : ownTest final = true := by
      rw [← ownGateEq final finalSupported]
      exact referenceOwn
    have retained : issuedLedger setup implementation block.block low control high who
        (final.view who) := (decide_eq_true_eq.mp referenceGood).1
    have selected : block.block.wordAction who k (final.view who) =
        decodeEventAction setup.program event
          (cast (congrArg EventField.Action cleanSiteProof.binding.symm) (.success value)) :=
      (decide_eq_true_eq.mp referenceGood).2
    let completeWord : SourceProgram.History Player L := fun owner =>
      if owner ∈ current.excluded then [] else
        (List.range block.block.length).filterMap
          (fun position => block.block.wordAction owner position (final.view owner))
    let imposed : SourceProgram.History Player L := fun owner =>
      if owner ∈ current.excluded then [] else
        (List.range (if owner = who then k + 1 else block.block.length)).filterMap
          (fun position => block.block.wordAction owner position (final.view owner))
    let semantic := fun history : setup.proposalRecoveryProtocol.History =>
      ((setup.recoveryJointRecall (setup.proposalRecoveryEraseTrace history.trace)).take
        block.block.length).reverse
    have rows (history : setup.proposalRecoveryProtocol.History)
        (member : history ∈ ordinary.support) :
        semantic history = (List.range block.block.length).map (fun position owner =>
          if owner ∈ current.excluded then none else
            CommitRecoveryMove.lift
              (block.block.wordAction owner position ((reconstruct history).view owner))) := by
      obtain ⟨finished, last, lastTrace, attempt, historyEq, _replay, _point, excluded,
        recalledRows, _labels, activeViews, _proper⟩ := related history member
      have actual : semantic history = attempt.joints := by
        rw [historyEq]
        dsimp only [semantic]
        rw [recalledRows, ← attempt.joints_length, ← List.length_reverse, List.take_left,
          List.reverse_reverse]
      rw [actual, commitAttempt_wordAction block.block block.suffix cursor.source
        current.excluded finished last.excluded attempt excluded]
      apply List.map_congr_left
      intro position _member
      funext owner
      split
      · rfl
      · rename_i activeOwner
        rw [activeViews owner (by rw [excluded]; exact activeOwner)]
    have enrichedRows (history : setup.proposalRecoveryProtocol.History)
        (member : history ∈ ordinary.support) :
        ((setup.proposalRecoveryJointRecall history.trace).take block.block.length).reverse =
          (semantic history).map (fun row owner => (row owner).map
            ProposalRecoveryMove.ordinary) := by
      obtain ⟨finished, last, lastTrace, attempt, historyEq, _replay, _point, _excluded,
        recalledRows, labels, _activeViews, _proper⟩ := related history member
      have rawRows : semantic history = attempt.joints := by
        rw [historyEq]
        dsimp only [semantic]
        rw [recalledRows, ← attempt.joints_length, ← List.length_reverse,
          List.take_left, List.reverse_reverse]
      rw [rawRows]
      rw [historyEq, labels]
      rw [← attempt.joints_length]
      rw [← List.length_map (f := fun row owner => (row owner).map
        ProposalRecoveryMove.ordinary),
        ← List.length_reverse (as := attempt.joints.map (fun row owner =>
          (row owner).map ProposalRecoveryMove.ordinary)), List.map_reverse, List.take_left,
        List.reverse_reverse]
    have properRows (history : setup.proposalRecoveryProtocol.History)
        (member : history ∈ ordinary.support) : ∀ row ∈ semantic history,
        ∀ owner move, row owner = some move → move.missing = false ∧ ¬ move.action.IsFailure := by
      obtain ⟨finished, last, lastTrace, attempt, historyEq, _replay, _point, _excluded,
        recalledRows, _labels, _activeViews, proper⟩ := related history member
      have rawRows : semantic history = attempt.joints := by
        rw [historyEq]
        dsimp only [semantic]
        rw [recalledRows, ← attempt.joints_length, ← List.length_reverse,
          List.take_left, List.reverse_reverse]
      rw [rawRows]
      exact proper
    have readout (owner : Player) (action : OwnAction Player L)
        (member : action ∈ imposed owner) :
        ∃ position, block.block.wordAction owner position (final.view owner) = some action := by
      by_cases inactive : owner ∈ current.excluded
      · simp only [imposed, inactive, ↓reduceIte, List.not_mem_nil] at member
      · have listed : action ∈
            (List.range (if owner = who then k + 1 else block.block.length)).filterMap
            (fun position => block.block.wordAction owner position (final.view owner)) := by
          simpa only [imposed, inactive, ↓reduceIte] using member
        exact (List.mem_filterMap.mp listed).imp fun _ parts => parts.2
    have completeReadout (owner : Player) (action : OwnAction Player L)
        (member : action ∈ completeWord owner) :
        ∃ position, block.block.wordAction owner position (final.view owner) = some action := by
      by_cases inactive : owner ∈ current.excluded
      · simp only [completeWord, inactive, ↓reduceIte, List.not_mem_nil] at member
      · have listed : action ∈ (List.range block.block.length).filterMap
            (fun position => block.block.wordAction owner position (final.view owner)) := by
          simpa only [completeWord, inactive, ↓reduceIte] using member
        exact (List.mem_filterMap.mp listed).imp fun _ parts => parts.2
    have completeProper : ∀ owner action, action ∈ completeWord owner → ¬ action.IsFailure := by
      intro owner action member
      have activeOwner : owner ∉ current.excluded := by
        intro inactive
        simp only [completeWord, inactive, ↓reduceIte, List.not_mem_nil] at member
      obtain ⟨position, bounded, readAction⟩ := List.mem_filterMap.mp (by
        simpa only [completeWord, activeOwner, ↓reduceIte] using member)
      have rowMember : (fun player => if player ∈ current.excluded then none else
          CommitRecoveryMove.lift
            (block.block.wordAction player position (final.view player))) ∈ semantic reference := by
        rw [rows reference referenceSupported]
        exact List.mem_map.mpr ⟨position, bounded, rfl⟩
      exact (properRows reference referenceSupported _ rowMember owner ⟨action, false⟩
        (by simp only [activeOwner, ↓reduceIte, readAction, CommitRecoveryMove.lift,
          Option.map_some])).2
    have imposedSubset : ∀ owner, imposed owner ⊆ completeWord owner := by
      intro owner action member
      by_cases inactive : owner ∈ current.excluded
      · simp only [imposed, inactive, ↓reduceIte, List.not_mem_nil] at member
      · have listed : action ∈
            (List.range (if owner = who then k + 1 else block.block.length)).filterMap
              (fun position => block.block.wordAction owner position (final.view owner)) := by
          simpa only [imposed, inactive, ↓reduceIte] using member
        obtain ⟨position, bounded, readAction⟩ := List.mem_filterMap.mp listed
        simp only [completeWord, inactive, ↓reduceIte]
        refine List.mem_filterMap.mpr ⟨position, ?_, readAction⟩
        apply List.mem_range.mpr
        have bound := List.mem_range.mp bounded
        by_cases own : owner = who <;> simp only [own, ↓reduceIte] at bound <;> omega
    have imposedProper : ∀ owner action, action ∈ imposed owner → ¬ action.IsFailure :=
      fun owner action member => completeProper owner action (imposedSubset owner member)
    have sameForeign : ∀ owner, owner ≠ who → imposed owner = completeWord owner := by
      intro owner different
      simp only [imposed, completeWord, different, ↓reduceIte]
    obtain ⟨middleContext, middleNames, before, after, beforeLength, afterLength, split⟩ :=
      block.block.exists_split (k + 1) (by omega)
    let startOf (segment : SourceProgram.CommitPrefix checkpoint.residual.context
        checkpoint.residual.names block.context block.pending)
        (c : PhaseProposalOrdinarySourceCursor setup .concurrent implementation.runtime
          implementation.leaks implementation.plan control entry.phase segment block.suffix) :
        setup.proposalRecoveryProtocol.History := ⟨some c.current, c.trace⟩
    have castStart {α : Type} {β : α → Type} (f : (x : α) → β x →
        setup.proposalRecoveryProtocol.History) {x y : α} (same : x = y) (value : β x) :
        f y (same ▸ value) = f x value := by
      cases same
      rfl
    let splitCursor : PhaseProposalOrdinarySourceCursor setup .concurrent implementation.runtime
        implementation.leaks implementation.plan control entry.phase (before.append after)
          block.suffix := split.symm ▸ cursor
    have splitStart : startOf (before.append after) splitCursor =
        startOf block.block cursor := by
      exact castStart startOf split.symm cursor
    have splitStartTarget : (⟨some splitCursor.current, splitCursor.trace⟩ :
        setup.proposalRecoveryProtocol.History) = ⟨some current, targetTrace⟩ := by
      exact splitStart.trans (by rfl)
    have referenceSupported' : reference ∈ (setup.proposalRecoveryModel.runBehavioralFrom
        (sourceUnflaggedStrategy setup values) (before.length + after.length)
          ⟨some current, targetTrace⟩).support := by
      simpa only [ordinary, q0, beforeLength, show k + 1 + after.length = block.block.length by
        omega] using referenceSupported
    rw [setup.proposalRecoveryModel.runBehavioralFrom_add] at referenceSupported'
    obtain ⟨retainedPrefix, prefixSupported, suffixSupported⟩ :=
      (PMF.mem_support_bind_iff ..).mp referenceSupported'
    have prefixWords : ((semantic reference).take before.length =
        ((setup.recoveryJointRecall (setup.proposalRecoveryEraseTrace retainedPrefix.trace)).take
          before.length).reverse) ∧
        ((setup.proposalRecoveryJointRecall retainedPrefix.trace).take before.length).reverse =
          (((setup.recoveryJointRecall (setup.proposalRecoveryEraseTrace retainedPrefix.trace)).take
            before.length).reverse).map
              (fun row owner => (row owner).map ProposalRecoveryMove.ordinary) := by
      obtain ⟨lift', origin', point'⟩ :
          ∃ lifted : ProtocolState (before.prepend (after.prepend block.suffix)) →
              ProtocolState setup.program,
            ProtocolSuffix setup.program (before.prepend (after.prepend block.suffix)) lifted ∧
            current.point = lifted (ProtocolState.entry
              (before.prepend (after.prepend block.suffix)) cursor.source) := by
        rw [← before.prepend_append after block.suffix, split]
        exact ⟨cursor.lift, cursor.origin, cursor.point⟩
      obtain ⟨middle, middleState, middleTrace, firstAttempt, prefixEq, middlePoint,
        middleExcluded, middleEntry, _generation, firstWord, firstLabels, _proper⟩ :=
        proposalRecovery_ordinary_commit_block_support setup values before
          (after.prepend block.suffix) lift' origin' cursor.source current targetTrace point'
            (cursor.excluded.trans cursor.entryExcluded.symm) retainedPrefix prefixSupported
      obtain ⟨last, lastState, lastTrace, lastAttempt, referenceEq, _lastPoint,
        _lastExcluded, _lastEntry, _lastGeneration, lastWord, _lastLabels, _lastProper⟩ :=
        proposalRecovery_ordinary_commit_block_support setup values after block.suffix
          (fun state => lift' (before.liftPoint (after.prepend block.suffix) state))
          (origin'.compose (before.protocolSuffix (after.prepend block.suffix))) middle
          middleState middleTrace middlePoint (middleExcluded.trans middleEntry.symm)
          reference (by simpa only [sourceUnflaggedStrategy, prefixEq] using suffixSupported)
      have totalLength : (firstAttempt.joints ++ lastAttempt.joints).length =
          block.block.length := by
        rw [List.length_append, firstAttempt.joints_length, lastAttempt.joints_length]
        omega
      have joined : setup.recoveryJointRecall (setup.proposalRecoveryEraseTrace lastTrace) =
          (firstAttempt.joints ++ lastAttempt.joints).reverse ++
            setup.recoveryJointRecall (setup.proposalRecoveryEraseTrace targetTrace) := by
        rw [lastWord, firstWord, List.reverse_append, List.append_assoc]
      have firstRead : ((setup.recoveryJointRecall
          (setup.proposalRecoveryEraseTrace middleTrace)).take before.length).reverse =
            firstAttempt.joints := by
        rw [firstWord, ← firstAttempt.joints_length, ← List.length_reverse,
          List.take_left, List.reverse_reverse]
      refine ⟨?_, ?_⟩
      · rw [referenceEq, prefixEq, firstRead]
        dsimp only [semantic]
        rw [joined, ← totalLength, ← List.length_reverse, List.take_left,
          List.reverse_reverse, ← firstAttempt.joints_length, List.take_left]
      · rw [prefixEq, firstRead, firstLabels, ← firstAttempt.joints_length,
          ← List.length_reverse, ← List.length_map (f := fun row owner =>
            (row owner).map ProposalRecoveryMove.ordinary), List.take_left,
          List.map_reverse, List.reverse_reverse]
    have prefixWord := prefixWords.1
    have referenceCovered : ∀ row ∈ ((setup.proposalRecoveryJointRecall reference.trace).take
        (before.length + after.length)).reverse, ∀ owner move, row owner = some move →
          ∃ action ∈ completeWord owner, move = ProposalRecoveryMove.ordinary ⟨action, false⟩ := by
      intro row member owner move chosen
      have total : before.length + after.length = block.block.length := by omega
      rw [total, enrichedRows reference referenceSupported] at member
      obtain ⟨rawRow, rawMember, rfl⟩ := List.mem_map.mp member
      obtain ⟨rawMove, rawChosen, rfl⟩ := Option.map_eq_some_iff.mp chosen
      have proper := properRows reference referenceSupported rawRow rawMember owner rawMove
        rawChosen
      rw [rows reference referenceSupported] at rawMember
      obtain ⟨position, bounded, rowEq⟩ := List.mem_map.mp rawMember
      have readAction := congrFun rowEq owner
      rw [← readAction] at rawChosen
      split at rawChosen
      · cases rawChosen
      · rename_i activeOwner
        refine ⟨rawMove.action, ?_, ?_⟩
        · simp only [completeWord, activeOwner, ↓reduceIte]
          exact List.mem_filterMap.mpr ⟨position, bounded, by
            have actionRead := congrArg (Option.map (fun move => move.action)) rawChosen
            simp only [CommitRecoveryMove.lift, Option.map_map, Function.comp_def,
              Option.map_some] at actionRead
            have identity : ∀ action : Option (OwnAction Player L),
                Option.map (fun x => x) action = action := by
              intro action
              cases action <;> rfl
            rw [identity] at actionRead
            simpa only [final] using actionRead⟩
        · rw [show rawMove = ⟨rawMove.action, false⟩ by
            cases rawMove; simp_all only]
    have targetCovered : ∀ row ∈
        ((setup.proposalRecoveryJointRecall retainedPrefix.trace).take before.length).reverse,
        ∀ owner move, row owner = some move →
          ∃ action ∈ imposed owner, move = ProposalRecoveryMove.ordinary ⟨action, false⟩ := by
      intro row member owner move chosen
      have semanticPrefix : ((setup.proposalRecoveryJointRecall retainedPrefix.trace).take
          before.length).reverse = ((semantic reference).take before.length).map
            (fun row owner => (row owner).map ProposalRecoveryMove.ordinary) := by
        rw [prefixWord]
        exact prefixWords.2
      rw [semanticPrefix] at member
      obtain ⟨rawRow, rawMember, rfl⟩ := List.mem_map.mp member
      obtain ⟨rawMove, rawChosen, rfl⟩ := Option.map_eq_some_iff.mp chosen
      have fullMember := List.mem_of_mem_take rawMember
      have proper := properRows reference referenceSupported rawRow fullMember owner rawMove
        rawChosen
      rw [rows reference referenceSupported, ← List.map_take] at rawMember
      obtain ⟨position, bounded, rowEq⟩ := List.mem_map.mp rawMember
      have rangeMember := List.mem_of_mem_take bounded
      have bound : position < before.length := by
        have bounded' : position < min before.length block.block.length := by
          simpa only [List.take_range, List.mem_range] using bounded
        omega
      have readAction := congrFun rowEq owner
      rw [← readAction] at rawChosen
      split at rawChosen
      · cases rawChosen
      · rename_i activeOwner
        refine ⟨rawMove.action, ?_, ?_⟩
        · simp only [imposed, activeOwner, ↓reduceIte]
          apply List.mem_filterMap.mpr
          refine ⟨position, List.mem_range.mpr (by split <;> omega), ?_⟩
          have actionRead := congrArg (Option.map (fun move => move.action)) rawChosen
          simp only [CommitRecoveryMove.lift, Option.map_map, Function.comp_def,
            Option.map_some] at actionRead
          have identity : ∀ action : Option (OwnAction Player L),
              Option.map (fun x => x) action = action := by
            intro action
            cases action <;> rfl
          rw [identity] at actionRead
          simpa only [final] using actionRead
        · rw [show rawMove = ⟨rawMove.action, false⟩ by
            cases rawMove; simp_all only]
    have pastImposed : ∀ action ∈ imposed who, ∃ owner name payload result,
        action = OwnAction.commit owner name payload result ∧ name ∈ middleContext.map Prod.fst
          := by
      intro action member
      have activeWho : who ∉ current.excluded := by rw [cursorExcluded]; exact alive
      simp only [imposed, activeWho, ↓reduceIte] at member
      obtain ⟨position, bounded, actionRead⟩ := List.mem_filterMap.mp member
      have positionBound : position < before.length := by
        simpa only [beforeLength] using List.mem_range.mp bounded
      rw [← split, before.wordAction_append_prefix after who position _ positionBound]
        at actionRead
      obtain ⟨owner, name, domain, result, actionEq⟩ :=
        word_action_commit before who position _ action actionRead
      refine ⟨owner, name, domain, result, actionEq, ?_⟩
      exact word_action_name_in_context before who position _ owner name domain result
        (actionEq ▸ actionRead)
    have forcedComplete := source_word_run_conditioned setup .concurrent implementation.runtime
      implementation.leaks implementation.plan values fullValues nativeInitial
        implementation.horizon implementation.scheduler control
        ((nativeMenu).toRawTrace nativeInitial implementation.horizon implementation.scheduler
          trace) entry.phase before after block.suffix splitCursor (by omega) imposed completeWord
        (fun owner => final.view owner) (by simpa only [split] using readout)
        (by simpa only [split] using completeReadout) imposedProper completeProper who sameForeign
        reference retainedPrefix (by
          simpa only [← splitStartTarget,
            ← setup.proposalRecoveryModel.runBehavioralFrom_add] using
            (PMF.mem_support_bind_iff ..).mpr ⟨retainedPrefix, prefixSupported, suffixSupported⟩)
        referenceCovered (by simpa only [← splitStartTarget] using prefixSupported)
          targetCovered pastImposed
    have foreignRows (history : setup.proposalRecoveryProtocol.History)
        (member : history ∈ ordinary.support) :
        read history = word ↔ ∀ owner, owner ≠ who →
          (semantic history).map (fun row => row owner) =
            (semantic reference).map (fun row => row owner) := by
      rw [← referenceForeign]
      constructor
      · intro same owner different
        have historyEq : (reconstruct history).history owner = final.history owner := by
          simpa only [read, foreignRead, different, ↓reduceIte] using congrFun same owner
        have viewEq := block.block.prefixLaw_view_eq_of_history_eq block.suffix profile profile
          cursor.source cursor.source owner rfl _ _ (reconstructedSupport history member)
            finalSupported historyEq
        rw [rows history member, rows reference referenceSupported]
        simp only [List.map_map, Function.comp_def, viewEq, final]
      · intro same
        funext owner
        by_cases ownOwner : owner = who
        · simp only [read, foreignRead, ownOwner, ↓reduceIte]
        · obtain ⟨firstConfig, firstState, firstTrace, firstAttempt, firstEq, firstReplay,
            _firstPoint, firstExcluded, firstRecall, _firstLabels, _firstViews, _firstProper⟩ :=
            related history member
          obtain ⟨secondConfig, secondState, secondTrace, secondAttempt, secondEq, secondReplay,
            _secondPoint, secondExcluded, secondRecall, _secondLabels, _secondViews,
            _secondProper⟩ := related reference referenceSupported
          have firstRead : semantic history = firstAttempt.joints := by
            dsimp only [semantic]
            rw [firstEq, firstRecall, ← firstAttempt.joints_length,
              ← List.length_reverse, List.take_left, List.reverse_reverse]
          have secondRead : semantic reference = secondAttempt.joints := by
            dsimp only [semantic]
            rw [secondEq, secondRecall, ← secondAttempt.joints_length,
              ← List.length_reverse, List.take_left, List.reverse_reverse]
          have castJoints {config : SourceProgram.Config Player L block.context}
              {first last : Finset Player} (equal : first = last)
              (attempt : block.block.Attempt cursor.source cursor.current.excluded config first) :
              (equal ▸ attempt).joints = attempt.joints := by
            cases equal
            rfl
          have castWithout {config : SourceProgram.Config Player L block.context}
              {first last : Finset Player} (equal : first = last)
              (attempt : block.block.Attempt cursor.source cursor.current.excluded config first) :
              (equal ▸ attempt).withoutMisses ∅ cursor.source =
                attempt.withoutMisses ∅ cursor.source := by
            cases equal
            rfl
          let firstTyped := firstExcluded ▸ firstAttempt
          let secondTyped := secondExcluded ▸ secondAttempt
          have owned := structural_owned_history_of_joints block.block owner cursor.source
            cursor.source current.excluded firstConfig secondConfig firstTyped secondTyped rfl
              (by simpa only [firstTyped, secondTyped, castJoints firstExcluded firstAttempt,
                  castJoints secondExcluded secondAttempt, firstRead, secondRead]
                using same owner ownOwner)
          simpa only [read, foreignRead, ownOwner, ↓reduceIte, firstReplay, secondReplay,
            firstTyped, secondTyped, castWithout firstExcluded firstAttempt,
            castWithout secondExcluded secondAttempt]
            using owned
    have prefixFiber (history : setup.proposalRecoveryProtocol.History)
        (member : history ∈ ordinary.support) :
        own history = true ∧ read history = word ↔
          (∀ owner, owner ≠ who → (semantic history).map (fun row => row owner) =
            (semantic reference).map (fun row => row owner)) ∧
          (semantic history).take before.length = (semantic reference).take before.length := by
      have ledger := issuedLedger_iff_prefix_at_request setup implementation block.block
        block.suffix cursor.embedding low rank cursor.views.actionEq trace entry.phase
          entry.installed phaseLow phaseHigh who event payload cleanSiteProof.binding request
            (by have bounds := (entry.phase.mem_events event).mp entry.inside; omega)
            cleanSiteProof.unsent (final.view who) ((reconstruct history).view who) retained
      dsimp only [own]
      rw [ownGateEq _ (reconstructedSupport history member)]
      simp only [ownTest, high, decide_eq_true_eq, ledger, foreignRows history member]
      have rowBound (h : setup.proposalRecoveryProtocol.History)
          (supported : h ∈ ordinary.support) (position : Nat)
          (bound : position < block.block.length) : position < (semantic h).length := by
        rw [rows h supported]
        simpa only [List.length_map, List.length_range] using bound
      have rowEq (position : Nat) (bound : position < block.block.length) (owner : Player) :
          ((semantic history)[position]'(rowBound history member position bound)) owner =
            if owner ∈ current.excluded then none else CommitRecoveryMove.lift
              (block.block.wordAction owner position ((reconstruct history).view owner)) := by
        have indexed := congrArg
          (fun entries : List (Player → Option (CommitRecoveryMove Player L)) =>
          entries[position]?) (rows history member)
        have rangeBound : position < (List.range block.block.length).length := by
          simpa only [List.length_range] using bound
        have selected := Option.some.inj (by
          simpa only [List.getElem?_eq_getElem (rowBound history member position bound),
            List.getElem?_map, List.getElem?_eq_getElem rangeBound, Option.map_some,
            List.getElem_range, Option.some.injEq] using indexed)
        exact congrFun selected owner
      have referenceRow (position : Nat) (bound : position < block.block.length) (owner : Player) :
          ((semantic reference)[position]'
            (rowBound reference referenceSupported position bound)) owner =
            if owner ∈ current.excluded then none else CommitRecoveryMove.lift
              (block.block.wordAction owner position (final.view owner)) := by
        have indexed := congrArg
          (fun entries : List (Player → Option (CommitRecoveryMove Player L)) =>
          entries[position]?) (rows reference referenceSupported)
        have rangeBound : position < (List.range block.block.length).length := by
          simpa only [List.length_range] using bound
        have selected := Option.some.inj (by
          simpa only [List.getElem?_eq_getElem
            (rowBound reference referenceSupported position bound),
            List.getElem?_map, List.getElem?_eq_getElem rangeBound, Option.map_some,
            List.getElem_range, Option.some.injEq] using indexed)
        simpa only [final] using congrFun selected owner
      have activeWho : who ∉ current.excluded := by rw [cursorExcluded]; exact alive
      have liftInjective : Function.Injective
          (CommitRecoveryMove.lift : Option (OwnAction Player L) →
            Option (CommitRecoveryMove Player L)) := by
        intro first second same
        cases first with
        | none =>
          cases second with
          | none => rfl
          | some _ => simp only [CommitRecoveryMove.lift, Option.map_none,
              Option.map_some, reduceCtorEq] at same
        | some first =>
          cases second with
          | none => simp only [CommitRecoveryMove.lift, Option.map_none,
              Option.map_some, reduceCtorEq] at same
          | some second =>
            have equal : first = second := by
              simpa only [CommitRecoveryMove.lift, Option.map_some,
                Option.some.injEq, CommitRecoveryMove.mk.injEq, and_true] using same
            cases equal
            rfl
      constructor
      · rintro ⟨⟨earlier, chosen⟩, others⟩
        refine ⟨others, ?_⟩
        apply List.ext_getElem
        · rw [List.length_take, List.length_take, rows history member,
            rows reference referenceSupported]
          simp
        · intro position firstBound secondBound
          have bound : position < before.length := by
            exact lt_of_lt_of_le firstBound (List.length_take_le ..)
          have wholeBound : position < block.block.length := by omega
          funext owner
          rw [List.getElem_take, List.getElem_take, rowEq position wholeBound owner,
            referenceRow position wholeBound owner]
          by_cases ownOwner : owner = who
          · subst owner
            simp only [activeWho, ↓reduceIte]
            congr 1
            by_cases past : position < k
            · exact earlier position past
            · have currentPosition : position = k := by omega
              simpa only [currentPosition, selected] using chosen
          · have mapped := congrArg (fun items => items[position]?) (others owner ownOwner)
            simpa only [rows history member, rows reference referenceSupported,
              List.getElem?_map, List.getElem?_range, wholeBound, ↓reduceIte,
              Option.map_some, Option.some.injEq] using mapped
      · rintro ⟨others, prefixEq⟩
        have ownRows (position : Nat) (bound : position < before.length) :
            block.block.wordAction who position ((reconstruct history).view who) =
              block.block.wordAction who position (final.view who) := by
          have wholeBound : position < block.block.length := by omega
          have selectedRow := congrArg (fun items => (items[position]?).map
            (fun row => row who)) prefixEq
          apply liftInjective
          simpa only [rows history member, rows reference referenceSupported,
            List.getElem?_take, bound, ↓reduceIte, List.getElem?_map, List.getElem?_range,
            wholeBound, Option.map_some, Option.some.injEq, activeWho, ↓reduceIte]
            using selectedRow
        exact ⟨⟨fun position bound => ownRows position (by omega),
          (ownRows k (by omega)).trans selected⟩, others⟩
    let foreignObserved := fun history : setup.proposalRecoveryProtocol.History =>
      decide (∀ owner, owner ≠ who → (semantic history).map (fun row => row owner) =
        (semantic reference).map (fun row => row owner))
    let prefixObserved := fun history : setup.proposalRecoveryProtocol.History =>
      (semantic history).take before.length
    let jointObserved := fun history : setup.proposalRecoveryProtocol.History =>
      decide (own history = true ∧ read history = word)
    have foreignPresent : true ∈ (ordinary.map foreignObserved).support :=
      (PMF.mem_support_map_iff ..).mpr ⟨reference, referenceSupported, by
        exact decide_eq_true (by intro owner _; rfl)⟩
    have referenceConditioned : reference ∈
        (fiberPosterior ordinary foreignObserved true).support := by
      rw [fiberPosterior_support _ _ _ foreignPresent]
      exact ⟨by exact decide_eq_true (by intro owner _; rfl),
        referenceSupported⟩
    have prefixPresent : prefixObserved reference ∈
        ((fiberPosterior ordinary foreignObserved true).map prefixObserved).support :=
      (PMF.mem_support_map_iff ..).mpr ⟨reference, referenceConditioned, rfl⟩
    have total : before.length + after.length = block.block.length := by omega
    have completedConditional :
        setup.proposalRecoveryModel.runBehavioralFrom (sourceBlockWordStrategy setup values imposed)
          block.block.length ⟨some current, targetTrace⟩ =
          fiberPosterior ordinary (fun history => (own history, read history)) (true, word) := by
      have nested : setup.proposalRecoveryModel.runBehavioralFrom
          (sourceBlockWordStrategy setup values imposed) block.block.length
            ⟨some current, targetTrace⟩ =
          fiberPosterior (fiberPosterior ordinary foreignObserved true) prefixObserved
            (prefixObserved reference) := by
        rw [splitStartTarget] at forcedComplete
        simpa only [total, ordinary, q0, semantic, foreignObserved, prefixObserved,
          prefixWord] using forcedComplete
      have appended := posterior_append_observation ordinary foreignObserved jointObserved
        prefixObserved (prefixObserved reference) (fiberPosterior ordinary foreignObserved true)
          _ foreignPresent rfl prefixPresent nested (by
            intro history member
            simpa only [jointObserved, foreignObserved, prefixObserved, decide_eq_true_eq]
              using prefixFiber history member)
      rw [appended.2]
      exact fiberPosterior_eq_of_support_fiber ordinary jointObserved
        (fun history => (own history, read history)) true (true, word) (by
          intro history _
          simp only [jointObserved, decide_eq_true_eq, Prod.mk.injEq])
    have forcedWord : sourceForcedBlockJoint setup values implementation who
        ⟨some control, trace⟩ event payload ⟨some current, targetTrace⟩ word value =
        (setup.proposalRecoveryModel.runBehavioralFrom
          (sourceBlockWordStrategy setup values imposed) k ⟨some current, targetTrace⟩).bind
            (fun cut => (setup.proposalRecoveryModel.runBehavioralFrom
              (sourceBlockWordStrategy setup values imposed) (sourceCommitFuel setup cut) cut).map
                (Prod.mk cut)) := by
      let chosen := decodeEventAction setup.program event
        (cast (congrArg EventField.Action cleanSiteProof.binding.symm) (.success value))
      let prior := phaseCommitRecallWord setup.program .concurrent implementation.runtime
        implementation.leaks low event.val control.execution.application.generation
          (control.execution.recall who)
      let listed : SourceProgram.History Player L := fun owner => if owner = who then
        prior ++ chosen.toList else (word owner).drop
          ((ProtocolState.history setup.program current.point owner).length)
      have listMembership : ∀ owner action,
          action ∈ (if owner ∈ current.excluded then [] else listed owner) ↔
            action ∈ imposed owner := by
        intro owner action
        by_cases inactive : owner ∈ current.excluded
        · simp only [inactive, imposed, ↓reduceIte]
        · by_cases ownOwner : owner = who
          · subst owner
            have recalledActions := issued_ledger_recall_actions setup implementation block.block
              block.suffix cursor.embedding low rank cursor.views.actionEq control trace
                entry.phase entry.installed phaseLow phaseHigh who event payload
                  cleanSiteProof.binding
                  request (by have bounds := (entry.phase.mem_events event).mp entry.inside; omega)
                  (final.view who) retained action
            simp only [inactive, listed, prior, chosen, imposed, ↓reduceIte,
              List.mem_append, Option.mem_toList, recalledActions, ← selected]
            constructor
            · rintro (⟨position, bound, actionRead⟩ | actionRead)
              · exact List.mem_filterMap.mpr ⟨position, List.mem_range.mpr (by omega), actionRead⟩
              · exact List.mem_filterMap.mpr ⟨k, List.mem_range.mpr (by omega), actionRead⟩
            · rintro member
              obtain ⟨position, bounded, actionRead⟩ := List.mem_filterMap.mp member
              have bound := List.mem_range.mp bounded
              by_cases earlier : position < k
              · exact Or.inl ⟨position, earlier, actionRead⟩
              · have same : position = k := by omega
                exact Or.inr (same ▸ actionRead)
          · have fullWord : word owner = final.history owner := by
              have same := congrFun referenceForeign owner
              simpa only [read, foreignRead, ownOwner, ↓reduceIte] using same.symm
            have entryWord : ProtocolState.history setup.program current.point owner =
                cursor.source.history owner := rfl
            simp only [inactive, listed, imposed, ownOwner, ↓reduceIte, fullWord, entryWord]
            rw [ordinaryBlockWord_drop block.block block.suffix profile cursor.source owner
              final finalSupported]
      have strategies : sourceBlockWordStrategy setup values
          (fun owner => if owner ∈ current.excluded then [] else listed owner) =
          sourceBlockWordStrategy setup values imposed := by
        funext owner information
        unfold sourceBlockWordStrategy
        simp only [listMembership]
      have sourceRank : instructionCount setup.program -
          ProtocolState.remaining setup.program current.point = low := by
        rw [← cursorCurrent]
        rw [cursor.point, cursor.origin.remaining_lift, ProtocolState.remaining_entry]
        have programCount := cursor.compiled.countEq
        simp only [eventCount_eq_instructionCount] at programCount
        have start : cursor.offset = low := offset
        omega
      simp only [sourceForcedBlockJoint, cleanSiteProof.binding, ↓reduceDIte]
      change ((setup.proposalRecoveryModel.runBehavioralFrom
          (sourceBlockWordStrategy setup values listed) (event.val -
            (instructionCount setup.program - ProtocolState.remaining setup.program current.point))
          ⟨some current, targetTrace⟩).bind fun cut =>
            (setup.proposalRecoveryModel.runBehavioralFrom (sourceBlockWordStrategy setup values
              listed) (sourceCommitFuel setup cut) cut).map (Prod.mk cut)) = _
      rw [sourceRank, source_word_cut_mask_excluded setup values listed current.excluded
        ⟨some current, targetTrace⟩ k (by exact Finset.Subset.refl _), strategies]
    obtain ⟨cutContext, cutNames, cutBefore, cutAfter, cutLength, restLength, cutSplit⟩ :=
      block.block.exists_split k inside.le
    let cutCursor : PhaseProposalOrdinarySourceCursor setup .concurrent implementation.runtime
        implementation.leaks implementation.plan control entry.phase (cutBefore.append cutAfter)
          block.suffix := cutSplit.symm ▸ cursor
    have cutStart : (⟨some cutCursor.current, cutCursor.trace⟩ :
        setup.proposalRecoveryProtocol.History) = ⟨some current, targetTrace⟩ := by
      exact (castStart startOf cutSplit.symm cursor).trans cursorStart
    have cutTraceLength : cutCursor.trace.length = targetTrace.length :=
      congrArg (fun history : setup.proposalRecoveryProtocol.History => history.trace.length)
        cutStart
    have forcedGeometry := source_word_pair_fuel setup values implementation control
      entry.phase cutBefore cutAfter block.suffix block.boundary cutCursor imposed
        (fun owner => final.view owner) (by simpa only [cutSplit] using readout) imposedProper
    have ordinaryGeometry := ordinary_source_pair_geometry setup values implementation
      control entry.phase cutBefore cutAfter block.suffix cutCursor
    rw [cutStart] at forcedGeometry ordinaryGeometry
    have cutRest : cutAfter.length = block.block.length - k := by omega
    rw [cutLength, cutRest] at forcedGeometry ordinaryGeometry
    have forcedCompletion : (sourceForcedBlockJoint setup values implementation who
        ⟨some control, trace⟩ event payload ⟨some current, targetTrace⟩ word value).map Prod.snd =
        fiberPosterior ordinary (fun history => (own history, read history)) (true, word) := by
      rw [forcedWord]
      have fuelEq := forcedGeometry.1
      rw [fuelEq]
      simp only [PMF.map_bind, PMF.map_comp, Function.comp_def]
      simp only [show (fun x : setup.proposalRecoveryProtocol.History => x) = id from rfl,
        PMF.map_id]
      rw [← setup.proposalRecoveryModel.runBehavioralFrom_add,
        Nat.add_sub_of_le inside.le]
      exact completedConditional
    have pairPresent : (true, word) ∈
        (pair.map (fun point => (own point.2, read point.2))).support := by
      rw [← pairComplete, PMF.map_comp, Function.comp_def] at jointPresent
      exact jointPresent
    have posteriorCompletion :
        (fiberPosterior pair (fun point => (own point.2, read point.2)) (true, word)).map Prod.snd =
          fiberPosterior ordinary (fun history => (own history, read history)) (true, word) := by
      have mapped := map_fiberPosterior_readout pair Prod.snd
        (fun history => (own history, read history)) (true, word) pairPresent
      simpa only [pairComplete, Function.comp_def] using mapped
    apply source_pair_eq_of_completed setup _ _ (targetTrace.length + k)
    · intro point member
      rw [forcedWord] at member
      simpa only [cutLength] using (forcedGeometry.2 point member).1
    · intro point member
      have original := (mem_support_fiberPosterior pairPresent member).2
      simpa only [cutLength, cutRest]
        using (ordinaryGeometry point original).1
    · intro point member
      rw [forcedWord] at member
      simpa only [cutLength, cutTraceLength] using (forcedGeometry.2 point member).2
    · intro point member
      have original := (mem_support_fiberPosterior pairPresent member).2
      simpa only [cutLength, cutRest, cutTraceLength]
        using (ordinaryGeometry point original).2
    · exact forcedCompletion.trans posteriorCompletion.symm
  have result := pair_posteriors_of_word_conditionals pair words ownLaw
    (fun point => read point.2) (fun point => own point.2) foreignGate
      (fun word => sourceForcedBlockJoint setup values implementation who ⟨some control, trace⟩
        event payload ⟨some current, targetTrace⟩ word value) ownPositive foreignPositive
          pairJoint conditional
  have observedMap : pair.map observed =
      pair.map (fun point => own point.2 && foreignGate (read point.2)) :=
    map_congr_on_support pair pairObserved
  have ownMap : pair.map ownObserved = pair.map (fun point => own point.2) :=
    map_congr_on_support pair pairOwn
  have observedPosterior := fiberPosterior_eq_of_support_fiber pair observed
    (fun point => own point.2 && foreignGate (read point.2)) true true
      (fun point member => by rw [pairObserved point member])
  have ownPosterior := fiberPosterior_eq_of_support_fiber pair ownObserved
    (fun point => own point.2) true true (fun point member => by rw [pairOwn point member])
  have wordsEq : foreign.map Prod.fst = words := by
    rw [foreignEq, PMF.map_comp]
    exact PMF.map_id _
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [observedMap]
    exact result.1
  · simpa only [foreignEq] using result.2.1
  · rw [observedPosterior, foreignEq]
    exact result.2.2.1
  · rw [ownMap]
    exact result.2.2.2.1
  · rw [ownPosterior, wordsEq]
    exact result.2.2.2.2

end ForeignPosterior

section NativeReconstruction

open scoped ENNReal

variable (implementation : ReservedConcurrentImplementation setup)

local notation "nativeApplication" => implementation.application
local notation "nativeMenu" => PhaseCount.onePacketMenu implementation.runtime
  implementation.leaks implementation.bounds
local notation "nativeInitial" => implementation.initial

open Classical in
-- OPEN OBLIGATION: qualified_annotation_pushforward - Exact qualified decision-cut weights
theorem qualified_annotation_pushforward
    (operational : implementation.Operational)
    (scale sourceBad nativeBad : Set.Icc (0 : ℝ) 1)
    (scalePositive : 0 < scale.val) (scaleBelow : scale.val < 1)
    (sourceBadPositive : 0 < sourceBad.val) (sourceBadBelow : sourceBad.val < 1)
    (nativeBadPositive : 0 < nativeBad.val) (nativeBadBelow : nativeBad.val < 1)
    (fullValues : ∀ owner key, FullSupport (values owner key))
    (sourceProfile : ∀ owner, setup.proposalRecoveryModel.BehavioralPolicy owner)
    (nativeProfile : ∀ owner,
      ((nativeMenu).information nativeInitial implementation.horizon
        implementation.scheduler).BehavioralPolicy owner)
    (sourcePrescribed : ∀ owner (history : setup.proposalRecoveryProtocol.History),
      ¬ setup.proposalRecoveryProtocol.terminal history.state →
      sourceProfile owner (setup.proposalRecoveryModel.infoOf owner history.trace) =
        setup.proposalRecoveryNormalizedTrembledProfile
          scale.val scale.property.1 scale.property.2
          sourceBad.val sourceBad.property.1 sourceBad.property.2
          scale.val scale.property.1 scale.property.2 values owner
            (setup.proposalRecoveryModel.infoOf owner history.trace))
    (nativePrescribed : nativeProfile = phaseProposalReferenceStrategy setup .concurrent
      implementation.runtime implementation.leaks implementation.bounds implementation.plan
      nativeInitial implementation.horizon implementation.scheduler values
      ⟨nativeBad, scale, scale, scale⟩)
    (who : Player)
    (site : ((nativeMenu).information nativeInitial implementation.horizon
      implementation.scheduler).InformationSite who)
    (past : List (nativeApplication).PlayerEntry) (view : (nativeApplication).PlayerView)
    (siteEq : site.1 = some (past, view))
    (event : (serviceGraph setup .concurrent).EventId) (payload : L.Ty)
    (cleanSite : CleanUnsentBinding setup implementation who past view event payload)
    (qualified : 0 < qualifiedPrefixMass setup implementation nativeProfile who site event)
    (source : QualifiedBindingSource setup values implementation sourceProfile who site past view
      event payload cleanSite.binding)
    (pairLaw : ForeignPosteriorCutPair setup values implementation) :
    let sourceSite := source.site
    let encode := source.encode
    let anchor := source.anchor
    let own := ENNReal.ofReal (setup.proposalRecoveryModel.ownPlayReachProbability
      (sourceProfile who) (setup.proposalRecoveryModel.ownPlay who anchor.trace))
    let classes := (setup.proposalRecoveryForeignProducts values scale sourceBad scale
      who anchor.trace).1
    let coefficient := mechanicalCoefficient setup implementation
      ⟨nativeBad, scale, scale, scale⟩ nativeProfile who site event
    let sourceMass := ∑' h : setup.proposalRecoveryModel.InformationHistory who sourceSite.1,
      if setup.proposalRecoveryForeignGood who h.val then
        setup.proposalRecoveryModel.historyReachWeight sourceProfile h.val else 0
    0 < own ∧ own ≠ ⊤ ∧ 0 < classes ∧ classes ≠ ⊤ ∧
    0 < sourceMass ∧ sourceMass ≠ ⊤ ∧
    0 < ∑' index, coefficient index ∧ (∑' index, coefficient index) ≠ ⊤ ∧
    (∀ history : setup.proposalRecoveryProtocol.History,
      setup.proposalRecoveryForeignGood who history →
      setup.proposalRecoveryModel.infoOf who history.trace = sourceSite.1 →
      own = ENNReal.ofReal (setup.proposalRecoveryModel.ownPlayReachProbability
        (sourceProfile who) (setup.proposalRecoveryModel.ownPlay who history.trace)) ∧
      classes = (setup.proposalRecoveryForeignProducts values scale sourceBad scale
        who history.trace).1) ∧
    ∀ (index : MechanicalIndex setup implementation who) (value : L.Val payload)
      (cut completed : setup.proposalRecoveryProtocol.History),
      own * classes * annotatedForcedBlockWeight setup values implementation operational
        sourceProfile nativeProfile who site index event payload value cut completed =
      coefficient index *
        (if same : setup.proposalRecoveryModel.infoOf who cut.trace = sourceSite.1 then
          if setup.proposalRecoveryForeignGood who cut then
            setup.proposalRecoveryModel.historyReachWeight sourceProfile cut *
              sourceForcedBlock setup values who cut (same.symm ▸ encode value) completed
          else 0
        else 0) := by
  sorry

open Classical in
theorem qualified_reconstruction
    (operational : implementation.Operational)
    (scale sourceBad nativeBad : Set.Icc (0 : ℝ) 1)
    (scalePositive : 0 < scale.val) (scaleBelow : scale.val < 1)
    (sourceBadPositive : 0 < sourceBad.val) (sourceBadBelow : sourceBad.val < 1)
    (nativeBadPositive : 0 < nativeBad.val) (nativeBadBelow : nativeBad.val < 1)
    (fullValues : ∀ owner key, FullSupport (values owner key))
    (sourceProfile : ∀ owner, setup.proposalRecoveryModel.BehavioralPolicy owner)
    (nativeProfile : ∀ owner,
      ((nativeMenu).information nativeInitial implementation.horizon
        implementation.scheduler).BehavioralPolicy owner)
    (sourcePrescribed : ∀ owner (history : setup.proposalRecoveryProtocol.History),
      ¬ setup.proposalRecoveryProtocol.terminal history.state →
      sourceProfile owner (setup.proposalRecoveryModel.infoOf owner history.trace) =
        setup.proposalRecoveryNormalizedTrembledProfile
          scale.val scale.property.1 scale.property.2
          sourceBad.val sourceBad.property.1 sourceBad.property.2
          scale.val scale.property.1 scale.property.2 values owner
            (setup.proposalRecoveryModel.infoOf owner history.trace))
    (nativePrescribed : nativeProfile = phaseProposalReferenceStrategy setup .concurrent
      implementation.runtime implementation.leaks implementation.bounds implementation.plan
      nativeInitial implementation.horizon implementation.scheduler values
      ⟨nativeBad, scale, scale, scale⟩)
    (who : Player)
    (site : ((nativeMenu).information nativeInitial implementation.horizon
      implementation.scheduler).InformationSite who)
    (past : List (nativeApplication).PlayerEntry) (view : (nativeApplication).PlayerView)
    (siteEq : site.1 = some (past, view))
    (event : (serviceGraph setup .concurrent).EventId) (payload : L.Ty)
    (cleanSite : CleanUnsentBinding setup implementation who past view event payload)
    (qualified : 0 < qualifiedPrefixMass setup implementation nativeProfile who site event) :
    ∃ (sourceSite : setup.proposalRecoveryModel.InformationSite who)
      (encode : L.Val payload → setup.proposalRecoveryModel.Choice who sourceSite.1)
      (anchor : setup.proposalRecoveryProtocol.History),
      setup.proposalRecoveryModel.infoOf who anchor.trace = sourceSite.1 ∧
      setup.proposalRecoveryForeignGood who anchor ∧
      0 < setup.proposalRecoveryModel.historyReachWeight sourceProfile anchor ∧
      phaseProposalQuery? setup .concurrent implementation.runtime implementation.leaks
          implementation.plan who event past view =
        some (setup.proposalRecoveryQuery who sourceSite.1) ∧
      (∀ value, phaseRecoveryBindingData setup .concurrent event who payload cleanSite.binding
        ((encode value).val.map (fun move => move.semantic)) = (.success value, false)) ∧
      sourceUnflaggedStrategy setup values who sourceSite.1 =
        (values who (setup.proposalRecoveryQuery who sourceSite.1)).map (fun sampled =>
          encode (phaseRecoveryDomainValue setup .concurrent event who payload cleanSite.binding
            sampled.val.val)) ∧
      let own := ENNReal.ofReal (setup.proposalRecoveryModel.ownPlayReachProbability
        (sourceProfile who) (setup.proposalRecoveryModel.ownPlay who anchor.trace))
      let classes := (setup.proposalRecoveryForeignProducts values scale sourceBad scale
        who anchor.trace).1
      let coefficient := mechanicalCoefficient setup implementation
        ⟨nativeBad, scale, scale, scale⟩ nativeProfile who site event
      let sourceMass := ∑' h : setup.proposalRecoveryModel.InformationHistory who sourceSite.1,
        if setup.proposalRecoveryForeignGood who h.val then
          setup.proposalRecoveryModel.historyReachWeight sourceProfile h.val else 0
      0 < own ∧ own ≠ ⊤ ∧ 0 < classes ∧ classes ≠ ⊤ ∧
      0 < sourceMass ∧ sourceMass ≠ ⊤ ∧
      0 < ∑' index, coefficient index ∧ (∑' index, coefficient index) ≠ ⊤ ∧
      (∀ history : setup.proposalRecoveryProtocol.History,
        setup.proposalRecoveryForeignGood who history →
        setup.proposalRecoveryModel.infoOf who history.trace = sourceSite.1 →
        own = ENNReal.ofReal (setup.proposalRecoveryModel.ownPlayReachProbability
          (sourceProfile who) (setup.proposalRecoveryModel.ownPlay who history.trace)) ∧
        classes = (setup.proposalRecoveryForeignProducts values scale sourceBad scale
          who history.trace).1) ∧
      ∀ (index : MechanicalIndex setup implementation who) (value : L.Val payload)
        (cut completed : setup.proposalRecoveryProtocol.History),
        own * classes * annotatedForcedBlockWeight setup values implementation operational
          sourceProfile nativeProfile who site index event payload value cut completed =
        coefficient index *
          (if same : setup.proposalRecoveryModel.infoOf who cut.trace = sourceSite.1 then
            if setup.proposalRecoveryForeignGood who cut then
              setup.proposalRecoveryModel.historyReachWeight sourceProfile cut *
                sourceForcedBlock setup values who cut (same.symm ▸ encode value) completed
            else 0
          else 0) := by
  obtain ⟨source⟩ := qualified_source_site setup values implementation operational
      scale sourceBad nativeBad
      scalePositive scaleBelow sourceBadPositive sourceBadBelow nativeBadPositive nativeBadBelow
      fullValues sourceProfile nativeProfile sourcePrescribed nativePrescribed who site past view
      siteEq event payload cleanSite qualified
  refine ⟨source.site, source.encode, source.anchor, source.anchorInfo, source.anchorGood,
    source.anchorReach, source.query, source.encoded, source.ordinary, ?_⟩
  exact qualified_annotation_pushforward setup values implementation operational
      scale sourceBad nativeBad
      scalePositive scaleBelow sourceBadPositive sourceBadBelow nativeBadPositive nativeBadBelow
      fullValues sourceProfile nativeProfile sourcePrescribed nativePrescribed who site past view
      siteEq event payload cleanSite qualified source
    (foreign_posterior_cut_pair setup values implementation)

end NativeReconstruction


section QualifiedPayoffAttachment

variable (implementation : ReservedConcurrentImplementation setup)

local notation "nativeApplication" => implementation.application
local notation "nativeMenu" => PhaseCount.onePacketMenu implementation.runtime
  implementation.leaks implementation.bounds
local notation "nativeInitial" => implementation.initial
local notation "nativeProtocol" => ReactiveApplication.ResponseMenu.protocol
  (PhaseCount.onePacketMenu implementation.runtime implementation.leaks implementation.bounds)
  implementation.initial implementation.horizon implementation.scheduler
local notation "nativeModel" => ReactiveApplication.ResponseMenu.information
  (PhaseCount.onePacketMenu implementation.runtime implementation.leaks implementation.bounds)
  implementation.initial implementation.horizon implementation.scheduler

open Classical in
/-- Open proof obligation: the actual qualified native payoff numerator equals
its full annotated source continuation numerator, including the unqualified complement. -/
-- OPEN OBLIGATION: annotated_stopped_payoff - Qualified payoff numerator on the original tape
theorem annotated_stopped_payoff
    (operational : implementation.Operational)
    (scale sourceBad : Set.Icc (0 : ℝ) 1)
    (scalePositive : 0 < scale.val) (scaleBelow : scale.val < 1)
    (badPositive : 0 < sourceBad.val) (badBelow : sourceBad.val < 1)
    (fullValues : ∀ owner key, FullSupport (values owner key))
    (sourceProfile : ∀ owner, setup.proposalRecoveryModel.BehavioralPolicy owner)
    (sourcePrescribed : ∀ owner (history : setup.proposalRecoveryProtocol.History),
      ¬ setup.proposalRecoveryProtocol.terminal history.state →
      sourceProfile owner (setup.proposalRecoveryModel.infoOf owner history.trace) =
        setup.proposalRecoveryNormalizedTrembledProfile
          scale.val scale.property.1 scale.property.2
          sourceBad.val sourceBad.property.1 sourceBad.property.2
          scale.val scale.property.1 scale.property.2 values owner
            (setup.proposalRecoveryModel.infoOf owner history.trace))
    (native : (nativeModel).BehavioralAssessment)
    (nativeMixed : native.IsFullyMixed)
    (nativeBayes : InformationModel.BehavioralAssessment.IsBayesConsistent
      (nativeModel) native ((nativeMenu).decisionInformationAntichain nativeInitial
        implementation.horizon implementation.scheduler))
    (who : Player) (site : (nativeModel).InformationSite who)
    (past : List (nativeApplication).PlayerEntry)
    (view : (nativeApplication).PlayerView)
    (information : site.1 = some (past, view))
    (event : (serviceGraph setup .concurrent).EventId) (payload : L.Ty)
    (cleanSite : CleanUnsentBinding setup implementation who past view event payload)
    (value : L.Val payload)
    (choice : (nativeModel).Choice who site.1)
    (proper : ∃ (serial : Nat)
        (material : WitnessedSubmission (serviceGraph setup .concurrent)),
      choice.1 = some ⟨some material⟩ ∧
      material.call.packet = .commitment event (who, .prepared serial) ∧
      PhaseProposal.bindingPreparation material = some ⟨payload, value⟩)
    (utility : State L setup.program.terminalCtx → Player → ℝ)
    (excludedPayoff : Player → ℝ) (outcome : Option ℝ)
    (pairLaw : ForeignPosteriorCutPair setup values implementation) :
    let informationMass := (nativeModel).informationMass native.strategy who site
    let admittedMass := qualifiedPrefixMass setup implementation native.strategy who site event
    informationMass *
        qualifiedPayoff setup .concurrent implementation.runtime implementation.leaks
          implementation.bounds implementation.plan implementation.prior values native
          who site choice utility excludedPayoff outcome =
      (∑' index : MechanicalIndex setup implementation who,
        ∑' cut : setup.proposalRecoveryProtocol.History,
          ∑' completed : setup.proposalRecoveryProtocol.History,
            annotatedForcedBlockWeight setup values implementation operational sourceProfile
              native.strategy who site index event payload value cut completed *
              ((setup.proposalRecoveryModel.runBehavioralTerminalFrom
                setup.proposalRecoveryProtocol_bounded.wellFoundedHistories
                (sourceUnflaggedStrategy setup values) completed).map fun terminal =>
                  some (setup.proposalRecoveryPayoff utility excludedPayoff who terminal))
                outcome) +
      (informationMass - admittedMass) * (PMF.pure (none : Option ℝ)) outcome
 := by
  sorry

end QualifiedPayoffAttachment

omit mode runtime leaks bounds plan prior values in
/-- The original concurrent assessments satisfy exact qualified binding transport. -/
theorem qualified_binding_law (implementation : ReservedConcurrentImplementation setup) :
    QualifiedBindingLaw setup implementation := by
  classical
  intro operational scale sourceBad nativeBad scalePositive scaleBelow badPositive badBelow
    nativePositive nativeBelow values fullValues source native sourceMixed sourceBayes
    sourcePrescribed nativeMixed nativeBayes nativePrescribed who site past view information
    event payload binding request unsent noSaved noCurrent noForeignFailure
  dsimp only
  let model := (PhaseCount.onePacketMenu implementation.runtime implementation.leaks
    implementation.bounds).information implementation.initial implementation.horizon
      implementation.scheduler
  let cleanSite : CleanUnsentBinding setup implementation who past view event payload :=
    ⟨binding, request, unsent, noSaved, noCurrent, noForeignFailure⟩
  let proper := fun (value : L.Val payload) (choice : model.Choice who site.1) =>
    ∃ (serial : Nat) (material : WitnessedSubmission (serviceGraph setup .concurrent)),
      choice.1 = some ⟨some material⟩ ∧
      material.call.packet = .commitment event (who, .prepared serial) ∧
      PhaseProposal.bindingPreparation material = some ⟨payload, value⟩
  let mass := fun choice => qualificationMass setup .concurrent implementation.runtime
    implementation.leaks implementation.bounds implementation.plan implementation.prior
    values native who site choice
  let payoff := fun choice utility excludedPayoff => qualifiedPayoff setup .concurrent
    implementation.runtime implementation.leaks implementation.bounds implementation.plan
    implementation.prior values native who site choice utility excludedPayoff
  let nativeMass := model.informationMass native.strategy who site
  let admittedMass := qualifiedPrefixMass setup implementation native.strategy who site event
  have nativeMassPositive : 0 < nativeMass :=
    model.informationMass_pos_of_fullSupport native.strategy nativeMixed who site
  have nativeMassFinite : nativeMass ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top
    (model.informationMass_le_one native.strategy who site
      ((PhaseCount.onePacketMenu implementation.runtime implementation.leaks
        implementation.bounds).decisionInformationAntichain implementation.initial
        implementation.horizon implementation.scheduler who site))
  have pairLaw := foreign_posterior_cut_pair setup values implementation
  have endpoint (value : L.Val payload) (choice : model.Choice who site.1)
      (offered : proper value choice) (utility : State L setup.program.terminalCtx → Player → ℝ)
      (excludedPayoff : Player → ℝ) (outcome : Option ℝ) :=
    annotated_stopped_payoff setup values implementation operational scale sourceBad
      scalePositive scaleBelow badPositive badBelow fullValues source.strategy sourcePrescribed
      native nativeMixed nativeBayes who site past view information event payload cleanSite
      value choice offered utility excludedPayoff outcome pairLaw
  by_cases offered : ∃ (value : L.Val payload) (choice : model.Choice who site.1),
      proper value choice
  · obtain ⟨referenceValue, referenceChoice, referenceProper⟩ := offered
    by_cases admittedZero : admittedMass = 0
    · left
      intro value choice properChoice
      have atNone := endpoint value choice properChoice (fun _ _ => 0) (fun _ => 0) none
      have noneOne : payoff choice (fun _ _ => 0) (fun _ => 0) none = 1 := by
        apply (ENNReal.mul_right_inj nativeMassPositive.ne' nativeMassFinite).mp
        simpa [admittedMass, nativeMass, admittedZero, PMF.map_apply] using atNone
      have pure : payoff choice (fun _ _ => 0) (fun _ => 0) = PMF.pure none := by
        apply pmf_eq_pure_of_support_subset_singleton
        exact ((PMF.apply_eq_one_iff _ _).mp noneOne).subset
      have zero : mass choice = 0 := by
        have observed := qualifiedPayoff_isSome setup .concurrent implementation.runtime
          implementation.leaks implementation.bounds implementation.plan implementation.prior
          values native who site choice (fun _ _ => 0) (fun _ => 0)
        rw [show qualifiedPayoff setup .concurrent implementation.runtime implementation.leaks
          implementation.bounds implementation.plan implementation.prior values native who site
          choice (fun _ _ => 0) (fun _ => 0) = PMF.pure none from pure] at observed
        have atTrue := congrArg (fun law : PMF Bool => law true) observed
        simpa only [mass, qualificationMass, PMF.pure_map, Option.isSome_none,
          PMF.pure_apply_of_ne false true (by decide : true ≠ false), ENNReal.toReal_zero]
            using congrArg ENNReal.toReal atTrue.symm
      exact ⟨zero, fun utility excludedPayoff => qualifiedPayoff_eq_pure_none setup .concurrent
        implementation.runtime implementation.leaks implementation.bounds implementation.plan
        implementation.prior values native who site choice zero utility excludedPayoff⟩
    · have admittedPositive : 0 < admittedMass := pos_iff_ne_zero.mpr admittedZero
      obtain ⟨sourceSite, encode, anchor, anchorInfo, anchorGood, anchorReach, query, encoded,
          ordinary, ownPositive, ownFinite, classesPositive, classesFinite, sourceMassPositive,
          sourceMassFinite, coefficientPositive, coefficientFinite, _constant, rectangle⟩ :=
        qualified_reconstruction setup values implementation operational scale sourceBad nativeBad
          scalePositive scaleBelow badPositive badBelow nativePositive nativeBelow fullValues
          source.strategy native.strategy sourcePrescribed nativePrescribed who site past view
          information event payload cleanSite admittedPositive
      let own := ENNReal.ofReal (setup.proposalRecoveryModel.ownPlayReachProbability
        (source.strategy who) (setup.proposalRecoveryModel.ownPlay who anchor.trace))
      let classes := (setup.proposalRecoveryForeignProducts values scale sourceBad scale
        who anchor.trace).1
      let factor := own * classes
      let coefficient := mechanicalCoefficient setup implementation
        ⟨nativeBad, scale, scale, scale⟩ native.strategy who site event
      let coefficientMass := ∑' index, coefficient index
      let good : Set (setup.proposalRecoveryModel.InformationHistory who sourceSite.1) :=
        {h | setup.proposalRecoveryForeignGood who h.val}
      let sourceMass := ∑' h : setup.proposalRecoveryModel.InformationHistory who sourceSite.1,
        if setup.proposalRecoveryForeignGood who h.val then
          setup.proposalRecoveryModel.historyReachWeight source.strategy h.val else 0
      let sourceInformationMass :=
        setup.proposalRecoveryModel.informationMass source.strategy who sourceSite
      have sourceInformationPositive : 0 < sourceInformationMass :=
        setup.proposalRecoveryModel.informationMass_pos_of_fullSupport
          source.strategy sourceMixed who sourceSite
      have sourceInformationFinite : sourceInformationMass ≠ ⊤ :=
        ne_top_of_le_ne_top ENNReal.one_ne_top
          (setup.proposalRecoveryModel.informationMass_le_one source.strategy who sourceSite
            (setup.proposalRecoveryModel_decisionAntichain who sourceSite))
      have beliefScale (h : setup.proposalRecoveryModel.InformationHistory who sourceSite.1) :
          sourceInformationMass * source.belief who sourceSite h =
            setup.proposalRecoveryModel.historyReachWeight source.strategy h.val := by
        rw [sourceBayes who sourceSite sourceInformationPositive h, div_eq_mul_inv]
        calc
          _ = setup.proposalRecoveryModel.historyReachWeight source.strategy h.val *
              (sourceInformationMass * sourceInformationMass⁻¹) := by ac_rfl
          _ = _ := by rw [ENNReal.mul_inv_cancel sourceInformationPositive.ne'
            sourceInformationFinite, mul_one]
      have positive : ∃ h ∈ good, h ∈ (source.belief who sourceSite).support := by
        refine ⟨⟨anchor, anchorInfo⟩, anchorGood, ?_⟩
        apply (PMF.mem_support_iff _ _).mpr
        intro absent
        have contradiction := beliefScale ⟨anchor, anchorInfo⟩
        rw [absent, mul_zero] at contradiction
        exact anchorReach.ne' contradiction.symm
      let belief := (source.belief who sourceSite).filter good positive
      have sourceScale (h : setup.proposalRecoveryModel.InformationHistory who sourceSite.1) :
          sourceMass * belief h =
            if setup.proposalRecoveryForeignGood who h.val then
              setup.proposalRecoveryModel.historyReachWeight source.strategy h.val else 0 := by
        have scaledIndicator (h : setup.proposalRecoveryModel.InformationHistory who sourceSite.1) :
            sourceInformationMass * good.indicator (source.belief who sourceSite) h =
              if setup.proposalRecoveryForeignGood who h.val then
                setup.proposalRecoveryModel.historyReachWeight source.strategy h.val else 0 := by
          by_cases member : h ∈ good
          · rw [Set.indicator_of_mem member, beliefScale]
            change setup.proposalRecoveryForeignGood who h.val at member
            rw [ite_eq_left member]
          · rw [Set.indicator_of_notMem member, mul_zero]
            change ¬ setup.proposalRecoveryForeignGood who h.val at member
            rw [ite_eq_right member]
        have scaledMass : sourceMass = sourceInformationMass *
            ∑' h, good.indicator (source.belief who sourceSite) h := by
          rw [← ENNReal.tsum_mul_left]
          exact tsum_congr fun h => (scaledIndicator h).symm
        rw [scaledMass, mul_assoc, filter_mass_mul]
        exact scaledIndicator h
      have factorPositive : 0 < factor := ENNReal.mul_pos ownPositive.ne' classesPositive.ne'
      have factorFinite : factor ≠ ⊤ := ENNReal.mul_ne_top ownFinite classesFinite
      have denominatorPositive : 0 < factor * nativeMass :=
        ENNReal.mul_pos factorPositive.ne' nativeMassPositive.ne'
      have denominatorFinite : factor * nativeMass ≠ ⊤ :=
        ENNReal.mul_ne_top factorFinite nativeMassFinite
      let retainedMass := (factor * nativeMass)⁻¹ * (coefficientMass * sourceMass)
      let complement := nativeMass⁻¹ * (nativeMass - admittedMass)
      have retainedPositive : 0 < retainedMass := by
        exact ENNReal.mul_pos (ENNReal.inv_ne_zero.mpr denominatorFinite)
          (mul_ne_zero coefficientPositive.ne' sourceMassPositive.ne')
      have retainedFinite : retainedMass ≠ ⊤ :=
        ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr denominatorPositive.ne')
          (ENNReal.mul_ne_top coefficientFinite sourceMassFinite)
      have density (value : L.Val payload) (choice : model.Choice who site.1)
          (offered : proper value choice)
          (utility : State L setup.program.terminalCtx → Player → ℝ)
          (excludedPayoff : Player → ℝ) (outcome : Option ℝ) :
          payoff choice utility excludedPayoff outcome =
            retainedMass * sourceCausalPayoff setup values source who sourceSite
              (encode value) positive utility excludedPayoff outcome +
            complement * (PMF.pure (none : Option ℝ)) outcome := by
        let kernel := fun completed : setup.proposalRecoveryProtocol.History =>
          (setup.proposalRecoveryModel.runBehavioralTerminalFrom
            setup.proposalRecoveryProtocol_bounded.wellFoundedHistories
            (sourceUnflaggedStrategy setup values) completed).map fun terminal =>
              some (setup.proposalRecoveryPayoff utility excludedPayoff who terminal)
        let causal := sourceCausalPayoff setup values source who sourceSite
          (encode value) positive utility excludedPayoff
        let cutTerm := fun cut : setup.proposalRecoveryProtocol.History =>
          if same : setup.proposalRecoveryModel.infoOf who cut.trace = sourceSite.1 then
            if setup.proposalRecoveryForeignGood who cut then
              setup.proposalRecoveryModel.historyReachWeight source.strategy cut *
                ((sourceForcedBlock setup values who cut (same.symm ▸ encode value)).bind
                  kernel) outcome
            else 0
          else 0
        have sourceSum : (∑' cut, cutTerm cut) = sourceMass * causal outcome := by
          have supported : Function.support cutTerm ⊆
              {cut | setup.proposalRecoveryModel.infoOf who cut.trace = sourceSite.1} := by
            intro cut nonzero
            by_contra absent
            change setup.proposalRecoveryModel.infoOf who cut.trace ≠ sourceSite.1 at absent
            exact nonzero (by simp only [cutTerm, dite_eq_right absent])
          rw [← tsum_subtype_eq_of_support_subset supported]
          dsimp only [causal]
          rw [sourceCausalPayoff_block setup values source who sourceSite (encode value)
            positive utility excludedPayoff]
          simp only [PMF.map_bind, PMF.bind_apply]
          rw [← ENNReal.tsum_mul_left]
          apply tsum_congr
          intro h
          rw [← mul_assoc, sourceScale]
          have same : setup.proposalRecoveryModel.infoOf who h.val.trace = sourceSite.1 :=
            h.property
          by_cases active : setup.proposalRecoveryForeignGood who h.val
          · simp only [cutTerm, dite_eq_left same, ite_eq_left active, PMF.bind_apply, kernel]
          · simp only [cutTerm, dite_eq_left same, ite_eq_right active, zero_mul]
        have weighted : factor *
            (∑' index : MechanicalIndex setup implementation who,
              ∑' cut : setup.proposalRecoveryProtocol.History,
                ∑' completed : setup.proposalRecoveryProtocol.History,
                  annotatedForcedBlockWeight setup values implementation operational source.strategy
                    native.strategy who site index event payload value cut completed *
                    kernel completed outcome) =
              coefficientMass * sourceMass * causal outcome := by
          calc
            _ = ∑' index : MechanicalIndex setup implementation who,
                coefficient index * ∑' cut, cutTerm cut := by
              rw [← ENNReal.tsum_mul_left]
              apply tsum_congr
              intro index
              simp only [← ENNReal.tsum_mul_left]
              apply tsum_congr
              intro cut
              dsimp only [factor, own, classes]
              simp_rw [← mul_assoc, rectangle index value cut]
              by_cases same : setup.proposalRecoveryModel.infoOf who cut.trace = sourceSite.1
              · by_cases active : setup.proposalRecoveryForeignGood who cut
                · simp only [cutTerm, dite_eq_left same, ite_eq_left active, PMF.bind_apply,
                    mul_assoc, ENNReal.tsum_mul_left, coefficient]
                · simp only [cutTerm, dite_eq_left same, ite_eq_right active, mul_zero,
                    zero_mul, tsum_zero]
              · simp only [cutTerm, dite_eq_right same, mul_zero, zero_mul, tsum_zero]
            _ = coefficientMass * sourceMass * causal outcome := by
              rw [sourceSum, ENNReal.tsum_mul_right]
              dsimp only [coefficientMass]
              ac_rfl
        have nativeEquation := endpoint value choice offered utility excludedPayoff outcome
        apply (ENNReal.mul_right_inj denominatorPositive.ne' denominatorFinite).mp
        calc
          _ = factor * (nativeMass * payoff choice utility excludedPayoff outcome) := by
            rw [mul_assoc]
          _ = coefficientMass * sourceMass * causal outcome +
              factor * ((nativeMass - admittedMass) * (PMF.pure (none : Option ℝ)) outcome) := by
            rw [nativeEquation, mul_add, weighted]
          _ = (factor * nativeMass) *
              (retainedMass * causal outcome +
                complement * (PMF.pure (none : Option ℝ)) outcome) := by
            have retainedCancel : (factor * nativeMass) * retainedMass =
                coefficientMass * sourceMass := by
              change (factor * nativeMass) *
                ((factor * nativeMass)⁻¹ * (coefficientMass * sourceMass)) = _
              rw [← mul_assoc,
                ENNReal.mul_inv_cancel denominatorPositive.ne' denominatorFinite, one_mul]
            have complementCancel : (factor * nativeMass) * complement =
                factor * (nativeMass - admittedMass) := by
              change (factor * nativeMass) *
                (nativeMass⁻¹ * (nativeMass - admittedMass)) = _
              calc
                _ = factor * ((nativeMass * nativeMass⁻¹) *
                    (nativeMass - admittedMass)) := by ac_rfl
                _ = _ := by rw [ENNReal.mul_inv_cancel nativeMassPositive.ne'
                  nativeMassFinite, one_mul]
            symm
            rw [mul_add, ← mul_assoc, retainedCancel, ← mul_assoc, complementCancel]
            ac_rfl
      have normalized : retainedMass + complement = 1 := by
        have summed := congrArg (fun f : Option ℝ → ℝ≥0∞ => ∑' outcome, f outcome)
          (funext (density referenceValue referenceChoice referenceProper
            (fun _ _ => 0) (fun _ => 0)))
        simpa only [PMF.tsum_coe, ENNReal.tsum_add, ENNReal.tsum_mul_left, mul_one]
          using summed.symm
      have retainedBound : retainedMass ≤ 1 := by
        rw [← normalized]
        exact le_add_of_nonneg_right zero_le
      have complementFinite : complement ≠ ⊤ :=
        ne_top_of_le_ne_top ENNReal.one_ne_top (by
          rw [← normalized]
          exact le_add_of_nonneg_left zero_le)
      let retained : Set.Ioc (0 : ℝ) 1 :=
        ⟨retainedMass.toReal, ENNReal.toReal_pos retainedPositive.ne' retainedFinite,
          by
            simpa only [ENNReal.toReal_one] using
              (ENNReal.toReal_mono ENNReal.one_ne_top retainedBound)⟩
      have complementReal : ENNReal.ofReal (1 - retained.val) = complement := by
        have realSum := congrArg ENNReal.toReal normalized
        rw [ENNReal.toReal_add retainedFinite complementFinite, ENNReal.toReal_one] at realSum
        have difference : 1 - retained.val = complement.toReal := by
          change 1 - retainedMass.toReal = complement.toReal
          linarith
        rw [difference, ENNReal.ofReal_toReal complementFinite]
      have mixture (value : L.Val payload) (choice : model.Choice who site.1)
          (offered : proper value choice)
          (utility : State L setup.program.terminalCtx → Player → ℝ)
          (excludedPayoff : Player → ℝ) :
          payoff choice utility excludedPayoff =
            mix retained.val retained.property.1.le retained.property.2
              (sourceCausalPayoff setup values source who sourceSite (encode value) positive
                utility excludedPayoff) (PMF.pure none) := by
        ext outcome
        rw [density value choice offered, mix_apply, complementReal]
        rw [show ENNReal.ofReal retained.val = retainedMass from
          ENNReal.ofReal_toReal retainedFinite]
      refine Or.inr ⟨sourceSite, retained, encode, positive, query, encoded, ordinary, ?_⟩
      intro value choice properChoice
      refine ⟨?_, mixture value choice properChoice⟩
      have readout : (sourceCausalPayoff setup values source who sourceSite (encode value)
          positive (fun _ _ => 0) (fun _ => 0)).map Option.isSome = PMF.pure true := by
        simp only [sourceCausalPayoff, PMF.map_bind, PMF.map_comp, Function.comp_def]
        dsimp only [Option.isSome]
        simp only [PMF.map, Function.comp_def, PMF.bind_const]
      have observed := qualifiedPayoff_isSome setup .concurrent implementation.runtime
        implementation.leaks implementation.bounds implementation.plan implementation.prior
        values native who site choice (fun _ _ => 0) (fun _ => 0)
      have projected := congrArg (PMF.map Option.isSome)
        (mixture value choice properChoice (fun _ _ => 0) (fun _ => 0))
      rw [observed, mix_map, readout, PMF.pure_map] at projected
      have atTrue := congrArg (fun law : PMF Bool => law true) projected
      simp only [mix_apply, Option.isSome, PMF.pure_apply_self,
        PMF.pure_apply_of_ne false true (by decide : true ≠ false), mul_one, mul_zero,
        add_zero] at atTrue
      change (qualificationLaw setup .concurrent implementation.runtime implementation.leaks
        implementation.bounds implementation.plan implementation.prior values native who site
        choice true).toReal = retained.val
      rw [atTrue, ENNReal.toReal_ofReal retained.property.1.le]
  · left
    intro value choice properChoice
    exact False.elim (offered ⟨value, choice, properChoice⟩)


end Vegas.PhaseProposalQualifiedBinding
