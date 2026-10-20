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
import Vegas.Game.ProposalRecoveryPools
import Vegas.Game.PhaseProposalAttemptArchive
import GameTheory.Protocol.Predraw
import Interaction.ReactiveAnchoredStopped

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
local notation "initial" =>
  PMF.map (PhaseRuntimeState.initial plan) (PMF.map encodeInputs setup.initialLaw)
local notation "horizon" => ReservedEpoch.executionHorizon runtime
local notation "scheduler" => ReactiveApplication.SchedulerImplementation.scheduler
  (ReservedEpoch.implementation runtime leaks (ReservedEpoch.packetCapacity runtime) prior)
local notation "E" => ReactiveApplication.ResponseMenu.protocol
  (PhaseCount.onePacketMenu runtime leaks bounds) initial horizon scheduler
local notation "N" => ReactiveApplication.ResponseMenu.information
  (PhaseCount.onePacketMenu runtime leaks bounds) initial horizon scheduler

/-- Zero future flags use the original ordinary value table. -/
def unflaggedStrategy
    (values : ∀ who (key : setup.ProposalRecoveryComponent who),
      PMF (setup.CommitRecoveryValueChoice who key.1)) :
    ∀ who, (N).BehavioralPolicy who :=
  fun who => (menu).restrictPolicy initial horizon scheduler who
    (phaseProposalUnflaggedPolicy setup mode runtime leaks bounds plan values who)

variable (values : ∀ who (key : setup.ProposalRecoveryComponent who),
  PMF (setup.CommitRecoveryValueChoice who key.1))

local notation "clean" => unflaggedStrategy setup mode runtime leaks bounds plan prior values

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

open Classical in
/-- One actual response, with the chosen atom committed at this history's
actual information. Subsequent play is defined separately. -/
def currentStep (who : Player) (history : (E).History)
    (choice : (N).Choice who ((N).infoOf who history.trace)) : PMF (E).History :=
  (N).runBehavioralFrom
    (Profile.update (sig := (N).behavioralSignature) clean who
      ((clean who).commit ((N).infoOf who history.trace) choice)) 1 history

/-- The literal atom has exactly its native physical response image. -/
theorem currentStep_state (who : Player) (history : (E).History)
    (choice : (N).Choice who ((N).infoOf who history.trace))
    (remaining : Nat) (execution : (app).Execution)
    (current : history.state = some ⟨remaining, some who, execution⟩)
    (response : (app).Action) (selected : choice.1 = some response) :
    (currentStep setup mode runtime leaks bounds plan prior values who history choice).map
      History.state = PMF.pure (some ⟨remaining, none, execution.respond app who response⟩) := by
  exact (menu).run_commit_response initial horizon scheduler clean history who remaining
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
      ((N).runBehavioralUntil ((menu).bounded initial horizon scheduler).wellFoundedHistories clean
        (attemptExit setup mode runtime leaks bounds plan prior history) after).bind fun stop =>
          ((N).runBehavioralTerminalFrom
            ((menu).bounded initial horizon scheduler).wellFoundedHistories clean stop).map
              fun terminal => (stop, terminal)

/-- Erasing the recorded exit gives exactly the original postresponse terminal
law. In particular stopping does not redraw a tape or an initial input. -/
theorem stoppedFinish_terminal (who : Player) (history : (E).History)
    (choice : (N).Choice who ((N).infoOf who history.trace)) :
    (stoppedFinish setup mode runtime leaks bounds plan prior values who history choice).map
        Prod.snd =
      (currentStep setup mode runtime leaks bounds plan prior values who history choice).bind
        ((N).runBehavioralTerminalFrom
          ((menu).bounded initial horizon scheduler).wellFoundedHistories clean) := by
  unfold stoppedFinish
  rw [PMF.map_bind]
  apply bind_congr_on_support
  intro after _
  rw [PMF.map_bind]
  calc
    _ = ((N).runBehavioralUntil
        ((menu).bounded initial horizon scheduler).wellFoundedHistories clean
        (attemptExit setup mode runtime leaks bounds plan prior history) after).bind
          ((N).runBehavioralTerminalFrom
            ((menu).bounded initial horizon scheduler).wellFoundedHistories clean) := by
      apply bind_congr_on_support
      intro stop _
      calc
        _ = ((N).runBehavioralTerminalFrom
            ((menu).bounded initial horizon scheduler).wellFoundedHistories clean stop).map id :=
          PMF.map_comp _ _ _
        _ = _ := PMF.map_id _
    _ = _ := ((N).runBehavioralTerminalFrom_eq_bind_runBehavioralUntil
      ((menu).bounded initial horizon scheduler).wellFoundedHistories clean
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
        ((menu).decodeProfile initial horizon scheduler clean)
        (some ⟨remaining, none, execution.respond app who response⟩) := by
  calc
    _ = ((stoppedFinish setup mode runtime leaks bounds plan prior values who history choice).map
        Prod.snd).map History.state := (PMF.map_comp _ _ _).symm
    _ = _ := by
      rw [stoppedFinish_terminal]
      exact phaseProposal_response_kernel_finish setup mode runtime leaks bounds plan prior clean
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
          ((menu).decodeProfile initial horizon scheduler clean)
          (some ⟨remaining, none, execution.respond app who response⟩) := by
  rw [stoppedFinish_state setup mode runtime leaks bounds plan prior values who history choice
    remaining execution current response selected]
  simpa only [PMF.pure_bind] using
    (phaseProposal_current_finish_seed_marginal setup mode runtime leaks plan prior
      ((menu).decodeProfile initial horizon scheduler clean) remaining who execution
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
      before ending priorTrace raw effect changed
  have record := (receipts.exclusion.installed phase (by
    simpa only using installed)).phase_drain phase
  rintro ⟨owner, member⟩
  have excluded := Finset.mem_sdiff.mp (Finset.mem_inter.mp member).1
  rcases (record.excluded owner).mp excluded.1 with inherited |
      ⟨event, lower, acting, failed⟩
  · exact excluded.2 inherited
  · have read := ReservedEpoch.original_binding_publicFailure_iff runtime leaks
      (serviceGraph_revealRelaxedOrdered setup mode) plan (setup.initialLaw.map encodeInputs)
      horizon scheduler before ((menu).toRawTrace initial horizon scheduler priorTrace)
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
  have initialEq : initial = setup.initialLaw.map
      (fun draw => PhaseRuntimeState.initial plan (encodeInputs draw)) := PMF.map_comp _ _ _
  have counted : ((menu).protocol
      (setup.initialLaw.map fun draw => PhaseRuntimeState.initial plan (encodeInputs draw))
      horizon scheduler).Trace (some before) := by
    rw [← initialEq]
    exact priorTrace
  obtain ⟨witness, archived⟩ := recoverySourceCheckpoint_proposalArchive_history setup mode runtime
    leaks bounds plan maximal horizon scheduler counted
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
    ((menu).toRawTrace initial horizon scheduler priorTrace)).2.2
  obtain ⟨native, binding, receipts, stored, remembered, coverage⟩ :=
    phaseClosingEffect_checkpoint_facts setup mode runtime leaks bounds plan horizon scheduler
      before ending priorTrace raw effect changed
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

/-- The source continuation uses the same ordinary table with all three future
flag rates set to zero. Its past belief is supplied by the actual assessment. -/
def sourceUnflaggedStrategy : ∀ who, setup.proposalRecoveryModel.BehavioralPolicy who :=
  setup.proposalRecoveryNormalizedTrembledProfile
    0 le_rfl zero_le_one 0 le_rfl zero_le_one 0 le_rfl zero_le_one values

omit values in
/-- The source qualification retains generated preparations in canceled
attempts; only foreign generated preparation failures are filtered. -/
def sourceForeignGood (who : Player) (history : setup.proposalRecoveryProtocol.History) : Prop :=
  ∀ owner, owner ≠ who → ¬ setup.GeneratedPreparationHistory owner history

open Classical in
/-- Causally insert the selected source atom and then use the zero-flag
continuation. This never conditions a baseline future on the selected value. -/
def sourceCausalPayoff (assessment : setup.proposalRecoveryModel.BehavioralAssessment)
    (who : Player) (site : setup.proposalRecoveryModel.InformationSite who)
    (choice : setup.proposalRecoveryModel.Choice who site.1)
    (positive : ∃ history ∈
        {history : setup.proposalRecoveryModel.InformationHistory who site.1 |
          sourceForeignGood setup who history.val},
      history ∈ (assessment.belief who site).support)
    (utility : State L setup.program.terminalCtx → Player → ℝ)
    (excludedPayoff : Player → ℝ) : PMF (Option ℝ) :=
  let profile := sourceUnflaggedStrategy setup values
  let sourceCertificate := setup.proposalRecoveryProtocol_bounded.wellFoundedHistories
  ((assessment.belief who site).filter
      {history | sourceForeignGood setup who history.val} positive).bind fun history =>
    ((setup.proposalRecoveryModel.runBehavioralFrom
      (Profile.update (sig := setup.proposalRecoveryModel.behavioralSignature) profile who
        ((profile who).commit site.1 choice)) 1 history.val).bind
      (setup.proposalRecoveryModel.runBehavioralTerminalFrom sourceCertificate profile)).map
        (fun terminal => some (setup.proposalRecoveryPayoff utility excludedPayoff who terminal))

end Vegas.PhaseProposalQualifiedBinding
