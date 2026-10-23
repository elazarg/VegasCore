/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseProposalCurrentBindingGain
import GameTheoryExtensions.Math.Probability.NestedPosterior
import GameTheory.Math.Probability.FiniteSampling
import Vegas.Game.PhaseProposalNativeSourceInformation
import Vegas.Game.ProposalRecoveryPools
import GameTheory.Protocol.Predraw
import Interaction.ReactiveSchedulerStoppedSeed
import Vegas.Pending.ReservedEpochService
import Vegas.Pending.PhaseBindingMemoryCallback
import Vegas.Source.CommitPrefixProduct
import Vegas.Game.AsyncDeviationForeign

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
theorem closing_all_admitted_excluded_eq
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
theorem word_action_commit
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
theorem source_word_strategy_table
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
theorem source_word_cut_mask_excluded
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
theorem source_word_run_conditioned
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

section IssuedCylinders

open scoped ENNReal

variable (implementation : ReservedConcurrentImplementation setup)

local notation "nativeApplication" => implementation.application
local notation "nativeMenu" => PhaseCount.onePacketMenu implementation.runtime
  implementation.leaks implementation.bounds
local notation "nativeInitial" => implementation.initial
local notation "nativeProtocol" => ReactiveApplication.ResponseMenu.protocol
  nativeMenu nativeInitial implementation.horizon implementation.scheduler

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
/-- The original foreign issued cylinder has the product of its owner-word
masses at the same source entry. The focal owner contributes the sure event. -/
theorem ordinaryForeignJoint_issued_mass
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
      let profile := ordinaryBlockProfile setup .concurrent implementation.plan values block.block
        block.suffix cursor.embedding (fun owner view => cursor.views.view owner view)
          (control.execution.application.entry.excluded,
            control.execution.application.generation, control.execution.application.attempt.phase)
          control.execution.application.publicView
          (PhaseProposal.sourceArchive control.execution.network.inputs)
      let law := block.block.prefixLaw block.suffix profile cursor.source
      ((ordinaryForeignJoint setup values implementation operational who ⟨some control, trace⟩
        ⟨some cursor.current, cursor.trace⟩).map Prod.snd) true =
        ∏ owner, if owner = who then 1 else
          ((law.map (SourceProgram.Config.view owner)).map (fun word => decide (
            issuedLedger setup implementation block.block
              control.execution.application.attempt.phase control
                (control.execution.application.attempt.phase + block.block.length)
                owner word))) true := by
  classical
  intro checkpoint block cursor positive embedding lift views profile law
  let laws := fun owner => law.map (SourceProgram.Config.view owner)
  let restriction := fun owner => {word | owner ≠ who → issuedLedger setup implementation
    block.block control.execution.application.attempt.phase control
      (control.execution.application.attempt.phase + block.block.length) owner word}
  have wholeMass :
      (law.map (fun final => decide (∀ owner, owner ≠ who → issuedLedger setup implementation
        block.block control.execution.application.attempt.phase control
          (control.execution.application.attempt.phase + block.block.length)
            owner (final.view owner)))) true =
        (law.map (fun final owner => final.view owner)).toOuterMeasure
          (Set.pi Set.univ restriction) := by
    rw [← PMF.toOuterMeasure_apply_singleton, PMF.toOuterMeasure_map_apply,
      PMF.toOuterMeasure_map_apply]
    congr 1
    ext final
    change decide (∀ owner, owner ≠ who → issuedLedger setup implementation
      block.block control.execution.application.attempt.phase control
        (control.execution.application.attempt.phase + block.block.length)
          owner (final.view owner)) = true ↔
      ∀ owner, owner ∈ Set.univ → owner ≠ who → issuedLedger setup implementation
        block.block control.execution.application.attempt.phase control
          (control.execution.application.attempt.phase + block.block.length)
            owner (final.view owner)
    rw [decide_eq_true_eq]
    exact ⟨fun retained owner _ => retained owner,
      fun retained owner => retained owner (Set.mem_univ owner)⟩
  have coordinateMass (owner : Player) :
      (laws owner).toOuterMeasure (restriction owner) =
        if owner = who then 1 else
          ((laws owner).map (fun word => decide (issuedLedger setup implementation block.block
            control.execution.application.attempt.phase control
              (control.execution.application.attempt.phase + block.block.length)
                owner word))) true := by
    by_cases same : owner = who
    · subst owner
      simp only [ite_true]
      apply ((laws who).toOuterMeasure_apply_eq_one_iff _).mpr
      intro word _supported different
      exact (different rfl).elim
    · simp only [same, ite_false]
      conv_rhs => rw [← PMF.toOuterMeasure_apply_singleton, PMF.toOuterMeasure_map_apply]
      apply congrArg (laws owner).toOuterMeasure
      ext word
      change (owner ≠ who → issuedLedger setup implementation block.block
        control.execution.application.attempt.phase control
          (control.execution.application.attempt.phase + block.block.length) owner word) ↔
        decide (issuedLedger setup implementation block.block
          control.execution.application.attempt.phase control
            (control.execution.application.attempt.phase + block.block.length) owner word) = true
      rw [decide_eq_true_eq]
      exact ⟨fun retained => retained same, fun retained _ => retained⟩
  rw [ordinaryForeignJoint_of_selected_cursor setup values implementation operational who control
    trace phase cursor positive embedding lift views, PMF.map_comp]
  change (law.map (fun final => decide (∀ owner, owner ≠ who → issuedLedger setup implementation
    block.block control.execution.application.attempt.phase control
      (control.execution.application.attempt.phase + block.block.length)
        owner (final.view owner)))) true = _
  rw [wholeMass, block.block.prefixLaw_views_product block.suffix profile cursor.source,
    independentProduct_outerMeasure_pi]
  exact Finset.prod_congr rfl fun owner _ => coordinateMass owner

open Classical in
/-- The proper typed draw at one literal binding callback. Silent callbacks
and nonbinding packets contribute one; the queried law uses this actual input. -/
def sourceReplayBindingDrawAtom
    (owner : Player) (past : List (nativeApplication).PlayerEntry)
    (view : (nativeApplication).PlayerView) (action : (nativeApplication).Action) : ℝ≥0∞ :=
  match action.transmission with
  | none => 1
  | some material => match material.call.packet with
    | .commitment event _ => match PhaseProposal.bindingPreparation material with
      | none => 0
      | some ⟨payload, value⟩ =>
        if binding : (serviceGraph setup .concurrent).outputLayout event = .binding owner payload
          then match phaseProposalQuery? setup .concurrent implementation.runtime
              implementation.leaks implementation.plan owner event past view with
          | none => 0
          | some key => ((values owner key).map (fun choice => phaseRecoveryDomainValue setup
              .concurrent event owner payload binding choice.val.val)) value
        else 0
    | .opening .. | .malformed .. => 1

open Classical in
/-- The typed draws at the actual foreign registrations in the final signed
attempt. Each factor reads its literal earlier own recall and callback view. -/
def sourceReplayCurrentIssuedProduct (who : Player) (history : (nativeProtocol).History) :
    ℝ≥0∞ :=
  match history.state with
  | none => 1
  | some control => ∏ owner, if owner = who then 1 else
      (((control.execution.recall owner).zipIdx).map fun indexed =>
        match indexed.1.emitted with
        | none => 1
        | some message =>
            if message.payload.attempt = control.execution.application.attempt then
              match message.payload.packet.call with
              | .commitment _ _ => sourceReplayBindingDrawAtom setup values implementation owner
                  ((control.execution.recall owner).take indexed.2)
                    indexed.1.beforeView indexed.1.action
              | .opening .. | .malformed .. => 1
            else 1).prod

open Classical in
/-- The static slot addressed by one actual recalled registration in the
current signed attempt. The owner and interval tests are the ledger's tests. -/
def sourceIssuedRecordPosition
    {Γ Δ : SourceCtx Player L} {O P : Finset VarId}
    (block : SourceProgram.CommitPrefix Γ O Δ P) (low : Nat)
    (control : (nativeApplication).Control) (owner : Player)
    (record : (nativeApplication).PlayerEntry) : Option Nat :=
  match record.emitted with
  | none => none
  | some message =>
      if message.payload.attempt = control.execution.application.attempt then
        match message.payload.packet.call with
        | .commitment named _ =>
            if low ≤ named.val ∧ named.val < low + block.length ∧
                ∃ payload, (serviceGraph setup .concurrent).outputLayout named =
                  .binding owner payload then some (named.val - low) else none
        | .opening .. | .malformed .. => none
      else none

/-- The literal source actions fixed by the first recalled registrations.
The complete source word and its law stay fixed as the observation grows. -/
def sourceIssuedOwnObservation
    {Γ Δ : SourceCtx Player L} {O P : Finset VarId}
    (block : SourceProgram.CommitPrefix Γ O Δ P) (low : Nat)
    (control : (nativeApplication).Control) (owner : Player)
    (reference : DecisionView owner Δ) (count : Nat) (word : DecisionView owner Δ) : Prop :=
  ∀ record ∈ (control.execution.recall owner).take count, ∀ position,
    sourceIssuedRecordPosition setup implementation block low control owner record = some position →
      block.wordAction owner position word = block.wordAction owner position reference

open Classical in
/-- The current foreign source product uses the chronological conditional
owner kernels of the original complete ordinary word law. -/
def sourceReplayIssuedSourceProduct
    {Γ Δ : SourceCtx Player L} {O P : Finset VarId}
    (block : SourceProgram.CommitPrefix Γ O Δ P) (suffix : SourceProgram Player L Δ P)
    (profile : SourceProgram.BehavioralProfile (block.prepend suffix))
    (entry : SourceProgram.Config Player L Γ) (low : Nat)
    (control : (nativeApplication).Control) (focal : Player)
    (reference : SourceProgram.Config Player L Δ) : ℝ≥0∞ :=
  ∏ owner, if owner = focal then 1 else
    ∏ index ∈ Finset.range (control.execution.recall owner).length,
      match (control.execution.recall owner)[index]? with
      | none => 1
      | some record =>
          match sourceIssuedRecordPosition setup implementation block low control owner record with
          | none => 1
          | some position =>
              ((fiberPosterior
                ((block.prefixLaw suffix profile entry).map (SourceProgram.Config.view owner))
                (fun word => decide (sourceIssuedOwnObservation setup implementation block low
                  control owner (reference.view owner) index word)) true).map
                    (block.wordAction owner position))
                  (block.wordAction owner position (reference.view owner))

/-- On the actual emitted ledger, its source action constraints are exactly
the constraints retained by the complete recalled-registration observation. -/
theorem issuedLedger_iff_recalled_word_actions
    {Γ Δ : SourceCtx Player L} {O P : Finset VarId}
    (block : SourceProgram.CommitPrefix Γ O Δ P) (suffix : SourceProgram Player L Δ P)
    (embedding : OutputEmbedding (inputLayout setup.context) (outputLayout setup.program)
      (block.prepend suffix)) (low : Nat)
    (rank : ∀ index, (embedding.event index).val = low + index.val)
    (actions : ∀ index action, decodeEventAction setup.program (embedding.event index) action =
      decodeEventAction (block.prepend suffix) index
        (cast (congrArg EventField.Action (embedding.layout_eq index)) action))
    {control : (nativeApplication).Control} (trace : (nativeProtocol).Trace (some control))
    (owner : Player) (reference word : DecisionView owner Δ)
    (retained : issuedLedger setup implementation block low control (low + block.length)
      owner reference) :
    issuedLedger setup implementation block low control (low + block.length) owner word ↔
      sourceIssuedOwnObservation setup implementation block low control owner reference
        (control.execution.recall owner).length word := by
  rw [issuedLedger_iff_actions setup implementation block suffix embedding low rank actions
    trace owner reference word retained]
  unfold sourceIssuedOwnObservation
  rw [List.take_length]
  constructor
  · intro agrees record member position indexed
    unfold sourceIssuedRecordPosition at indexed
    cases emitted : record.emitted with
    | none => simp only [emitted] at indexed; cases indexed
    | some message =>
        simp only [emitted] at indexed
        split at indexed
        · rename_i sameAttempt
          cases call : message.payload.packet.call with
          | malformed | opening => simp only [call] at indexed; cases indexed
          | commitment named candidate =>
              simp only [call] at indexed
              split at indexed
              · rename_i admitted
                obtain ⟨lower, upper, payload, shape⟩ := admitted
                have samePosition : named.val - low = position := Option.some.inj indexed
                rw [← samePosition]
                exact agrees named payload shape candidate message
                  (List.mem_filterMap.mpr ⟨record, member, emitted⟩) sameAttempt call ⟨lower, upper⟩
              · cases indexed
        · cases indexed
  · intro agrees named payload shape candidate message emitted sameAttempt call interval
    obtain ⟨record, member, emittedRecord⟩ := List.mem_filterMap.mp emitted
    have indexed : sourceIssuedRecordPosition setup implementation block low control owner
        record = some (named.val - low) := by
      unfold sourceIssuedRecordPosition
      rw [emittedRecord]
      simp only [sameAttempt, ite_true, call]
      exact ite_eq_left ⟨interval.1, interval.2, payload, shape⟩
    exact agrees record member _ indexed

open Classical in
/-- Each actual issued owner cylinder has its chronological conditional word mass.
The complete prior and its supported reference word stay fixed throughout. -/
theorem issuedLedger_owner_cylinder_telescope
    {Γ Δ : SourceCtx Player L} {O P : Finset VarId}
    (block : SourceProgram.CommitPrefix Γ O Δ P) (suffix : SourceProgram Player L Δ P)
    (embedding : OutputEmbedding (inputLayout setup.context) (outputLayout setup.program)
      (block.prepend suffix)) (low : Nat)
    (rank : ∀ index, (embedding.event index).val = low + index.val)
    (actions : ∀ index action, decodeEventAction setup.program (embedding.event index) action =
      decodeEventAction (block.prepend suffix) index
        (cast (congrArg EventField.Action (embedding.layout_eq index)) action))
    {control : (nativeApplication).Control} (trace : (nativeProtocol).Trace (some control))
    (profile : SourceProgram.BehavioralProfile (block.prepend suffix))
    (entry : SourceProgram.Config Player L Γ) (owner : Player)
    (reference : SourceProgram.Config Player L Δ)
    (supported : reference ∈ (block.prefixLaw suffix profile entry).support)
    (retained : issuedLedger setup implementation block low control
      (low + block.length) owner (reference.view owner)) :
    ((((block.prefixLaw suffix profile entry).map (SourceProgram.Config.view owner)).map
      (fun word => decide (issuedLedger setup implementation block low control
        (low + block.length) owner word))) true) =
      ∏ index ∈ Finset.range (control.execution.recall owner).length,
        match (control.execution.recall owner)[index]? with
        | none => 1
        | some record =>
            match sourceIssuedRecordPosition setup implementation block low control owner
                record with
            | none => 1
            | some position =>
                ((fiberPosterior
                  ((block.prefixLaw suffix profile entry).map (SourceProgram.Config.view owner))
                  (fun word => decide (sourceIssuedOwnObservation setup implementation block low
                    control owner (reference.view owner) index word)) true).map
                      (block.wordAction owner position))
                    (block.wordAction owner position (reference.view owner)) := by
  classical
  let law := (block.prefixLaw suffix profile entry).map (SourceProgram.Config.view owner)
  let past := control.execution.recall owner
  let observe := fun count word => decide (sourceIssuedOwnObservation setup implementation
    block low control owner (reference.view owner) count word)
  let atom : Nat → ℝ≥0∞ := fun index => match past[index]? with
    | none => 1
    | some record =>
        match sourceIssuedRecordPosition setup implementation block low control owner record with
        | none => 1
        | some position => ((fiberPosterior law (observe index) true).map
            (block.wordAction owner position))
              (block.wordAction owner position (reference.view owner))
  have referenceSupport : reference.view owner ∈ law.support :=
    (PMF.mem_support_map_iff _ _ _).mpr ⟨reference, supported, rfl⟩
  have referenceMatches (count : Nat) : observe count (reference.view owner) = true := by
    apply decide_eq_true
    intro _record _member _position _indexed
    rfl
  have matchesStep (index : Nat) (inside : index < past.length) (word : DecisionView owner Δ) :
      sourceIssuedOwnObservation setup implementation block low control owner
          (reference.view owner) (index + 1) word ↔
        sourceIssuedOwnObservation setup implementation block low control owner
          (reference.view owner) index word ∧
        (∀ position, sourceIssuedRecordPosition setup implementation block low control owner
            past[index] = some position →
          block.wordAction owner position word =
            block.wordAction owner position (reference.view owner)) := by
    unfold sourceIssuedOwnObservation
    change (∀ record ∈ past.take (index + 1), _) ↔ _
    rw [List.take_succ_eq_append_getElem inside]
    constructor
    · intro next
      refine ⟨?_, ?_⟩
      · intro record member position indexed
        exact next record (List.mem_append_left _ member) position indexed
      · intro position indexed
        exact next past[index] (List.mem_append_right _ (List.mem_singleton_self _))
          position indexed
    · rintro ⟨previous, next⟩ record member position indexed
      rcases List.mem_append.mp member with earlier | last
      · exact previous record earlier position indexed
      · have sameRecord : record = past[index] := List.mem_singleton.mp last
        subst record
        exact next position indexed
  have mass : ∀ count ≤ past.length,
      (law.map (observe count)) true = ∏ index ∈ Finset.range count, atom index := by
    intro count
    induction count with
    | zero =>
        intro _bounded
        have all : observe 0 = fun _ => true := by
          funext word
          apply decide_eq_true
          intro record member
          cases member
        rw [all, Finset.prod_range_zero]
        change (law.map (Function.const _ true)) true = 1
        rw [PMF.map_const, PMF.pure_apply_self]
    | succ count ih =>
        intro bounded
        have inside : count < past.length := by omega
        have previous := ih (by omega)
        have possible : true ∈ (law.map (observe count)).support :=
          (PMF.mem_support_map_iff _ _ _).mpr
            ⟨reference.view owner, referenceSupport, referenceMatches count⟩
        have current : past[count]? = some past[count] := List.getElem?_eq_getElem inside
        cases indexed : sourceIssuedRecordPosition setup implementation block low control
            owner past[count] with
        | none =>
            have same : observe (count + 1) = observe count := by
              funext word
              apply decide_eq_decide.mpr
              rw [matchesStep count inside word]
              constructor
              · exact And.left
              · intro earlier
                refine ⟨earlier, ?_⟩
                intro position impossible
                rw [indexed] at impossible
                cases impossible
            rw [same, previous, Finset.prod_range_succ]
            simp only [atom, current, indexed, mul_one]
        | some position =>
            have increment := observation_fiber_mass law (observe count) (observe (count + 1))
              (block.wordAction owner position)
              (block.wordAction owner position (reference.view owner)) possible (by
                intro word _drawn
                rw [decide_eq_true_eq, decide_eq_true_eq, matchesStep count inside word]
                constructor
                · rintro ⟨old, next⟩
                  exact ⟨old, next position indexed⟩
                · rintro ⟨old, next⟩
                  refine ⟨old, ?_⟩
                  intro selected selectedAt
                  have samePosition : position = selected :=
                    Option.some.inj (indexed.symm.trans selectedAt)
                  exact samePosition ▸ next)
            rw [increment, previous, Finset.prod_range_succ]
            simp only [atom, current, indexed]
  have ledger : (fun word => decide (issuedLedger setup implementation block low control
      (low + block.length) owner word)) = observe past.length := by
    funext word
    exact decide_eq_decide.mpr (issuedLedger_iff_recalled_word_actions setup implementation
      block suffix embedding low rank actions trace owner (reference.view owner) word
        retained)
  change (law.map _) true = ∏ index ∈ Finset.range past.length, atom index
  rw [ledger]
  exact mass _ le_rfl

open Classical in
/-- A supported complete source word witnesses every earlier issued cylinder.
Successive actual registrations therefore multiply their chronological owner
atoms without dividing by a possibly zero mass. -/
theorem issuedLedger_foreign_cylinder_telescope
    {Γ Δ : SourceCtx Player L} {O P : Finset VarId}
    (block : SourceProgram.CommitPrefix Γ O Δ P) (suffix : SourceProgram Player L Δ P)
    (embedding : OutputEmbedding (inputLayout setup.context) (outputLayout setup.program)
      (block.prepend suffix)) (low : Nat)
    (rank : ∀ index, (embedding.event index).val = low + index.val)
    (actions : ∀ index action, decodeEventAction setup.program (embedding.event index) action =
      decodeEventAction (block.prepend suffix) index
        (cast (congrArg EventField.Action (embedding.layout_eq index)) action))
    {control : (nativeApplication).Control} (trace : (nativeProtocol).Trace (some control))
    (profile : SourceProgram.BehavioralProfile (block.prepend suffix))
    (entry : SourceProgram.Config Player L Γ) (focal : Player)
    (reference : SourceProgram.Config Player L Δ)
    (supported : reference ∈ (block.prefixLaw suffix profile entry).support)
    (retained : ∀ owner, owner ≠ focal → issuedLedger setup implementation block low control
      (low + block.length) owner (reference.view owner)) :
    ∏ owner, (if owner = focal then 1 else
      (((block.prefixLaw suffix profile entry).map (SourceProgram.Config.view owner)).map
        (fun word => decide (issuedLedger setup implementation block low control
          (low + block.length) owner word))) true) =
      sourceReplayIssuedSourceProduct setup implementation block suffix profile entry low control
        focal reference := by
  classical
  unfold sourceReplayIssuedSourceProduct
  apply Finset.prod_congr rfl
  intro owner _member
  by_cases own : owner = focal
  · simp only [own, ite_true]
  · simp only [own, ite_false]
    exact issuedLedger_owner_cylinder_telescope setup implementation block suffix embedding low
      rank actions trace profile entry owner reference supported (retained owner own)

open Classical in
/-- The true-bit mass of the original foreign joint is its finite chronological
issued-owner product at the same pulled source entry. -/
theorem ordinaryForeignJoint_issued_source_product
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
      let profile := ordinaryBlockProfile setup .concurrent implementation.plan values block.block
        block.suffix cursor.embedding (fun owner view => cursor.views.view owner view)
          (control.execution.application.entry.excluded,
            control.execution.application.generation, control.execution.application.attempt.phase)
          control.execution.application.publicView
          (PhaseProposal.sourceArchive control.execution.network.inputs)
      ∀ reference : SourceProgram.Config Player L block.context,
        reference ∈ (block.block.prefixLaw block.suffix profile cursor.source).support →
        (∀ owner, owner ≠ who → issuedLedger setup implementation block.block
          control.execution.application.attempt.phase control
            (control.execution.application.attempt.phase + block.block.length) owner
              (reference.view owner)) →
        ((ordinaryForeignJoint setup values implementation operational who ⟨some control, trace⟩
          ⟨some cursor.current, cursor.trace⟩).map Prod.snd) true =
          sourceReplayIssuedSourceProduct setup implementation block.block block.suffix profile
            cursor.source control.execution.application.attempt.phase control who reference := by
  intro checkpoint block cursor positive embedding lift views profile reference supported retained
  have offset : cursor.offset = control.execution.application.attempt.phase := by
    have sourceCount := cursor.compiled.countEq
    have selectedCount := checkpoint.compiled.countEq
    have reconstructed : eventCount (block.block.prepend block.suffix) =
        eventCount checkpoint.residual.tail := congrArg eventCount block.reconstruct
    omega
  have rank : ∀ index, (cursor.embedding.event index).val =
      control.execution.application.attempt.phase + index.val := by
    intro index
    rw [cursor.compiled.rankEq, offset]
  rw [ordinaryForeignJoint_issued_mass setup values implementation operational who control trace
    phase cursor positive embedding lift views]
  exact issuedLedger_foreign_cylinder_telescope setup implementation block.block block.suffix
    cursor.embedding control.execution.application.attempt.phase rank cursor.views.actionEq
      trace profile cursor.source who reference supported retained

end IssuedCylinders

end Vegas.PhaseProposalQualifiedBinding
