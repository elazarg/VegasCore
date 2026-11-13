module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Game.ClientSpecification
public import Vegas.Game.OnePacketContinuationPayoff

@[expose] public section

/-! # Audited native and physical continuations with actual settled payoff -/

noncomputable section

namespace Vegas

open SourceProgram Interaction EventGraphRuntime GameTheory GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Protocol.InformationModel
  GameTheory.Math.Probability GameTheory.Enforcement

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)} {timeouts : EventTimeouts (graph setup)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
  {bounds : MessageBounds (graph setup)} {horizon : Nat}
  {scheduler : (application setup timeouts leaks).Scheduler}
  {Parameter : Type} {parameter : State L setup.context → Parameter}
  {utility : Parameter × PublicOutcome setup.program → Player → ℝ}
  {excludedPayoff : Player → ℝ}

local notation "Initial" => initialLaw setup
local notation "app" => application setup timeouts leaks
local notation "one" => bounds.onePacketMenu timeouts leaks
local notation "raw" => bounds.rawMenu timeouts leaks
local notation "N" => onePacketModel setup timeouts leaks bounds Initial horizon scheduler
local notation "R" => ReactiveApplication.ResponseMenu.information
  (bounds.rawMenu timeouts leaks) (initialLaw setup) horizon scheduler
local notation "EP" => ReactiveApplication.ResponseMenu.protocol
  (bounds.onePacketMenu timeouts leaks) (initialLaw setup) horizon scheduler
local notation "RP" => ReactiveApplication.ResponseMenu.protocol
  (bounds.rawMenu timeouts leaks) (initialLaw setup) horizon scheduler

/-- Every represented raw continuation is free of audit charges and retains
the complete normalized terminal history jointly with its realized settlement. -/
theorem ClientAssessmentRefinement.continuation_settlement
    (spec : ClientSpec setup timeouts leaks bounds horizon scheduler
      parameter utility excludedPayoff)
    {intended : setup.intendedModel.BehavioralAssessment} {target : (R).BehavioralAssessment}
    (refinement : ClientAssessmentRefinement setup timeouts leaks bounds horizon scheduler
      intended target)
    (nativeStart : (EP).History) (rawStart : (RP).History)
    (same : ((reactiveNormalization timeouts) leaks).history (raw)
      (bounds.rawMenu_recall timeouts leaks) Initial horizon scheduler rawStart =
      (bounds.onePacketRestriction timeouts leaks Initial horizon scheduler).history nativeStart) :
    (∀ final ∈ ((raw).runFrom Initial horizon scheduler target.strategy rawStart).support,
      ∀ who, TerminalAudit.charge (app).stateTraffic
        ((countAudit timeouts) leaks spec.evidenceService.sample) final.state who = 0) ∧
    ((raw).runFrom Initial horizon scheduler target.strategy rawStart).bind (fun final =>
      (spec.settlement final.state).map fun payoffs =>
        (((reactiveNormalization timeouts) leaks).history (raw)
          (bounds.rawMenu_recall timeouts leaks) Initial horizon scheduler final, payoffs)) =
      ((one).runFrom Initial horizon scheduler refinement.native.strategy nativeStart).map
        (fun final =>
          ((bounds.onePacketRestriction timeouts leaks Initial horizon scheduler).history final,
            exclusionBase setup timeouts parameter utility excludedPayoff leaks final.state)) := by
  let normalize := ((reactiveNormalization timeouts) leaks).history (raw)
    (bounds.rawMenu_recall timeouts leaks) Initial horizon scheduler
  let embed := (bounds.onePacketRestriction timeouts leaks Initial horizon scheduler).history
  let nativeRun := (one).runFrom Initial horizon scheduler refinement.native.strategy nativeStart
  let rawRun := (raw).runFrom Initial horizon scheduler target.strategy rawStart
  let base := exclusionBase setup timeouts parameter utility excludedPayoff leaks
  have histories : rawRun.map normalize = nativeRun.map embed :=
    refinement.continuation nativeStart rawStart same
  have chargeZero (final : (RP).History) (supported : final ∈ rawRun.support) (who : Player) :
      TerminalAudit.charge (app).stateTraffic
        ((countAudit timeouts) leaks spec.evidenceService.sample) final.state who = 0 := by
    have member : normalize final ∈ (nativeRun.map embed).support := by
      rw [← histories]
      exact (PMF.mem_support_map_iff _ _ _).mpr ⟨final, supported, rfl⟩
    obtain ⟨sourceFinal, _sourceSupported, sourceEq⟩ := (PMF.mem_support_map_iff _ _ _).mp member
    have stateEq : sourceFinal.state = ((reactiveNormalization timeouts) leaks).state
        final.state := congrArg History.state sourceEq
    have clean := bounds.onePacketMenu_countCharge_zero timeouts leaks Initial horizon scheduler
      spec.evidenceService sourceFinal who
    rw [stateEq] at clean
    simpa only [TerminalAudit.charge, (app).stateTraffic_normalization
      ((reactiveNormalization timeouts) leaks)] using clean
  refine ⟨chargeZero, ?_⟩
  have normalBase (final : (RP).History) : base (normalize final).state = base final.state :=
    exclusionBase_normalization setup timeouts parameter utility excludedPayoff leaks final.state
  have retainedBase (final : (EP).History) : base (embed final).state = base final.state := rfl
  calc
    _ = rawRun.map (fun final => (normalize final, base final.state)) := by
      rw [← PMF.bind_pure_comp]
      apply bind_congr_on_support
      intro final supported
      have settled : spec.settlement final.state = PMF.pure (base final.state) :=
        TerminalAudit.settlement_clean base (app).stateTraffic
          ((countAudit timeouts) leaks spec.evidenceService.sample) spec.deposit final.state
            (chargeZero final supported)
      rw [settled, PMF.pure_map]
      rfl
    _ = _ := by
      have transported := congrArg (fun law => law.map (fun final => (final, base final.state)))
        histories
      simpa only [PMF.map_comp, Function.comp_def, normalBase, retainedBase] using transported

omit [Fintype Player] in
/-- Every configuration in an intended continuation from an actually reached
intended source point has no public default or failed reveal. -/
theorem intendedOpening_continuation_clean
    [Finite Player] (wellFormed : setup.WellFormed)
    (intended : ∀ who, setup.intendedModel.BehavioralPolicy who)
    (point : ProtocolState setup.program) (reached : IntendedReached setup point)
    (terminal : Config Player L setup.program.terminalCtx)
    (supported : terminal ∈ (setup.continuationLaw
      (setup.intendedOpeningProfile intended) (some point)).support) :
    terminal.defaulted = ∅ ∧
      ∀ who, failedReveals setup.program who (publicOutcome setup.program terminal) = 0 := by
  let := Fintype.ofFinite Player
  obtain ⟨history, state⟩ := reached
  have law := setup.intendedOpeningProfile_runFrom wellFormed intended
    (setup.protocolRemaining history.state) history le_rfl
  have observed : some terminal ∈ ((setup.continuationLaw
      (setup.intendedOpeningProfile intended) history.state).map some).support := by
    rw [state]
    exact (PMF.mem_support_map_iff _ _ _).mpr ⟨terminal, supported, rfl⟩
  rw [← law] at observed
  obtain ⟨final, _finalSupport, read⟩ := (PMF.mem_support_map_iff _ _ _).mp observed
  exact ⟨Finset.eq_empty_iff_forall_notMem.mpr fun who =>
    setup.not_defaulted_of_intendedState (setup.intendedState_trace wellFormed final.trace)
      who read, setup.intended_no_failed_reveals wellFormed final read⟩

/-- The exact source configuration and ordinary utility law at a clean
boundary is also the actual raw realized-settlement law. -/
theorem ClientAssessmentRefinement.continuation_source_settlement
    (spec : ClientSpec setup timeouts leaks bounds horizon scheduler
      parameter utility excludedPayoff)
    {intended : setup.intendedModel.BehavioralAssessment} {target : (R).BehavioralAssessment}
    (refinement : ClientAssessmentRefinement setup timeouts leaks bounds horizon scheduler
      intended target)
    (nativeStart : (EP).History) (rawStart : (RP).History)
    (same : ((reactiveNormalization timeouts) leaks).history (raw)
      (bounds.rawMenu_recall timeouts leaks) Initial horizon scheduler rawStart =
      (bounds.onePacketRestriction timeouts leaks Initial horizon scheduler).history nativeStart)
    (rank : Nat) (anchor : (app).Execution)
    (state : nativeStart.state = some ⟨horizon - anchor.environmentRecall.length, none, anchor⟩)
    (boundary : ReachedBoundary setup timeouts leaks horizon scheduler rank anchor)
    (point : ProtocolState setup.program)
    (decoded : sourceServicePrefix? setup rank anchor.application.config = some point)
    (valid : ProtocolState.Intended setup.program point) :
    ((raw).runFrom Initial horizon scheduler target.strategy rawStart).bind
        (fun final => spec.observation final.state) =
      (setup.continuationLaw (setup.intendedOpeningProfile intended.strategy) (some point)).map
        (fun terminal => (some terminal, utility (setup.parameterOutcome parameter terminal))) := by
  have settled := (refinement.continuation_settlement spec nativeStart rawStart same).2
  have projected := congrArg (PMF.map (fun output =>
    (sourceReadout setup timeouts leaks output.1.state, output.2))) settled
  have normalRead (history : (RP).History) :
      sourceReadout setup timeouts leaks
        (((reactiveNormalization timeouts) leaks).history (raw)
          (bounds.rawMenu_recall timeouts leaks) Initial horizon scheduler history).state =
      sourceReadout setup timeouts leaks history.state := by
    change sourceReadout setup timeouts leaks
      (((reactiveNormalization timeouts) leaks).state history.state) = _
    cases history.state <;> rfl
  have retainedRead (history : (EP).History) :
      sourceReadout setup timeouts leaks
        ((bounds.onePacketRestriction timeouts leaks Initial horizon scheduler).history
          history).state = sourceReadout setup timeouts leaks history.state := rfl
  have nativeLaw := refinement.fidelity.continuation_jointLaw parameter utility excludedPayoff
    rank nativeStart anchor state boundary point decoded valid
  have readoutJoint :
      ((raw).runFrom Initial horizon scheduler target.strategy rawStart).bind
        (fun final => spec.observation final.state) =
      ((one).runFrom Initial horizon scheduler refinement.native.strategy nativeStart).map
        (readoutExclusion setup timeouts leaks bounds Initial horizon scheduler parameter
          utility excludedPayoff) := by
    change ((raw).runFrom Initial horizon scheduler target.strategy rawStart).bind
        (fun final => (spec.settlement final.state).map
          (fun payoffs => (sourceReadout setup timeouts leaks final.state, payoffs))) =
      ((one).runFrom Initial horizon scheduler refinement.native.strategy nativeStart).map
        (fun final => (sourceReadout setup timeouts leaks final.state,
          exclusionBase setup timeouts parameter utility excludedPayoff leaks final.state))
    simpa only [PMF.map_bind, PMF.map_comp, Function.comp_def, normalRead,
      retainedRead] using projected
  refine readoutJoint.trans (nativeLaw.trans ?_)
  apply map_congr_on_support
  intro terminal supported
  have reached := intendedReached_of_reachedBoundary spec.wellFormed rank nativeStart anchor
    state boundary point decoded valid
  have clean := intendedOpening_continuation_clean spec.wellFormed intended.strategy point
    reached terminal supported
  apply Prod.ext
  · rfl
  · funext who
    exact exclusionTerminalUtility_of_not_defaulted setup parameter utility excludedPayoff
      (by rw [clean.1]; exact Finset.notMem_empty who)

/-- Every supported raw continuation from a represented clean source boundary
finishes with a complete source readout, no public defaults and no failed reveal. -/
theorem ClientAssessmentRefinement.continuation_source_clean
    (spec : ClientSpec setup timeouts leaks bounds horizon scheduler
      parameter utility excludedPayoff)
    {intended : setup.intendedModel.BehavioralAssessment} {target : (R).BehavioralAssessment}
    (refinement : ClientAssessmentRefinement setup timeouts leaks bounds horizon scheduler
      intended target)
    (nativeStart : (EP).History) (rawStart : (RP).History)
    (same : ((reactiveNormalization timeouts) leaks).history (raw)
      (bounds.rawMenu_recall timeouts leaks) Initial horizon scheduler rawStart =
      (bounds.onePacketRestriction timeouts leaks Initial horizon scheduler).history nativeStart)
    (rank : Nat) (anchor : (app).Execution)
    (state : nativeStart.state = some ⟨horizon - anchor.environmentRecall.length, none, anchor⟩)
    (boundary : ReachedBoundary setup timeouts leaks horizon scheduler rank anchor)
    (point : ProtocolState setup.program)
    (decoded : sourceServicePrefix? setup rank anchor.application.config = some point)
    (valid : ProtocolState.Intended setup.program point) :
    ∀ final ∈ ((raw).runFrom Initial horizon scheduler target.strategy rawStart).support,
      ∃ (control : (app).Control) (terminal : Config Player L setup.program.terminalCtx),
        final.state = some control ∧
        sourceReadout setup timeouts leaks final.state = some terminal ∧
        control.execution.application.config.defaulted = ∅ ∧
        (∀ who, failedReveals setup.program who (publicOutcome setup.program terminal) = 0) := by
  have settled := refinement.continuation_source_settlement spec nativeStart rawStart same rank
    anchor state boundary point decoded valid
  have readoutLaw :
      ((raw).runFrom Initial horizon scheduler target.strategy rawStart).map
        (fun final => sourceReadout setup timeouts leaks final.state) =
      (setup.continuationLaw (setup.intendedOpeningProfile intended.strategy) (some point)).map
        some := by
    have projected := congrArg (PMF.map Prod.fst) settled
    have forgetSettlement (final : (RP).History) :
        (spec.observation final.state).map Prod.fst =
          PMF.pure (sourceReadout setup timeouts leaks final.state) := by
      rw [ClientSpec.observation, PMF.map_comp]
      exact PMF.map_const _ _
    have forgetLaw :
        ((raw).runFrom Initial horizon scheduler target.strategy rawStart).bind
          (fun final => PMF.pure (sourceReadout setup timeouts leaks final.state)) =
        ((raw).runFrom Initial horizon scheduler target.strategy rawStart).map
          (fun final => sourceReadout setup timeouts leaks final.state) :=
      PMF.bind_pure_comp _ _
    apply forgetLaw.symm.trans
    simpa only [PMF.map_bind, forgetSettlement, PMF.map_comp, Function.comp_def] using projected
  have reached := intendedReached_of_reachedBoundary spec.wellFormed rank nativeStart anchor
    state boundary point decoded valid
  intro final supported
  have observed : sourceReadout setup timeouts leaks final.state ∈
      ((setup.continuationLaw (setup.intendedOpeningProfile intended.strategy)
        (some point)).map some).support := by
    rw [← readoutLaw]
    exact (PMF.mem_support_map_iff _ _ _).mpr ⟨final, supported, rfl⟩
  obtain ⟨terminal, sourceSupport, decodedFinal⟩ := (PMF.mem_support_map_iff _ _ _).mp observed
  have sourceClean := intendedOpening_continuation_clean spec.wellFormed intended.strategy point
    reached terminal sourceSupport
  have read : sourceReadout setup timeouts leaks final.state = some terminal := decodedFinal.symm
  cases current : final.state with
  | none =>
      rw [current] at read
      cases read
  | some control =>
      have readAt : sourceReadout setup timeouts leaks (some control) = some terminal := by
        rw [← current]
        exact read
      have defaults := serviceSourceReadout_defaults setup .sequential timeouts.duration leaks
        control terminal readAt
      exact ⟨control, terminal, rfl, readAt,
        (congrArg DefaultHistory.defaulted defaults).symm.trans sourceClean.1, sourceClean.2⟩

/-- Decoding the selected raw strategy preserves the complete intended joint
source-configuration and realized-settlement law from every represented clean boundary. -/
theorem ClientAssessmentRefinement.physical_continuation_source_settlement
    (spec : ClientSpec setup timeouts leaks bounds horizon scheduler
      parameter utility excludedPayoff)
    {intended : setup.intendedModel.BehavioralAssessment} {target : (R).BehavioralAssessment}
    (refinement : ClientAssessmentRefinement setup timeouts leaks bounds horizon scheduler
      intended target)
    (nativeStart : (EP).History) (rawStart : (RP).History)
    (same : ((reactiveNormalization timeouts) leaks).history (raw)
      (bounds.rawMenu_recall timeouts leaks) Initial horizon scheduler rawStart =
      (bounds.onePacketRestriction timeouts leaks Initial horizon scheduler).history nativeStart)
    (rank : Nat) (anchor : (app).Execution)
    (state : nativeStart.state = some ⟨horizon - anchor.environmentRecall.length, none, anchor⟩)
    (boundary : ReachedBoundary setup timeouts leaks horizon scheduler rank anchor)
    (point : ProtocolState setup.program)
    (decoded : sourceServicePrefix? setup rank anchor.application.config = some point)
    (valid : ProtocolState.Intended setup.program point) :
    ((app).finish Initial horizon scheduler
      ((raw).decodeProfile Initial horizon scheduler target.strategy) rawStart.state).bind
        spec.observation =
      (setup.continuationLaw (setup.intendedOpeningProfile intended.strategy) (some point)).map
        (fun terminal => (some terminal, utility (setup.parameterOutcome parameter terminal))) := by
  have physical := congrArg (fun law => law.bind spec.observation)
    ((raw).runFrom_stateLaw Initial horizon scheduler target.strategy rawStart)
  rw [PMF.bind_map] at physical
  exact physical.symm.trans (refinement.continuation_source_settlement spec nativeStart rawStart
    same rank anchor state boundary point decoded valid)

/-- Every decoded physical continuation from represented starts incurs no audit charge. -/
theorem ClientAssessmentRefinement.physical_continuation_noCharges
    (spec : ClientSpec setup timeouts leaks bounds horizon scheduler
      parameter utility excludedPayoff)
    {intended : setup.intendedModel.BehavioralAssessment} {target : (R).BehavioralAssessment}
    (refinement : ClientAssessmentRefinement setup timeouts leaks bounds horizon scheduler
      intended target)
    (nativeStart : (EP).History) (rawStart : (RP).History)
    (same : ((reactiveNormalization timeouts) leaks).history (raw)
      (bounds.rawMenu_recall timeouts leaks) Initial horizon scheduler rawStart =
      (bounds.onePacketRestriction timeouts leaks Initial horizon scheduler).history nativeStart)
    (outcome : (app).ProtocolState)
    (supported : outcome ∈ ((app).finish Initial horizon scheduler
      ((raw).decodeProfile Initial horizon scheduler target.strategy) rawStart.state).support)
    (who : Player) :
    TerminalAudit.charge (app).stateTraffic
      ((countAudit timeouts) leaks spec.evidenceService.sample) outcome who = 0 := by
  rw [← (raw).runFrom_stateLaw Initial horizon scheduler target.strategy rawStart] at supported
  obtain ⟨final, member, current⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
  rw [← current]
  exact (refinement.continuation_settlement spec nativeStart rawStart same).1 final member who

/-- Every supported decoded physical continuation from a represented clean
source boundary has a complete readout, no public default and no failed reveal. -/
theorem ClientAssessmentRefinement.physical_continuation_source_clean
    (spec : ClientSpec setup timeouts leaks bounds horizon scheduler
      parameter utility excludedPayoff)
    {intended : setup.intendedModel.BehavioralAssessment} {target : (R).BehavioralAssessment}
    (refinement : ClientAssessmentRefinement setup timeouts leaks bounds horizon scheduler
      intended target)
    (nativeStart : (EP).History) (rawStart : (RP).History)
    (same : ((reactiveNormalization timeouts) leaks).history (raw)
      (bounds.rawMenu_recall timeouts leaks) Initial horizon scheduler rawStart =
      (bounds.onePacketRestriction timeouts leaks Initial horizon scheduler).history nativeStart)
    (rank : Nat) (anchor : (app).Execution)
    (state : nativeStart.state = some ⟨horizon - anchor.environmentRecall.length, none, anchor⟩)
    (boundary : ReachedBoundary setup timeouts leaks horizon scheduler rank anchor)
    (point : ProtocolState setup.program)
    (decoded : sourceServicePrefix? setup rank anchor.application.config = some point)
    (valid : ProtocolState.Intended setup.program point)
    (outcome : (app).ProtocolState)
    (supported : outcome ∈ ((app).finish Initial horizon scheduler
      ((raw).decodeProfile Initial horizon scheduler target.strategy) rawStart.state).support) :
    ∃ (control : (app).Control) (terminal : Config Player L setup.program.terminalCtx),
      outcome = some control ∧
      sourceReadout setup timeouts leaks outcome = some terminal ∧
      control.execution.application.config.defaulted = ∅ ∧
      (∀ who, failedReveals setup.program who (publicOutcome setup.program terminal) = 0) := by
  rw [← (raw).runFrom_stateLaw Initial horizon scheduler target.strategy rawStart] at supported
  obtain ⟨final, member, current⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
  simpa only [current] using refinement.continuation_source_clean spec nativeStart rawStart same
    rank anchor state boundary point decoded valid final member

/-- The actual settled continuation contract holds for the same semantic
assessment refinement at every matching pair of legal histories. -/
theorem ClientAssessmentRefinement.continuation_correct
    (spec : ClientSpec setup timeouts leaks bounds horizon scheduler
      parameter utility excludedPayoff)
    {intended : setup.intendedModel.BehavioralAssessment} {target : (R).BehavioralAssessment}
    (refinement : ClientAssessmentRefinement setup timeouts leaks bounds horizon scheduler
      intended target) :
    ClientContinuationCorrectness spec intended target refinement := by
  intro nativeStart rawStart same
  obtain ⟨charges, histories⟩ := refinement.continuation_settlement spec nativeStart rawStart same
  refine ⟨charges, histories, ?_⟩
  intro rank anchor state boundary point decoded valid
  exact ⟨refinement.continuation_source_clean spec nativeStart rawStart same rank anchor state
    boundary point decoded valid,
    refinement.continuation_source_settlement spec nativeStart rawStart same rank anchor state
      boundary point decoded valid⟩

end Vegas
