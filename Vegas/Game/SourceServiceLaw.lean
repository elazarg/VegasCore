/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServicePhaseLaw
import Vegas.Game.SourceServiceCompiledExecution
import GameTheoryExtensions.Math.Probability.Support

/-! # Initialized source laws of the full native service

The actual service prefix is read into the existing source protocol. Its
transition law is derived on every supported prefix, including correlated
initial types, dynamic binding catalogues and retained private traffic.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
open GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]

theorem sourceService_prefix_state_law
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (bounds : MessageBounds (graph setup)) (values : bounds.CoversBindingValues)
    (initialValues : ∀ state ∈ (initialLaw setup).support, bounds.CandidateValues state)
    (capacity : (graph setup).order.eventCount ≤ bounds.candidateCount)
    (rosters : (graph setup).EventId → List Player)
    (opportunities : ActorOpportunities setup rosters)
    (network : (runtime setup).NetworkPolicy leaks)
    (profile : BehavioralProfile setup.program)
    (permitted : ∀ who, (profile who).Admitted setup.program
      (CommitmentInterface.values setup.program))
    (effective : ∀ who, (profile who).EffectiveDisclosures setup.program []
      (Revelations.initial setup.context))
    (count : Nat) (within : count ≤ eventCount setup.program) :
    let admission := CommitmentInterface.values setup.program
    let encoded := fun who => setup.toProtocolBehavioralPolicy admission who
      (profile who) (permitted who)
    (((initialLaw setup).bind fun state => (runtime setup).runInteractionPlan leaks
      (sourceServiceLastPolicy setup leaks rosters profile) network
      (rosterPlanPrefix setup rosters count)
      (ReactiveApplication.Execution.initial (application setup leaks) state)).map fun final =>
        sourceServicePrefix? setup count final.application.config) =
      ((setup.informationModel admission).runBehavioral encoded (count + 1)).map History.state := by
  intro admission encoded
  let app := application setup leaks
  let menu := sourceServiceMenu setup leaks bounds rosters
  let players := sourceServiceLastPolicy setup leaks rosters profile
  let physical := fun count => (initialLaw setup).bind fun state =>
    (runtime setup).runInteractionPlan leaks players network (rosterPlanPrefix setup rosters count)
      (ReactiveApplication.Execution.initial app state)
  let readout := fun count (execution : app.Execution) =>
    sourceServicePrefix? setup count execution.application.config
  let kernel := setup.behavioralStateStep admission encoded
  have bindingOpportunities := opportunities.binding
  have covered := sourceServiceLastPolicy_admissible setup leaks bounds values initialValues
    capacity rosters bindingOpportunities network profile permitted
  have step (rank : Nat) (inside : rank < (graph setup).order.eventCount)
      (execution : app.Execution) (supported : execution ∈ (physical rank).support) :
      ((runtime setup).runInteractionPlan leaks players network
        (rosterBlock setup rosters ⟨rank, inside⟩) execution).map (readout (rank + 1)) =
          kernel (readout rank execution) := by
    have uniform := roster_restrict_prefix_support setup leaks rosters network menu players
      covered rank execution supported
    obtain ⟨initial, _selected, state, _related, decoded, Γ, names, remaining, remainingProfile,
      current, refs, embedding, refsBefore, aligned, _admitted, lift, stateEq, stepEq, decodeEq,
      inheritedEffective, _, boundary⟩ :=
      initialized_sourceService_prefix_support setup leaks bounds values capacity rosters
        bindingOpportunities menu.uniformResponses
        (fun who past view response chosen =>
          (menu.uniformResponses_support who past view response).mp chosen)
        network profile rank inside.le execution uniform
    have positive : 0 < eventCount remaining := by
      have remainingCount := aligned.graphSuffix.countEq
      have wholeInside : rank < eventCount setup.program := inside
      omega
    have atRank : (embedding.event ⟨0, positive⟩).val = rank := by
      simpa only [Nat.add_zero] using aligned.graphSuffix.rankEq ⟨0, positive⟩
    have eventEq : embedding.event ⟨0, positive⟩ = (⟨rank, inside⟩ : (graph setup).EventId) :=
      Fin.ext atRank
    have phase := boundary.step_state_law remaining positive profile remainingProfile current refs
      embedding refsBefore rank aligned execution bounds network opportunities
        (inheritedEffective effective)
    have projected := congrArg (PMF.map (Option.map lift)) phase
    simp only [PMF.map_comp, Function.comp_def, Option.map_some] at projected
    have decodeAt (final : app.Execution) : readout (rank + 1) final =
        (decodeSourcePrefix? remaining refs current.registry current.revelations embedding.ref 1
          final.application.config.store (decodeHistory setup.program
            (final.application.config.history.map
              (setup.eventGraph.fromModeCompletion .sequential)))).map lift :=
      decodeEq 1 _ _
    have sourceStep : kernel (readout rank execution) =
        (ProtocolState.behavioralStateStep remaining remainingProfile
          (ProtocolState.entry remaining current)).map (some ∘ lift) := by
      change setup.behavioralStateStep admission encoded
        (sourceServicePrefix? setup rank execution.application.config) = _
      rw [decoded, stateEq, setup.behavioralStateStep_encoded_some admission profile permitted,
        stepEq.1, PMF.map_comp]
    rw [sourceStep]
    have expected := projected
    rw [eventEq] at expected
    refine Eq.trans ?_ expected
    apply map_congr_on_support _
    intro final _
    exact decodeAt final
  have prefixes : ∀ rank ≤ eventCount setup.program,
      (physical rank).map (readout rank) =
        (fun law => law.bind kernel)^[rank + 1] (PMF.pure none) := by
    intro rank bound
    induction rank with
    | zero =>
        change ((initialLaw setup).bind fun state =>
          (runtime setup).runInteractionPlan leaks players network
            (rosterPlanPrefix setup rosters 0)
            (ReactiveApplication.Execution.initial app state)).map (readout 0) = _
        simp only [rosterPlanPrefix, List.take_zero, List.flatMap_nil, runInteractionPlan,
          Nat.zero_add, Function.iterate_one, PMF.pure_bind, ← PMF.bind_pure_comp, Function.comp_def,
          PMF.map_comp]
        change (initialLaw setup).map (fun state => sourceServicePrefix? setup 0
          (ReactiveApplication.Execution.initial app state).application.config) =
            setup.behavioralStateStep admission encoded none
        rw [setup.behavioralStateStep_none, initialLaw, PMF.map_comp]
        congr 1
        funext initial
        exact sourceServicePrefix?_initial setup initial
    | succ rank ih =>
        have inside : rank < (graph setup).order.eventCount := by
          change rank < eventCount setup.program
          omega
        have prior := ih inside.le
        have plan := rosterPlanPrefix_succ setup rosters ⟨rank, inside⟩
        have distribution : physical (rank + 1) = (physical rank).bind
            ((runtime setup).runInteractionPlan leaks players network
              (rosterBlock setup rosters ⟨rank, inside⟩)) := by
          dsimp only [physical]
          simp only [plan, (runtime setup).runInteractionPlan_append, PMF.bind_bind]
        rw [distribution, PMF.map_bind]
        trans (physical rank).bind (fun execution => kernel (readout rank execution))
        · exact bind_congr_on_support _ (fun execution supported => step rank inside execution supported)
        · rw [← PMF.bind_map, prior]
          exact (Function.iterate_succ_apply' (fun law => law.bind kernel) (rank + 1)
            (PMF.pure none)).symm
  have sourceLaw := setup.runBehavioralFrom_state admission encoded (count + 1)
    (setup.executionProtocol admission).initHistory
  exact (prefixes count within).trans sourceLaw.symm

omit [Fintype Player] in
theorem decodeSourcePrefix?_terminal_readout
    {Field : Type} [DecidableEq Field] {layout : Field → EventGraph.EventField Player L}
    {Γ : SourceCtx Player L} {openNames : Finset VarId}
    (program : SourceProgram Player L Γ openNames) (refs : ContextRefs layout Γ)
    (registry : Registry Γ) (revelations : Revelations Γ)
    (outputs : ∀ event, EventGraph.FieldRef layout (outputLayout program event))
    (store : EventGraph.Store layout) (history : SourceProgram.History Player L) :
    (decodeSourcePrefix? program refs registry revelations outputs (eventCount program)
      store history).bind (ProtocolState.readout program) =
        decodeState? (terminalRefsWith program refs outputs) store := by
  induction program with
  | ret payoffs =>
      simp only [eventCount, decodeSourcePrefix?, terminalRefsWith]
      cases decodeState? refs store <;> rfl
  | sample name fresh distribution next ih =>
      simp only [eventCount, decodeSourcePrefix?, terminalRefsWith, Option.bind_map]
      exact ih _ _ _ _
  | commit name owner fresh guard next ih =>
      simp only [eventCount, decodeSourcePrefix?, terminalRefsWith, Option.bind_map]
      exact ih _ _ _ _
  | reveal published owner name fresh binding unresolved next ih =>
      simp only [eventCount, decodeSourcePrefix?, terminalRefsWith, Option.bind_map]
      exact ih _ _ _ _

omit [Fintype Player] in
theorem sourceServicePrefix?_terminal_readout
    (setup : Setup (Player := Player) (L := L)) (config : (graph setup).Config) :
    setup.protocolReadout (sourceServicePrefix? setup (eventCount setup.program) config) =
      decodeState? (terminalRefs setup.program) config.store :=
  decodeSourcePrefix?_terminal_readout setup.program _ _ _ _ _ _

omit [Fintype Player] in
/-- The whole physical service has the typed outcome law of its effective
source policy. This theorem includes the original sampling distributions and
all dynamically created source bindings. -/
theorem sourceServiceLastPolicy_readout_law [Finite Player]
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (bounds : MessageBounds (graph setup)) (values : bounds.CoversBindingValues)
    (initialValues : ∀ state ∈ (initialLaw setup).support, bounds.CandidateValues state)
    (capacity : (graph setup).order.eventCount ≤ bounds.candidateCount)
    (rosters : (graph setup).EventId → List Player)
    (opportunities : ActorOpportunities setup rosters)
    (network : (runtime setup).NetworkPolicy leaks)
    (profile : BehavioralProfile setup.program)
    (permitted : ∀ who, (profile who).Admitted setup.program
      (CommitmentInterface.values setup.program))
    (effective : ∀ who, (profile who).EffectiveDisclosures setup.program []
      (Revelations.initial setup.context)) :
    (((initialLaw setup).bind fun state => (runtime setup).runInteractionPlan leaks
      (sourceServiceLastPolicy setup leaks rosters profile) network (rosterPlan setup rosters)
      (ReactiveApplication.Execution.initial (application setup leaks) state)).map fun final =>
        sourceReadout setup leaks (some ⟨0, none, final⟩)) = (setup.run profile).map some := by
  let := Fintype.ofFinite Player
  have prefixLaw := sourceService_prefix_state_law setup leaks bounds values initialValues capacity
    rosters opportunities network profile permitted effective (eventCount setup.program) le_rfl
  have observed := congrArg (PMF.map setup.protocolReadout) prefixLaw
  simp only [PMF.map_comp, Function.comp_def] at observed
  have completed : rosterPlanPrefix setup rosters (eventCount setup.program) =
      rosterPlan setup rosters := by
    unfold rosterPlanPrefix rosterPlan
    rw [List.take_of_length_le (by
      rw [List.length_finRange]
      exact le_rfl)]
  simp only [completed, sourceServicePrefix?_terminal_readout] at observed
  have sourceLaw := setup.protocol_runBehavioral_eq (CommitmentInterface.values setup.program)
    profile permitted
  rw [InformationModel.runSingleMoverBehavioralFrom_eq_runBehavioralFrom] at sourceLaw
  have finished := observed.trans (by
    simpa only [eventCount_eq_instructionCount, InformationModel.runBehavioral] using sourceLaw)
  simpa only [sourceReadout_eq_decode] using finished

/-- The actual finite compiler preserves the original source's whole typed
outcome law. Failed guarded reveal intentions are retained by the original
policy's private-memory normalization, whose exact source law is used here. -/
theorem sourceServiceCompiledProfile_readout_law
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (bounds : MessageBounds (graph setup)) (values : bounds.CoversBindingValues)
    (initialValues : ∀ state ∈ (initialLaw setup).support, bounds.CandidateValues state)
    (capacity : (graph setup).order.eventCount ≤ bounds.candidateCount)
    (rosters : (graph setup).EventId → List Player)
    (opportunities : ActorOpportunities setup rosters)
    (network : (runtime setup).NetworkPolicy leaks)
    (original : BehavioralProfile setup.program)
    (permitted : ∀ who, (original who).Admitted setup.program
      (CommitmentInterface.values setup.program)) :
    (((sourceServiceMenu setup leaks bounds rosters).information (initialLaw setup)
      (rosterPlan setup rosters).length (rosterScheduler setup leaks rosters network)).runBehavioral
      (sourceServiceCompiledProfile setup leaks bounds rosters network original)
      (2 * (rosterPlan setup rosters).length + 1)).map
        (fun final => sourceReadout setup leaks final.state) = (setup.run original).map some := by
  let normalized := normalizeDisclosureProfile setup.program []
    (Revelations.initial setup.context) original
  have bindingOpportunities := opportunities.binding
  have physical := sourceServiceCompiledProfile_complete_state setup leaks bounds values
    initialValues capacity rosters bindingOpportunities network original permitted
  have observed := congrArg (PMF.map (sourceReadout setup leaks)) physical
  simp only [PMF.map_comp, Function.comp_def] at observed
  have effective (who : Player) : (normalized who).EffectiveDisclosures setup.program []
      (Revelations.initial setup.context) :=
    (original who).normalizeDisclosureFrom_effective setup.program []
      (Revelations.initial setup.context) (fun view => PMF.pure view.2)
  have sourceLaw := sourceServiceLastPolicy_readout_law setup leaks bounds values initialValues
    capacity rosters opportunities network normalized
      (normalized_sourceService_admitted setup original permitted) effective
  refine observed.trans (sourceLaw.trans ?_)
  apply congrArg (PMF.map some)
  unfold Setup.run
  apply bind_congr_on_support _
  intro initial _
  exact normalizeDisclosureProfile_runFrom setup.program original (setup.initialConfig initial)

end Vegas
