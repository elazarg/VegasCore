/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceDeviationLaw
import Vegas.Game.SourceServiceTimedLaw

/-! # Typed outcome of a permitted deviation

Against the timed calendar profile of a source profile, every unilateral
deviation within the permitted menu has the typed terminal-state law of a
single source deviation of the same player, admitted at the commitment
interface. Private-intention normalization of the other players is undone by
the existing normalization theorem.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
open GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]

/-- Every initialized prefix of a permitted deviation has the state law of a
source deviation, jointly with the deviator's traffic, which depends on the
source state only through the deviator's source observation. -/
theorem sourceServiceDeviation_initialized_prefix_factorization
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (bounds : MessageBounds (graph setup)) (values : bounds.CoversBindingValues)
    (capacity : (graph setup).order.eventCount ≤ bounds.candidateCount)
    (rosters : (graph setup).EventId → List Player)
    (opportunities : BindingOpportunities setup rosters)
    (timing : TimingLaw setup rosters)
    (network : (runtime setup).NetworkPolicy leaks)
    (profile : BehavioralProfile setup.program)
    (who : Player) (deviation : (application setup leaks).Policy)
    (lawful : ∀ past view response, response ∈ (deviation past view).support →
      response ∈ (sourceServiceMenu setup leaks bounds rosters).actions who past view)
    (covered : ∀ player, (sourceServiceMenu setup leaks bounds rosters).Admissible
      (initialLaw setup) (rosterPlan setup rosters).length
      (rosterScheduler setup leaks rosters network) player
      (Function.update (sourceServiceTimedPolicy setup leaks rosters timing profile) who
        deviation player))
    (permitted : ∀ player, (profile player).Admitted setup.program
      (CommitmentInterface.values setup.program))
    (effective : ∀ player, (profile player).EffectiveDisclosures setup.program []
      (Revelations.initial setup.context))
    (count : Nat) (within : count ≤ eventCount setup.program) :
    let players := Function.update (sourceServiceTimedPolicy setup leaks rosters timing profile)
      who deviation
    ∃ policy : BehavioralPolicy who setup.program,
      policy.Admitted setup.program (CommitmentInterface.values setup.program) ∧
      ∃ noise : setup.ProtocolView who → PMF _,
        (((initialLaw setup).bind fun state => (runtime setup).runInteractionPlan leaks
          players network (rosterPlanPrefix setup rosters count)
          (ReactiveApplication.Execution.initial (application setup leaks) state)).map fun final =>
            (sourceServicePrefix? setup count final.application.config,
              (runtime setup).bindingTraffic leaks who final)) =
          (setup.initialLaw.bind fun initial =>
            ((fun law => law.bind (ProtocolState.behavioralStateStep setup.program
              (Function.update profile who policy)))^[count]
              (PMF.pure (ProtocolState.entry setup.program (setup.initialConfig initial)))).map
                some).bind fun state =>
              (noise (setup.protocolObserve who state)).map fun extra => (state, extra) := by
  intro players
  let Seed := {initial // initial ∈ setup.initialLaw.support}
  let prior : PMF Seed := pmfToSubtype setup.initialLaw (fun _ member => member)
  let source := fun seed : Seed => setup.initialConfig seed.val
  let execution := fun seed : Seed => ReactiveApplication.Execution.initial
    (application setup leaks) (EventGraphRuntime.State.initial (graph := graph setup)
      (setup.eventInputs seed.val))
  obtain ⟨initialNoise, initialFactor⟩ := source_initial_memory_factorization setup leaks who
  have factor : prior.map (fun seed => (source seed,
      (runtime setup).bindingTraffic leaks who (execution seed))) =
      (prior.map source).bind fun config =>
        (initialNoise (config.view who)).map fun extra => (config, extra) := by
    have projected := congrArg (PMF.map fun pair => (pair.1.1, pair.2)) initialFactor
    dsimp only [prior, source, execution]
    rw [map_pmfToSubtype setup.initialLaw (fun _ member => member)
      (fun initial => (setup.initialConfig initial,
        (runtime setup).bindingTraffic leaks who
          (ReactiveApplication.Execution.initial (application setup leaks)
            (EventGraphRuntime.State.initial (graph := graph setup) (setup.eventInputs initial))))),
      map_pmfToSubtype setup.initialLaw (fun _ member => member) setup.initialConfig]
    simpa only [PMF.map_comp, PMF.map_bind, PMF.bind_map, Function.comp_def]
      using projected
  have initialized (seed : Seed) : execution seed ∈ ((initialLaw setup).bind fun state =>
      (runtime setup).runInteractionPlan leaks players network
        (rosterPlanPrefix setup rosters 0)
        (ReactiveApplication.Execution.initial (application setup leaks) state)).support := by
    simp only [rosterPlanPrefix, List.take_zero, List.flatMap_nil, runInteractionPlan, initialLaw,
      serviceInitialLaw]
    exact (PMF.mem_support_bind_iff _ _ _).mpr ⟨_, (PMF.mem_support_map_iff _ _ _).mpr
      ⟨seed.val, seed.property, rfl⟩, (PMF.mem_support_pure_iff _ _).mpr rfl⟩
  obtain ⟨policy, allowed, noise, law⟩ := sourceServiceDeviation_prefix_joint_factorization setup
    leaks bounds values capacity rosters opportunities timing network profile who deviation
      lawful covered count setup.program profile
      (ContextRefs.initial setup.context (outputLayout setup.program))
      (outputEmbedding setup.program) (initialRefsBefore setup.program) 0 prior source execution
      (fun _ => CompiledPolicySuffix.whole setup.program profile)
      (fun seed => SourceCheckpoint.initial setup seed.val) initialized
      (fun _ player => effective player) permitted initialNoise factor within
  refine ⟨policy, allowed, noise, ?_⟩
  let combined := fun initial : State L setup.context =>
    ((runtime setup).runInteractionPlan leaks players network
      (rosterPlanPrefix setup rosters count)
      (ReactiveApplication.Execution.initial (application setup leaks)
        (EventGraphRuntime.State.initial (graph := graph setup) (setup.eventInputs initial)))).map
      fun final => (sourceServicePrefix? setup count final.application.config,
        (runtime setup).bindingTraffic leaks who final)
  let sourcePrefix := fun initial : State L setup.context =>
    ((fun law => law.bind (ProtocolState.behavioralStateStep setup.program
      (Function.update profile who policy)))^[count]
      (PMF.pure (ProtocolState.entry setup.program (setup.initialConfig initial)))).map some
  have nativeLaw : prior.bind (fun seed => combined seed.val) = setup.initialLaw.bind combined := by
    refine (PMF.bind_map prior Subtype.val combined).symm.trans ?_
    exact congrArg (fun law => law.bind combined) (map_val_pmfToSubtype _ _)
  have sourceLaw : prior.bind (fun seed => sourcePrefix seed.val) =
      setup.initialLaw.bind sourcePrefix := by
    refine (PMF.bind_map prior Subtype.val sourcePrefix).symm.trans ?_
    exact congrArg (fun law => law.bind sourcePrefix) (map_val_pmfToSubtype _ _)
  change (prior.bind fun seed => combined seed.val) =
    (prior.bind fun seed => sourcePrefix seed.val).bind fun state =>
      (noise (setup.protocolObserve who state)).map fun extra => (state, extra) at law
  rw [nativeLaw, sourceLaw] at law
  rw [initialLaw, serviceInitialLaw, PMF.bind_map, PMF.map_bind]
  exact law

omit [Fintype Player] in
/-- Replacing one player's policy commutes with the other players' private
intention normalization: the source law is unchanged. -/
theorem run_update_normalizeDisclosureProfile [Finite Player]
    (setup : Setup (Player := Player) (L := L)) (original : BehavioralProfile setup.program)
    (who : Player) (policy : BehavioralPolicy who setup.program) :
    setup.run (Function.update (normalizeDisclosureProfile setup.program []
      (Revelations.initial setup.context) original) who policy) =
      setup.run (Function.update original who policy) := by
  unfold Setup.run
  apply bind_congr_on_support _
  intro initial _
  let config := setup.initialConfig initial
  let normalized := normalizeDisclosureProfile setup.program []
    (Revelations.initial setup.context) original
  have own := normalizeDisclosures_runFrom setup.program
    (Function.update normalized who policy) policy config
  rw [Function.update_idem, Function.update_idem] at own
  have profiles : Function.update normalized who
      (policy.normalizeDisclosures setup.program config.registry config.revelations) =
      normalizeDisclosureProfile setup.program config.registry config.revelations
        (Function.update original who policy) := by
    funext player
    by_cases same : player = who
    · subst player
      simp only [Function.update_self, normalizeDisclosureProfile]
    · simp only [Function.update_of_ne same, normalized, normalizeDisclosureProfile, config,
        Setup.initialConfig]
  change SourceProgram.run setup.program (Function.update normalized who policy) initial =
    SourceProgram.run setup.program (Function.update original who policy) initial
  unfold SourceProgram.run
  change runFrom setup.program (Function.update normalized who policy) config =
    runFrom setup.program (Function.update original who policy) config
  rw [← own, profiles, normalizeDisclosureProfile_runFrom]

/-- **A permitted deviation has the typed outcome law of a source
deviation.** Against the timed calendar profile of an admitted source profile,
every deviation of one player within the permitted menu has exactly the typed
terminal-state law of the source run in which that player follows one source
behavioral policy admitted at the commitment interface. -/
theorem sourceServiceDeviation_readout_law
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (bounds : MessageBounds (graph setup)) (values : bounds.CoversBindingValues)
    (initialValues : ∀ state ∈ (initialLaw setup).support, bounds.CandidateValues state)
    (capacity : (graph setup).order.eventCount ≤ bounds.candidateCount)
    (rosters : (graph setup).EventId → List Player)
    (opportunities : BindingOpportunities setup rosters)
    (timing : TimingLaw setup rosters)
    (full : ∀ event who owned, FullSupport (timing event who owned))
    (network : (runtime setup).NetworkPolicy leaks)
    (original : BehavioralProfile setup.program)
    (permitted : ∀ who, (original who).Admitted setup.program
      (CommitmentInterface.values setup.program))
    (who : Player)
    (deviation : ((sourceServiceMenu setup leaks bounds rosters).information (initialLaw setup)
      (rosterPlan setup rosters).length
      (rosterScheduler setup leaks rosters network)).BehavioralPolicy who) :
    ∃ policy : BehavioralPolicy who setup.program,
      policy.Admitted setup.program (CommitmentInterface.values setup.program) ∧
      (((sourceServiceMenu setup leaks bounds rosters).information (initialLaw setup)
        (rosterPlan setup rosters).length
          (rosterScheduler setup leaks rosters network)).runBehavioral
        (Function.update (sourceServiceTimedProfile setup leaks bounds rosters network timing
          original) who deviation)
        (2 * (rosterPlan setup rosters).length + 1)).map
          (fun final => sourceReadout setup leaks final.state) =
        (setup.run (Function.update original who policy)).map some := by
  classical
  let menu := sourceServiceMenu setup leaks bounds rosters
  let horizon := (rosterPlan setup rosters).length
  let scheduler := rosterScheduler setup leaks rosters network
  let normalized := normalizeDisclosureProfile setup.program []
    (Revelations.initial setup.context) original
  have admitted := normalized_sourceService_admitted setup original permitted
  let native := (application setup leaks).decodePolicy
    (menu.embedPolicy (initialLaw setup) horizon scheduler who deviation)
  have lawful : ∀ past view response, response ∈ (native past view).support →
      response ∈ menu.actions who past view :=
    fun past view response member => menu.decode_embedPolicy_covered (initialLaw setup) horizon
      scheduler who deviation past view response member
  let players := Function.update (sourceServiceTimedPolicy setup leaks rosters timing normalized)
    who native
  have covered : ∀ player, menu.Admissible (initialLaw setup) horizon scheduler player
      (players player) := by
    intro player
    by_cases same : player = who
    · subst player
      intro control _ _ action member
      simp only [players, Function.update_self] at member
      exact lawful _ _ action member
    · simp only [players, Function.update_of_ne same]
      exact sourceServiceTimedPolicy_admissible setup leaks bounds values initialValues capacity
        rosters opportunities network timing full normalized admitted player
  have profiles : Function.update (sourceServiceTimedProfile setup leaks bounds rosters network
      timing original) who deviation =
      fun player => menu.restrictPolicy (initialLaw setup) horizon scheduler player
        (players player) := by
    funext player
    by_cases same : player = who
    · subst player
      simp only [players, Function.update_self]
      exact (menu.restrict_decode_embedPolicy (initialLaw setup) horizon scheduler who
        deviation).symm
    · simp only [players, Function.update_of_ne same, sourceServiceTimedProfile]
      rfl
  rw [profiles]
  have physical := roster_restrict_complete_state setup leaks rosters network menu players covered
  have observed := congrArg (PMF.map (sourceReadout setup leaks)) physical
  simp only [PMF.map_comp, Function.comp_def] at observed
  obtain ⟨policy, allowed, noise, joint⟩ := sourceServiceDeviation_initialized_prefix_factorization
    setup leaks bounds values capacity rosters opportunities timing network normalized who native
      lawful covered admitted
      (fun player => (original player).normalizeDisclosureFrom_effective setup.program []
        (Revelations.initial setup.context) (fun view => PMF.pure view.2))
      (eventCount setup.program) le_rfl
  refine ⟨policy, allowed, observed.trans ?_⟩
  have updatedAdmitted (player : Player) :
      (Function.update normalized who policy player).Admitted setup.program
        (CommitmentInterface.values setup.program) := by
    by_cases same : player = who
    · subst player
      simpa only [Function.update_self] using allowed
    · simpa only [Function.update_of_ne same] using admitted player
  have projected := congrArg (PMF.map (fun pair => setup.protocolReadout pair.1)) joint
  simp only [PMF.map_comp, Function.comp_def, PMF.map_bind, pmf_map_fun_const,
    pmf_bind_pure_eq_map] at projected
  have completed : rosterPlanPrefix setup rosters (eventCount setup.program) =
      rosterPlan setup rosters := by
    unfold rosterPlanPrefix rosterPlan
    rw [List.take_of_length_le (by rw [List.length_finRange]; exact le_rfl)]
  simp only [completed, sourceServicePrefix?_terminal_readout] at projected
  have encodedState := setup.encoded_prefix_state (CommitmentInterface.values setup.program)
    (Function.update normalized who policy) updatedAdmitted (eventCount setup.program)
  have sourceLaw := setup.protocol_runBehavioral_eq (CommitmentInterface.values setup.program)
    (Function.update normalized who policy) updatedAdmitted
  rw [InformationModel.runSingleMoverBehavioralFrom_eq_runBehavioralFrom] at sourceLaw
  have encodedReadout := congrArg (PMF.map setup.protocolReadout) encodedState
  simp only [PMF.map_comp, Function.comp_def, PMF.map_bind] at encodedReadout
  have terminal := projected.trans (encodedReadout.symm.trans (by
    simpa only [eventCount_eq_instructionCount, InformationModel.runBehavioral] using sourceLaw))
  rw [run_update_normalizeDisclosureProfile setup original who policy] at terminal
  simpa only [sourceReadout_eq_decode, PMF.map_bind] using terminal

end Vegas
