/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.AsyncDeviationLaw
import Vegas.Game.SourceServiceDeviationReadout

/-! # Typed outcome of one deviation under an arbitrary scheduler

Against the first-turn clients of a source profile, under a scheduler
satisfying the asynchronous contract, every native policy of one player has the
typed terminal-state law of the source run in which that player follows one
source behavioral policy (`Vegas.asyncDeviation_readout_law`). The policy may
bind failure, which the source represents as an unopenable commitment; the
forfeiture interface admits every such policy.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
open GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]

namespace SourceProgram

/-- An interface that admits forfeiture at every commitment admits every
policy. -/
theorem BehavioralPolicy.admitted_of_forfeiture {who : Player} :
    {Γ : SourceCtx Player L} → {O : Finset VarId} → (program : SourceProgram Player L Γ O) →
    (admission : CommitmentInterface program) →
    (∀ site, admission site = .forfeiture) → (policy : BehavioralPolicy who program) →
    policy.Admitted program admission
  | _, _, .ret _, _, _, _ => trivial
  | _, _, .sample _ _ _ next, admission, all, policy =>
      BehavioralPolicy.admitted_of_forfeiture next admission all policy
  | _, _, .commit _ _ _ _ next, admission, all, policy =>
      ⟨fun _ _ choice _ => by
        cases choice with
        | success value => exact CommitmentAdmission.admits_success _ value
        | failure => exact (CommitmentAdmission.admits_failure _).mpr (all none),
        BehavioralPolicy.admitted_of_forfeiture next (fun site => admission (some site))
          (fun site => all (some site)) policy.2⟩
  | _, _, .reveal _ _ _ _ _ _ next, admission, all, policy =>
      BehavioralPolicy.admitted_of_forfeiture next admission all policy.2

/-- The forfeiture interface admits every policy. -/
theorem BehavioralPolicy.admitted_forfeiture {who : Player} {Γ : SourceCtx Player L}
    {O : Finset VarId} (program : SourceProgram Player L Γ O)
    (policy : BehavioralPolicy who program) :
    policy.Admitted program (CommitmentInterface.forfeiture program) :=
  BehavioralPolicy.admitted_of_forfeiture program _ (fun _ => rfl) policy

end SourceProgram

section Phases

variable {setup : Setup (Player := Player) (L := L)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}

/-- Running to the horizon is running the completion phases of a list of
events, then on to the horizon. -/
theorem runToHorizon_eq_deviationPhases_bind (scheduler : (application setup leaks).Scheduler)
    (players : Player → (application setup leaks).Policy) (horizon : Nat) :
    ∀ (events : List (graph setup).EventId) (execution : (application setup leaks).Execution),
      (application setup leaks).runToHorizon scheduler players horizon execution =
        (deviationPhases scheduler players horizon events execution).bind
          ((application setup leaks).runToHorizon scheduler players horizon)
  | [], execution => by simp only [deviationPhases, PMF.pure_bind]
  | event :: rest, execution => by
      rw [(application setup leaks).runToHorizon_eq_runUntilHorizon_bind scheduler players
        (fun final => event ∈ final.application.config.cut.completed) horizon execution]
      simp only [deviationPhases, PMF.bind_bind]
      apply bind_congr_on_support _
      intro middle _
      exact runToHorizon_eq_deviationPhases_bind scheduler players horizon rest middle

/-- The completion phases of consecutive events from a completion boundary
within the horizon stop at completion boundaries within the horizon. -/
theorem deviationPhases_boundary {horizon : Nat}
    {scheduler : (application setup leaks).Scheduler}
    (complete : CompletesPlay (runtime setup) leaks (initialLaw setup) horizon scheduler)
    (players : Player → (application setup leaks).Policy) :
    ∀ (events : List (graph setup).EventId) (rank : Nat)
      (execution : (application setup leaks).Execution),
      (∀ index (inside : index < events.length), (events.get ⟨index, inside⟩).val = rank + index) →
      CompletionBoundary setup leaks scheduler players rank execution →
      execution.environmentRecall.length ≤ horizon →
      ∀ final ∈ (deviationPhases scheduler players horizon events execution).support,
        CompletionBoundary setup leaks scheduler players (rank + events.length) final ∧
          final.environmentRecall.length ≤ horizon
  | [], rank, execution, _, boundary, bounded, final, reached => by
      cases (PMF.mem_support_pure_iff _ _).mp reached
      exact ⟨boundary, bounded⟩
  | event :: rest, rank, execution, consecutive, boundary, bounded, final, reached => by
      simp only [deviationPhases] at reached
      obtain ⟨middle, moved, rest'⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
      have eventRank : event.val = rank := by simpa using consecutive 0 (by simp)
      have atRank : CompletionBoundary setup leaks scheduler players event.val execution := by
        rw [eventRank]
        exact boundary
      obtain ⟨_, _, _, middleBounded, middleBoundary⟩ := completionRun_boundary_step complete
        event execution atRank bounded middle moved
      rw [eventRank] at middleBoundary
      have later := deviationPhases_boundary complete players rest (rank + 1) middle
        (fun index inside => by
          have shifted := consecutive (index + 1) (by simp; omega)
          simp only [List.get_eq_getElem, List.getElem_cons_succ] at shifted
          simp only [List.get_eq_getElem]
          omega) middleBoundary middleBounded final rest'
      simpa only [List.length_cons, Nat.add_assoc, Nat.add_comm 1] using later

end Phases

variable [Fintype Player]

/-- The events of the whole program in order. -/
abbrev programEvents (setup : Setup (Player := Player) (L := L)) (count : Nat) :
    List (graph setup).EventId :=
  ((List.finRange (eventCount setup.program)).take count).map
    (outputEmbedding setup.program).event

/-- **Every initialized prefix of one deviation** has the state law of a source
deviation, jointly with the deviator's traffic, which depends on the source
state only through the deviator's source observation. -/
theorem asyncDeviation_initialized_prefix_factorization
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    {horizon : Nat} {scheduler : (application setup leaks).Scheduler}
    {delay bound : (graph setup).EventId → Nat}
    (contract : AsyncContract (runtime setup) leaks (initialLaw setup) horizon scheduler
      delay bound)
    (timely : AsyncTimely (runtime setup) delay bound) (turns : Nat)
    (profile : BehavioralProfile setup.program)
    (who : Player) (deviation : (application setup leaks).Policy)
    (effective : ∀ player, (profile player).EffectiveDisclosures setup.program []
      (Revelations.initial setup.context))
    (count : Nat) (within : count ≤ eventCount setup.program) :
    let players := deviatedTurnProfile bound turns (firstTurnTiming setup turns) profile who
      deviation
    ∃ policy : BehavioralPolicy who setup.program,
      ∃ noise : setup.ProtocolView who → PMF _,
        (((initialLaw setup).bind fun state => deviationPhases scheduler players horizon
          (programEvents setup count)
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
  have initialBoundary (seed : Seed) : CompletionBoundary setup leaks scheduler players 0
      (execution seed) := by
    refine ⟨?_, EventOrder.Cut.empty_isPrefix _, ?_⟩
    · change execution seed ∈ ((application setup leaks).roundsFrom (initialLaw setup) scheduler
        players 0).support
      unfold ReactiveApplication.roundsFrom
      simp only [ReactiveApplication.runRounds, initialLaw]
      exact (PMF.mem_support_bind_iff _ _ _).mpr ⟨_, (PMF.mem_support_map_iff _ _ _).mpr
        ⟨seed.val, seed.property, rfl⟩, (PMF.mem_support_pure_iff _ _).mpr rfl⟩
    · intro event _ observer entry member
      cases member
  obtain ⟨policy, noise, law⟩ := asyncDeviation_prefix_joint_factorization setup leaks contract
    timely turns profile who deviation count setup.program profile
      (ContextRefs.initial setup.context (outputLayout setup.program))
      (outputEmbedding setup.program) (initialRefsBefore setup.program) 0 prior source execution
      (fun _ => CompiledPolicySuffix.whole setup.program profile)
      (fun seed => SourceCheckpoint.initial setup seed.val)
      (fun seed _ => initialBoundary seed) (fun _ _ => Nat.zero_le _)
      (fun _ player => effective player) initialNoise factor within
  refine ⟨policy, noise, ?_⟩
  let combined := fun initial : State L setup.context =>
    (deviationPhases scheduler players horizon (programEvents setup count)
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
  rw [initialLaw, PMF.bind_map, PMF.map_bind]
  exact law


omit [Fintype Player] in
/-- The program's events are consecutive from the first. -/
theorem programEvents_consecutive (setup : Setup (Player := Player) (L := L)) (count : Nat)
    (index : Nat) (inside : index < (programEvents setup count).length) :
    ((programEvents setup count).get ⟨index, inside⟩).val = 0 + index := by
  have inProgram : index < eventCount setup.program := by
    simp only [programEvents, List.length_map, List.length_take, List.length_finRange] at inside
    omega
  have ranked := (CompiledPolicySuffix.whole setup.program
    (failureProfile setup.program)).graphSuffix.rankEq ⟨index, inProgram⟩
  simpa [programEvents] using ranked

omit [Fintype Player] in
/-- **One deviation has the typed outcome law of a source deviation.** Against
the first-turn clients of a source profile, under a scheduler satisfying the
asynchronous contract, every native policy of one player has exactly the typed
terminal-state law of the source run in which that player follows one source
behavioral policy, possibly binding failure, and every other player keeps its
source policy. -/
theorem asyncDeviation_readout_law [Finite Player]
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    {horizon : Nat} {scheduler : (application setup leaks).Scheduler}
    {delay bound : (graph setup).EventId → Nat}
    (contract : AsyncContract (runtime setup) leaks (initialLaw setup) horizon scheduler
      delay bound)
    (timely : AsyncTimely (runtime setup) delay bound) (turns : Nat)
    (original : BehavioralProfile setup.program)
    (who : Player) (deviation : (application setup leaks).Policy) :
    ∃ policy : BehavioralPolicy who setup.program,
      ((application setup leaks).roundsFrom (initialLaw setup) scheduler
        (deviatedTurnProfile bound turns (firstTurnTiming setup turns)
          (sourceServiceClientProfile setup original) who deviation) horizon).map
          (fun execution => sourceReadout setup leaks ((application setup leaks).finished
            execution)) =
        (setup.run (Function.update original who policy)).map some := by
  classical
  have := Fintype.ofFinite Player
  let app := application setup leaks
  let normalized := sourceServiceClientProfile setup original
  let players := deviatedTurnProfile bound turns (firstTurnTiming setup turns) normalized who
    deviation
  obtain ⟨policy, noise, joint⟩ := asyncDeviation_initialized_prefix_factorization setup leaks
    contract timely turns normalized who deviation
    (fun player => sourceServiceClientProfile_effective original player)
    (eventCount setup.program) le_rfl
  refine ⟨policy, ?_⟩
  -- The run to the horizon passes through every completion phase and then keeps the readout.
  have physical : (app.roundsFrom (initialLaw setup) scheduler players horizon).map
      (fun execution => sourceReadout setup leaks (app.finished execution)) =
      ((initialLaw setup).bind fun state => deviationPhases scheduler players horizon
        (programEvents setup (eventCount setup.program))
        (ReactiveApplication.Execution.initial app state)).map
          (fun final => sourceReadout setup leaks (app.finished final)) := by
    unfold ReactiveApplication.roundsFrom
    rw [PMF.map_bind, PMF.map_bind]
    apply bind_congr_on_support _
    intro state stateSupport
    have toHorizon : app.runRounds scheduler players horizon
        (ReactiveApplication.Execution.initial app state) =
        app.runToHorizon scheduler players horizon
          (ReactiveApplication.Execution.initial app state) := rfl
    rw [toHorizon, runToHorizon_eq_deviationPhases_bind scheduler players horizon
      (programEvents setup (eventCount setup.program)), PMF.map_bind]
    rw [← PMF.bind_pure_comp]
    apply bind_congr_on_support _
    intro final reached
    have initialBoundary : CompletionBoundary setup leaks scheduler players 0
        (ReactiveApplication.Execution.initial app state) := by
      refine ⟨?_, ?_, ?_⟩
      · change ReactiveApplication.Execution.initial app state ∈
          (app.roundsFrom (initialLaw setup) scheduler players 0).support
        unfold ReactiveApplication.roundsFrom
        exact (PMF.mem_support_bind_iff _ _ _).mpr ⟨state, stateSupport,
          (PMF.mem_support_pure_iff _ _).mpr rfl⟩
      · obtain ⟨initial, _, rfl⟩ := PMF.support_map .. ▸ stateSupport
        exact EventOrder.Cut.empty_isPrefix _
      · intro event _ observer entry member
        cases member
    obtain ⟨finalBoundary, _⟩ := deviationPhases_boundary contract.completes players
      (programEvents setup (eventCount setup.program)) 0 _
      (programEvents_consecutive setup (eventCount setup.program)) initialBoundary
      (Nat.zero_le _) final reached
    have terminal : final.application.config.cut.IsPrefix (graph setup).order.eventCount := by
      have ordered := finalBoundary.ordered
      simp only [programEvents, List.length_map, List.length_take, List.length_finRange,
        Nat.min_self, Nat.zero_add] at ordered
      exact ordered
    unfold ReactiveApplication.runToHorizon
    rw [map_congr_on_support _ (g := fun _ => sourceReadout setup leaks (app.finished final))
      (fun next moved => by
        have same := runRounds_config_terminal scheduler players _ final next terminal moved
        change sourceReadout setup leaks (some ⟨0, none, next⟩) =
          sourceReadout setup leaks (some ⟨0, none, final⟩)
        simp only [sourceReadout, Option.bind_some, same]), pmf_map_fun_const]
    rfl
  rw [physical]
  have projected := congrArg (PMF.map (fun pair => setup.protocolReadout pair.1)) joint
  simp only [PMF.map_comp, Function.comp_def, PMF.map_bind, pmf_map_fun_const,
    pmf_bind_pure_eq_map] at projected
  simp only [sourceServicePrefix?_terminal_readout] at projected
  have admitted (player : Player) :
      (Function.update normalized who policy player).Admitted setup.program
        (CommitmentInterface.forfeiture setup.program) :=
    BehavioralPolicy.admitted_forfeiture setup.program _
  have encodedState := setup.encoded_prefix_state (CommitmentInterface.forfeiture setup.program)
    (Function.update normalized who policy) admitted (eventCount setup.program)
  have sourceLaw := setup.protocol_runBehavioral_eq (CommitmentInterface.forfeiture setup.program)
    (Function.update normalized who policy) admitted
  rw [InformationModel.runSingleMoverBehavioralFrom_eq_runBehavioralFrom] at sourceLaw
  have encodedReadout := congrArg (PMF.map setup.protocolReadout) encodedState
  simp only [PMF.map_comp, Function.comp_def, PMF.map_bind] at encodedReadout
  have terminal := projected.trans (encodedReadout.symm.trans (by
    simpa only [eventCount_eq_instructionCount, InformationModel.runBehavioral] using sourceLaw))
  rw [run_update_normalizeDisclosureProfile setup original who policy] at terminal
  have readoutEq (final : app.Execution) : sourceReadout setup leaks (app.finished final) =
      decodeState? (terminalRefs setup.program) final.application.config.store :=
    sourceReadout_eq_decode setup leaks ⟨0, none, final⟩
  simp only [readoutEq, PMF.map_bind]
  exact terminal

end Vegas
