/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.RevealClosureSimulation
import Vegas.Game.ConcurrentRevealForfeit
import Vegas.Game.RevealServiceEffectiveOutcomeLaw

/-! # Nash equilibria of effective-opening clients with concurrent reveals

The forfeited payoff of a concurrent-reveal configuration, read in instruction
order, ignores the decisions of defaulted players and depends only on the
order-free key; at a terminal configuration it is the payoff of the concurrent
graph game. So the ledger payoff of a deviation from effective-opening clients
is the graph payoff of a deviation served last, which the graph equilibrium
bounds, and the honest ledger payoff is the honest graph payoff.
-/

noncomputable section

namespace Vegas

open SourceProgram GameTheory GameTheory.Math.Probability Interaction EventGraphRuntime EventGraph

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

/-- The forfeited payoff of a concurrent-reveal configuration read in
instruction order; an unfinished configuration pays nothing. -/
def concurrentConfigPayoff (setup : Setup (Player := Player) (L := L)) {Parameter : Type}
    (parameter : State L setup.context → Parameter)
    (utility : Parameter × PublicOutcome setup.program → Player → ℝ) (forfeit : ℝ)
    (config : (serviceGraph setup .concurrentReveals).Config) (who : Player) : ℝ :=
  (concurrentOutcome setup parameter config).elim 0 fun outcome =>
    forfeitUtility setup.program forfeit utility outcome who

/-- The payoff ignores the decisions of defaulted players. -/
theorem concurrentConfigPayoff_erase (setup : Setup (Player := Player) (L := L))
    {Parameter : Type} (parameter : State L setup.context → Parameter)
    (utility : Parameter × PublicOutcome setup.program → Player → ℝ) (forfeit : ℝ)
    (config : (serviceGraph setup .concurrentReveals).Config) :
    concurrentConfigPayoff setup parameter utility forfeit config.erase =
      concurrentConfigPayoff setup parameter utility forfeit config := by
  unfold concurrentConfigPayoff
  rw [concurrentOutcome_erase]

/-- The payoff depends only on the order-free key. -/
theorem concurrentConfigPayoff_congr (setup : Setup (Player := Player) (L := L))
    {Parameter : Type} (parameter : State L setup.context → Parameter)
    (utility : Parameter × PublicOutcome setup.program → Player → ℝ) (forfeit : ℝ)
    {left right : (serviceGraph setup .concurrentReveals).Config}
    (same : runKey left = runKey right) :
    concurrentConfigPayoff setup parameter utility forfeit left =
      concurrentConfigPayoff setup parameter utility forfeit right := by
  unfold concurrentConfigPayoff concurrentOutcome
  rw [concurrentRankedRead_congr setup same]

/-- A terminal configuration reads its graph readout. -/
theorem concurrentRankedRead_terminal (setup : Setup (Player := Player) (L := L))
    (config : (serviceGraph setup .concurrentReveals).Config) (terminal : config.cut.Terminal) :
    concurrentRankedRead setup config = some (setup.concurrentReadout ⟨config, terminal⟩) := by
  unfold concurrentRankedRead
  rw [ite_eq_left terminal]
  have storeEq : (setup.rankedConfig config terminal).store = config.store := by
    funext field
    cases field <;> rfl
  have decoded := decodeConfig?_terminal setup.program
    ⟨setup.rankedConfig config terminal, setup.rankedConfig_terminal config terminal⟩
  change decodeConfig? _ _ _ _ _ _ (setup.rankedConfig config terminal).store
    (setup.rankedConfig config terminal).history = _ at decoded
  rw [storeEq] at decoded
  exact decoded

/-- At a terminal configuration the payoff is the concurrent graph game's. -/
theorem concurrentConfigPayoff_terminal (setup : Setup (Player := Player) (L := L))
    {Parameter : Type} (parameter : State L setup.context → Parameter)
    (utility : Parameter × PublicOutcome setup.program → Player → ℝ) (forfeit : ℝ)
    (config : (serviceGraph setup .concurrentReveals).Config) (terminal : config.cut.Terminal) :
    concurrentConfigPayoff setup parameter utility forfeit config =
      setup.concurrentForfeitPayoff parameter utility forfeit ⟨config, terminal⟩ := by
  unfold concurrentConfigPayoff concurrentOutcome
  rw [concurrentRankedRead_terminal setup config terminal]
  rfl

/-- The payoff read from the typed terminal state and public defaults. -/
def concurrentStatePayoff (setup : Setup (Player := Player) (L := L)) {Parameter : Type}
    (parameter : State L setup.context → Parameter)
    (utility : Parameter × PublicOutcome setup.program → Player → ℝ) (forfeit : ℝ)
    (final : State L setup.program.terminalCtx × DefaultHistory Player) (who : Player) : ℝ :=
  forfeitUtility setup.program forfeit utility
    (parameter (initialState setup.program final.1), ⟨sourcePublicEnv final.1, final.2⟩) who

/-- The configuration payoff is the state payoff of the instruction-order read. -/
theorem concurrentConfigPayoff_eq_stateRead (setup : Setup (Player := Player) (L := L))
    {Parameter : Type} (parameter : State L setup.context → Parameter)
    (utility : Parameter × PublicOutcome setup.program → Player → ℝ) (forfeit : ℝ)
    (config : (serviceGraph setup .concurrentReveals).Config) :
    concurrentConfigPayoff setup parameter utility forfeit config =
      fun who => (concurrentStateRead setup
        (concurrentStatePayoff setup parameter utility forfeit) config).elim 0 fun pay =>
          pay who := by
  funext who
  unfold concurrentConfigPayoff concurrentOutcome concurrentStateRead
  cases concurrentRankedRead setup config <;> rfl

/-- The concurrent graph game's payoff law under the scheduler serving one player
last is the last-served payoff law from the initial configurations. -/
theorem play_payoff_eq_lastRun (setup : Setup (Player := Player) (L := L)) {Parameter : Type}
    (parameter : State L setup.context → Parameter)
    (utility : Parameter × PublicOutcome setup.program → Player → ℝ) (forfeit : ℝ)
    (who : Player) (profile : (serviceGraph setup .concurrentReveals).BehavioralProfile) :
    ((setup.concurrentRevealGraph.gameForm setup.concurrentInputs
        (setup.concurrentRevealGraph.lastScheduler who)).play profile).map
      (setup.concurrentForfeitPayoff parameter utility forfeit) =
    (serviceInitialLaw setup .concurrentReveals).bind fun state =>
      (lastRun profile who state.config).map
        (concurrentConfigPayoff setup parameter utility forfeit) := by
  change ((setup.initialLaw.map (fun initial => setup.eventInputs initial)).bind
      (fun inputs => setup.concurrentRevealGraph.terminalOutcomes
        (setup.concurrentRevealGraph.lastScheduler who) profile inputs)).map _ = _
  rw [PMF.map_bind, PMF.bind_map, serviceInitialLaw, PMF.bind_map]
  apply bind_congr_on_support _
  intro initial _
  simp only [Function.comp_apply]
  have payoffs : setup.concurrentForfeitPayoff parameter utility forfeit =
      concurrentConfigPayoff setup parameter utility forfeit ∘ Subtype.val := by
    funext outcome
    exact (concurrentConfigPayoff_terminal setup parameter utility forfeit outcome.1
      outcome.2).symm
  rw [payoffs, ← PMF.map_comp, terminalOutcomes_map_val]
  have initialRemaining : (EventGraph.Config.initial (setup.eventInputs initial) :
      (serviceGraph setup .concurrentReveals).Config).remaining =
        (serviceGraph setup .concurrentReveals).order.eventCount := by
    simp [EventGraph.Config.remaining, EventGraph.Config.initial, EventOrder.Cut.empty]
  unfold lastRun EventGraph.runPolicies EventGraph.run
  change _ = (EventGraph.runPlan _ _ (EventGraph.Config.initial (setup.eventInputs initial) :
    (serviceGraph setup .concurrentReveals).Config).remaining _).map _
  rw [initialRemaining]
  rfl

/-- A ready-independent profile has one payoff law under every public scheduler. -/
theorem ReadyIndependent.payoff_scheduler_congr (setup : Setup (Player := Player) (L := L))
    {Parameter : Type} (parameter : State L setup.context → Parameter)
    (utility : Parameter × PublicOutcome setup.program → Player → ℝ) (forfeit : ℝ)
    {profile : (serviceGraph setup .concurrentReveals).BehavioralProfile}
    (independent : ReadyIndependent profile)
    (first second : (serviceGraph setup .concurrentReveals).PublicScheduler)
    (config : (serviceGraph setup .concurrentReveals).Config) :
    ((serviceGraph setup .concurrentReveals).runPlan
        ((serviceGraph setup .concurrentReveals).policyPlan profile first) config.remaining
        config).map (concurrentConfigPayoff setup parameter utility forfeit) =
      ((serviceGraph setup .concurrentReveals).runPlan
        ((serviceGraph setup .concurrentReveals).policyPlan profile second) config.remaining
        config).map (concurrentConfigPayoff setup parameter utility forfeit) := by
  classical
  let read := fun key : RunKey (serviceGraph setup .concurrentReveals) =>
    if found : ∃ other : (serviceGraph setup .concurrentReveals).Config, runKey other = key then
      concurrentConfigPayoff setup parameter utility forfeit found.choose
    else fun _ => 0
  have factored : concurrentConfigPayoff setup parameter utility forfeit = read ∘ runKey := by
    funext current
    have found : ∃ other : (serviceGraph setup .concurrentReveals).Config,
        runKey other = runKey current := ⟨current, rfl⟩
    simp only [Function.comp_apply, read, dite_eq_left found]
    exact (concurrentConfigPayoff_congr setup parameter utility forfeit found.choose_spec).symm
  rw [factored, ← PMF.map_comp, ← PMF.map_comp,
    independent.runPlan_map_runKey first _ config rfl,
    independent.runPlan_map_runKey second _ config rfl]

/-- **The honest graph payoff law** under the scheduler serving one player last
is the source payoff law. -/
theorem honest_play_payoff_law (setup : Setup (Player := Player) (L := L)) {Parameter : Type}
    (parameter : State L setup.context → Parameter)
    (utility : Parameter × PublicOutcome setup.program → Player → ℝ) (forfeit : ℝ)
    (source : BehavioralProfile setup.program)
    (disclosing : ∀ who, Disclosing setup.program (source who)) (who : Player) :
    ((setup.concurrentRevealGraph.gameForm setup.concurrentInputs
        (setup.concurrentRevealGraph.lastScheduler who)).play
          (concurrentReference setup source)).map
      (setup.concurrentForfeitPayoff parameter utility forfeit) =
    (setup.run source).map fun final =>
      concurrentStatePayoff setup parameter utility forfeit (final.state, final.defaults) := by
  rw [play_payoff_eq_lastRun]
  have canonical : ∀ state : EventGraphRuntime.State (serviceGraph setup .concurrentReveals),
      (lastRun (concurrentReference setup source) who state.config).map
          (concurrentConfigPayoff setup parameter utility forfeit) =
        (outcomeLaw (concurrentReference setup source)
          (concurrentStateRead setup (concurrentStatePayoff setup parameter utility forfeit))
          state.config).map fun pay => fun player => pay.elim 0 fun vector => vector player := by
    intro state
    unfold lastRun outcomeLaw
    rw [ReadyIndependent.payoff_scheduler_congr setup parameter utility forfeit
      (concurrentReference_readyIndependent setup source disclosing) _
      (serviceGraph setup .concurrentReveals).canonicalScheduler, PMF.map_comp]
    congr 1
    funext config
    exact concurrentConfigPayoff_eq_stateRead setup parameter utility forfeit config
  simp only [canonical]
  rw [← PMF.map_bind, concurrentReference_initial_stateLaw, PMF.map_comp]
  rfl

/-- The concurrent-reveal service graph relaxes the rank order exactly between
independent reveals. -/
theorem concurrentReveals_relaxedOrder (setup : Setup (Player := Player) (L := L)) :
    RelaxedOrder (serviceGraph setup .concurrentReveals) := by
  intro prior event
  change prior ∈ (setup.eventGraph.withMode .concurrentReveals).order.predecessors event ↔ _
  rw [setup.eventGraph.withMode_concurrentReveals_predecessors prior event]
  constructor
  · rintro ⟨member, independent⟩
    exact ⟨setup.eventGraph.order.predecessor_lt member, independent⟩
  · rintro ⟨earlier, independent⟩
    exact ⟨setup.eventGraph_total prior event earlier, independent⟩

/-- **The honest ledger payoff law.** Effective-opening clients have the source
payoff law. -/
theorem ledger_honest_payoff_law (setup : Setup (Player := Player) (L := L)) {Parameter : Type}
    (parameter : State L setup.context → Parameter)
    (utility : Parameter × PublicOutcome setup.program → Player → ℝ) (forfeit : ℝ)
    (duration : (serviceGraph setup .concurrentReveals).EventId → Nat)
    (leaks : MessageNetwork.ObservationRule Player
      (WitnessedPacket (serviceGraph setup .concurrentReveals)))
    {horizon turns : Nat}
    {scheduler : (serviceApplication setup .concurrentReveals duration leaks).Scheduler}
    {delay bound : (serviceGraph setup .concurrentReveals).EventId → Nat}
    (contract : AsyncContract (serviceTimeouts setup .concurrentReveals duration) leaks
      (serviceInitialLaw setup .concurrentReveals) horizon scheduler delay bound)
    (timely : AsyncTimely (serviceTimeouts setup .concurrentReveals duration) delay bound)
    (source : BehavioralProfile setup.program)
    (disclosing : ∀ who, Disclosing setup.program (source who)) :
    ((serviceApplication setup .concurrentReveals duration leaks).roundsFrom
        (serviceInitialLaw setup .concurrentReveals) scheduler
        (serviceReferenceTurnPolicy setup .concurrentReveals duration leaks bound turns
          (firstTurnTiming setup turns .concurrentReveals)
          (concurrentEffectiveReference setup source)) horizon).map
      (fun final => concurrentConfigPayoff setup parameter utility forfeit
        final.application.config) =
    (setup.run source).map fun final =>
      concurrentStatePayoff setup parameter utility forfeit (final.state, final.defaults) := by
  have law := congrArg (PMF.map fun pay : Option (Player → ℝ) => fun player =>
      pay.elim 0 fun vector => vector player)
    (concurrentEffectiveClients_state_law setup duration leaks (turns := turns) contract timely
      source disclosing (concurrentStatePayoff setup parameter utility forfeit))
  rw [PMF.map_comp, PMF.map_comp] at law
  refine Eq.trans ?_ law
  congr 1
  funext final
  simp only [Function.comp_apply]
  rw [concurrentConfigPayoff_eq_stateRead]
  rfl

/-- **The ledger payoff law of a deviation.** Against effective-opening clients
of a disclosing profile, a deviation of one player has the last-served payoff law
of a normalized deviation of the always-open compiled profile. -/
theorem ledger_deviation_payoff_law (setup : Setup (Player := Player) (L := L))
    {Parameter : Type} (parameter : State L setup.context → Parameter)
    (utility : Parameter × PublicOutcome setup.program → Player → ℝ) (forfeit : ℝ)
    (duration : (serviceGraph setup .concurrentReveals).EventId → Nat)
    (leaks : MessageNetwork.ObservationRule Player
      (WitnessedPacket (serviceGraph setup .concurrentReveals)))
    {horizon turns : Nat}
    {scheduler : (serviceApplication setup .concurrentReveals duration leaks).Scheduler}
    {delay bound : (serviceGraph setup .concurrentReveals).EventId → Nat}
    (contract : AsyncContract (serviceTimeouts setup .concurrentReveals duration) leaks
      (serviceInitialLaw setup .concurrentReveals) horizon scheduler delay bound)
    (timely : AsyncTimely (serviceTimeouts setup .concurrentReveals duration) delay bound)
    (source : BehavioralProfile setup.program)
    (disclosing : ∀ who, Disclosing setup.program (source who))
    (who : Player)
    (deviation : (serviceApplication setup .concurrentReveals duration leaks).Policy) :
    ∃ policy : (serviceGraph setup .concurrentReveals).BehavioralPolicy who,
      ((serviceApplication setup .concurrentReveals duration leaks).roundsFrom
          (serviceInitialLaw setup .concurrentReveals) scheduler
          (Function.update (serviceReferenceTurnPolicy setup .concurrentReveals duration leaks
            bound turns (firstTurnTiming setup turns .concurrentReveals)
            (concurrentEffectiveReference setup source)) who deviation) horizon).map
        (fun final => concurrentConfigPayoff setup parameter utility forfeit
          final.application.config) =
      (serviceInitialLaw setup .concurrentReveals).bind fun state =>
        (lastRun ((serviceGraph setup .concurrentReveals).normalizeProfile
          (GameTheory.Profile.update (sig := (serviceGraph setup .concurrentReveals).gameSignature)
            (compileEventProfile setup.program source) who policy)) who state.config).map
          (concurrentConfigPayoff setup parameter utility forfeit) := by
  classical
  let G := serviceGraph setup .concurrentReveals
  let app := serviceApplication setup .concurrentReveals duration leaks
  have concurrent : G.RevealsOnlyConcurrent :=
    setup.eventGraph.withMode_concurrentReveals_revealsOnlyConcurrent setup.eventGraph_total
  obtain ⟨policy, law⟩ := closure_deviation_erased_law (duration := duration)
    (leaks := leaks) bound turns contract timely
    (effectiveOpening (compileEventProfile setup.program source))
    (concurrentEffectiveReference_decides setup source)
    (concurrentEffectiveReference_readyIndependent setup source) who deviation
    (fun policy => concurrent.lastIndependent_normalizeProfile_of_footprint _ who
      (effectiveOpening_update_footprint (graph := G) (compileEventProfile setup.program source) who
        policy))
    (concurrentReveals_relaxedOrder setup) concurrent
  refine ⟨policy, ?_⟩
  let read := fun key : RunKey G =>
    if found : ∃ other : G.Config, runKey other = key then
      concurrentConfigPayoff setup parameter utility forfeit found.choose
    else fun _ => 0
  have readKey (config : G.Config) :
      read (runKey config) = concurrentConfigPayoff setup parameter utility forfeit config := by
    have found : ∃ other : G.Config, runKey other = runKey config := ⟨config, rfl⟩
    simp only [read, dite_eq_left found]
    exact concurrentConfigPayoff_congr setup parameter utility forfeit found.choose_spec
  have readErasedKey (config : G.Config) :
      read (readErased (runKey config)) =
        concurrentConfigPayoff setup parameter utility forfeit config := by
    rw [readErased_runKey]
    unfold erasedKey
    rw [readKey, concurrentConfigPayoff_erase]
  have twins := erasureTwins_effectiveOpening (graph := G)
    (compileEventProfile setup.program source)
    (fun owner event actor publication observation active =>
      compileEventPolicy_publication setup.program owner (source owner) (disclosing owner) event
        actor publication observation active) who policy
  calc ((app.roundsFrom (serviceInitialLaw setup .concurrentReveals) scheduler
          (Function.update (serviceReferenceTurnPolicy setup .concurrentReveals duration leaks
            bound turns (firstTurnTiming setup turns .concurrentReveals)
            (concurrentEffectiveReference setup source)) who deviation) horizon).map
        (fun final => concurrentConfigPayoff setup parameter utility forfeit
          final.application.config))
      = ((serviceInitialLaw setup .concurrentReveals).bind fun state =>
          (app.runToHorizon scheduler
            (Function.update (serviceReferenceTurnPolicy setup .concurrentReveals duration leaks
              bound turns (firstTurnTiming setup turns .concurrentReveals)
              (concurrentEffectiveReference setup source)) who deviation) horizon
            (ReactiveApplication.Execution.initial app state)).map
              fun final => readErased (runKey final.application.config)).map read := by
        unfold ReactiveApplication.roundsFrom
        rw [PMF.map_bind, PMF.map_bind]
        apply bind_congr_on_support _
        intro state _
        unfold ReactiveApplication.runToHorizon
        rw [PMF.map_comp]
        have lengthZero : (ReactiveApplication.Execution.initial app state).environmentRecall.length
            = 0 := rfl
        rw [lengthZero, Nat.sub_zero]
        congr 1
        funext final
        exact (readErasedKey final.application.config).symm
    _ = ((serviceInitialLaw setup .concurrentReveals).bind fun state =>
          lastErasedLaw (G.lastDeviationProfile
            (effectiveOpening (compileEventProfile setup.program source)) who policy) who
            state.config).map read :=
        congrArg (fun law => law.map read) law
    _ = (serviceInitialLaw setup .concurrentReveals).bind fun state =>
          (lastRun (G.lastDeviationProfile
            (effectiveOpening (compileEventProfile setup.program source)) who policy) who
            state.config).map (concurrentConfigPayoff setup parameter utility forfeit) := by
        rw [PMF.map_bind]
        apply bind_congr_on_support _
        intro state _
        unfold lastErasedLaw
        rw [PMF.map_comp]
        congr 1
        funext config
        simp only [Function.comp_apply]
        unfold erasedKey
        rw [readKey, concurrentConfigPayoff_erase]
    _ = _ := by
        apply bind_congr_on_support _
        intro state _
        unfold lastRun
        exact twins.runPlan_map_of_erase_invariant (G.lastScheduler who)
          (concurrentConfigPayoff setup parameter utility forfeit)
          (concurrentConfigPayoff_erase setup parameter utility forfeit) _ _

/-- **Effective-opening clients are an approximate Nash equilibrium with
concurrent reveals.** For a well-formed setup with finitely many binding values
and a forfeit at least the payoff range, the first-turn effective-opening clients
of a disclosing extension of an `ε`-Nash equilibrium of the intended game keep
that equilibrium on the ledger with independent reveals concurrent, under every
public scheduler of the asynchronous service contract: no player gains more than
`ε` in the forfeited payoff read in instruction order by any native policy. -/
theorem concurrentEffectiveClients_deviation_bound (setup : Setup (Player := Player) (L := L))
    [Finite Player] (finite : setup.program.FiniteBindingTypes) [setup.FiniteInitialLaw]
    (wellFormed : setup.WellFormed) {Parameter : Type}
    (parameter : State L setup.context → Parameter)
    (utility : Parameter × PublicOutcome setup.program → Player → ℝ) (forfeit : ℝ)
    (range : ∀ high low who, utility high who - utility low who ≤ forfeit)
    (intended : Profile setup.intendedModel.behavioralSignature)
    (target : Profile (setup.informationModel
      (CommitmentInterface.forfeiture setup.program)).behavioralSignature)
    (agrees : (setup.intendedRestriction
      (CommitmentInterface.forfeiture setup.program)).ExtendsProfile intended target) (ε : ℝ)
    (equilibrium : IsεNash (setup.intendedModel.toBehavioralGameForm
        (instructionCount setup.program + 1))
      (fun final who => (setup.protocolReadout final.state).elim 0
        (fun state => utility (setup.parameterOutcome parameter state) who)) ε intended)
    (disclosing : ∀ who, Disclosing setup.program (setup.decodeBehavioralProfile
      (CommitmentInterface.forfeiture setup.program) target who))
    (duration : (serviceGraph setup .concurrentReveals).EventId → Nat)
    (leaks : MessageNetwork.ObservationRule Player
      (WitnessedPacket (serviceGraph setup .concurrentReveals)))
    {horizon turns : Nat}
    {scheduler : (serviceApplication setup .concurrentReveals duration leaks).Scheduler}
    {delay bound : (serviceGraph setup .concurrentReveals).EventId → Nat}
    (contract : AsyncContract (serviceTimeouts setup .concurrentReveals duration) leaks
      (serviceInitialLaw setup .concurrentReveals) horizon scheduler delay bound)
    (timely : AsyncTimely (serviceTimeouts setup .concurrentReveals duration) delay bound)
    (who : Player)
    (deviation : (serviceApplication setup .concurrentReveals duration leaks).Policy) :
    extendedExpectedUtility (fun final player =>
        concurrentConfigPayoff setup parameter utility forfeit final.application.config player)
      who ((serviceApplication setup .concurrentReveals duration leaks).roundsFrom
        (serviceInitialLaw setup .concurrentReveals) scheduler
        (Function.update (serviceReferenceTurnPolicy setup .concurrentReveals duration leaks bound
          turns (firstTurnTiming setup turns .concurrentReveals)
          (concurrentEffectiveReference setup (setup.decodeBehavioralProfile
            (CommitmentInterface.forfeiture setup.program) target))) who deviation) horizon) ≤
      extendedExpectedUtility (fun final player =>
        concurrentConfigPayoff setup parameter utility forfeit final.application.config player)
      who ((serviceApplication setup .concurrentReveals duration leaks).roundsFrom
        (serviceInitialLaw setup .concurrentReveals) scheduler
        (serviceReferenceTurnPolicy setup .concurrentReveals duration leaks bound turns
          (firstTurnTiming setup turns .concurrentReveals)
          (concurrentEffectiveReference setup (setup.decodeBehavioralProfile
            (CommitmentInterface.forfeiture setup.program) target))) horizon) + ε := by
  let G := serviceGraph setup .concurrentReveals
  let source := setup.decodeBehavioralProfile (CommitmentInterface.forfeiture setup.program) target
  obtain ⟨policy, deviationLaw⟩ := ledger_deviation_payoff_law setup parameter utility forfeit
    duration leaks (turns := turns) contract timely source disclosing who deviation
  have graphNash := (setup.concurrentReveal_intended_forfeit finite wellFormed parameter utility
    forfeit range intended target agrees ε equilibrium disclosing (G.lastScheduler who)).1
  rw [isεNash_iff] at graphNash
  obtain ⟨_, _, bound⟩ := graphNash who (G.normalizePolicy who policy)
  rw [← G.normalizeProfile_update] at bound
  have viaPayoffs
      (law : PMF (serviceApplication setup .concurrentReveals duration leaks).Execution) :
      extendedExpectedUtility (fun final player =>
          concurrentConfigPayoff setup parameter utility forfeit final.application.config player)
        who law =
      extendedExpectedUtility (fun pay player => pay player) who
        (law.map fun final => concurrentConfigPayoff setup parameter utility forfeit
          final.application.config) := by
    rw [extendedExpectedUtility_map]
  have viaGame (profile : G.BehavioralProfile) :
      extendedExpectedUtility (setup.concurrentForfeitPayoff parameter utility forfeit) who
        ((setup.concurrentRevealGraph.gameForm setup.concurrentInputs
          (setup.concurrentRevealGraph.lastScheduler who)).play profile) =
      extendedExpectedUtility (fun pay player => pay player) who
        (((setup.concurrentRevealGraph.gameForm setup.concurrentInputs
          (setup.concurrentRevealGraph.lastScheduler who)).play profile).map
            (setup.concurrentForfeitPayoff parameter utility forfeit)) := by
    rw [extendedExpectedUtility_map]
  rw [viaPayoffs, viaPayoffs, deviationLaw,
    ledger_honest_payoff_law setup parameter utility forfeit duration leaks contract timely source
      disclosing,
    ← play_payoff_eq_lastRun setup parameter utility forfeit who,
    ← honest_play_payoff_law setup parameter utility forfeit source disclosing who,
    ← viaGame, ← viaGame]
  exact bound

/-- **The ledger game with concurrent reveals.** Each player chooses a native
ledger policy; the outcome is the configuration reached by the horizon. -/
def concurrentLedgerGame (setup : Setup (Player := Player) (L := L))
    (duration : (serviceGraph setup .concurrentReveals).EventId → Nat)
    (leaks : MessageNetwork.ObservationRule Player
      (WitnessedPacket (serviceGraph setup .concurrentReveals)))
    (scheduler : (serviceApplication setup .concurrentReveals duration leaks).Scheduler)
    (horizon : Nat) : GameForm Player where
  sig := { Strategy := fun _ => (serviceApplication setup .concurrentReveals duration leaks).Policy
           Outcome := (serviceGraph setup .concurrentReveals).Config }
  play profile := ((serviceApplication setup .concurrentReveals duration leaks).roundsFrom
    (serviceInitialLaw setup .concurrentReveals) scheduler profile horizon).map
      fun final => final.application.config

/-- The effective-opening clients of a source profile: each player opens a
reveal at its first opportunity exactly when the opening would be accepted. -/
def concurrentLedgerClients (setup : Setup (Player := Player) (L := L))
    (duration : (serviceGraph setup .concurrentReveals).EventId → Nat)
    (leaks : MessageNetwork.ObservationRule Player
      (WitnessedPacket (serviceGraph setup .concurrentReveals)))
    (bound : (serviceGraph setup .concurrentReveals).EventId → Nat) (turns : Nat)
    (source : BehavioralProfile setup.program) :
    Player → (serviceApplication setup .concurrentReveals duration leaks).Policy :=
  serviceReferenceTurnPolicy setup .concurrentReveals duration leaks bound turns
    (firstTurnTiming setup turns .concurrentReveals) (concurrentEffectiveReference setup source)

/-- Every expectation of a payoff bounded above exists. -/
private theorem hasExpectation_of_le {α : Type*} {law : PMF α} {pay : α → ℝ} {top : ℝ}
    (below : ∀ outcome, pay outcome ≤ top) : HasExpectation law pay := by
  rw [← hasExpectation_neg_iff, ← hasExpectation_affine_iff (c := 1) top one_pos]
  exact hasExpectation_of_nonneg fun outcome _ => by linarith [below outcome]

/-- The configuration payoff is bounded above when the forfeit is at least the
payoff range. -/
private theorem concurrentConfigPayoff_le (setup : Setup (Player := Player) (L := L))
    {Parameter : Type} (parameter : State L setup.context → Parameter)
    (utility : Parameter × PublicOutcome setup.program → Player → ℝ) (forfeit : ℝ)
    (range : ∀ high low who, utility high who - utility low who ≤ forfeit) (who : Player) :
    ∃ top, ∀ config, concurrentConfigPayoff setup parameter utility forfeit config who ≤ top := by
  classical
  by_cases inhabited : Nonempty (Parameter × PublicOutcome setup.program)
  · obtain ⟨anchor⟩ := inhabited
    have nonneg : 0 ≤ forfeit := by simpa using range anchor anchor who
    refine ⟨max 0 (utility anchor who + forfeit), fun config => ?_⟩
    unfold concurrentConfigPayoff
    cases concurrentOutcome setup parameter config with
    | none => exact le_max_left _ _
    | some outcome =>
        simp only [Option.elim, forfeitUtility]
        have := range outcome anchor who
        have : 0 ≤ forfeit * (failedReveals setup.program who outcome.2 : ℝ) :=
          mul_nonneg nonneg (Nat.cast_nonneg _)
        exact le_max_of_le_right (by linarith)
  · refine ⟨0, fun config => ?_⟩
    unfold concurrentConfigPayoff
    cases concurrentOutcome setup parameter config with
    | none => exact le_rfl
    | some outcome => exact (inhabited ⟨outcome⟩).elim

/-- **Nash equilibria of the intended game are preserved on the ledger with
concurrent reveals.** For a well-formed program with finitely many binding
values and a forfeit at least the payoff range,
the effective-opening clients of a disclosing extension of an `ε`-Nash
equilibrium of the intended game are an `ε`-Nash equilibrium of the ledger game
under every scheduler satisfying the asynchronous service contract. -/
theorem concurrentReveal_ledger_isεNash (setup : Setup (Player := Player) (L := L))
    [Finite Player] (finite : setup.program.FiniteBindingTypes) [setup.FiniteInitialLaw]
    (wellFormed : setup.WellFormed) {Parameter : Type}
    (parameter : State L setup.context → Parameter)
    (utility : Parameter × PublicOutcome setup.program → Player → ℝ) (forfeit : ℝ)
    (range : ∀ high low who, utility high who - utility low who ≤ forfeit)
    (intended : Profile setup.intendedModel.behavioralSignature)
    (target : Profile (setup.informationModel
      (CommitmentInterface.forfeiture setup.program)).behavioralSignature)
    (agrees : (setup.intendedRestriction
      (CommitmentInterface.forfeiture setup.program)).ExtendsProfile intended target) (ε : ℝ)
    (equilibrium : IsεNash (setup.intendedModel.toBehavioralGameForm
        (instructionCount setup.program + 1))
      (fun final who => (setup.protocolReadout final.state).elim 0
        (fun state => utility (setup.parameterOutcome parameter state) who)) ε intended)
    (disclosing : ∀ who, Disclosing setup.program (setup.decodeBehavioralProfile
      (CommitmentInterface.forfeiture setup.program) target who))
    (duration : (serviceGraph setup .concurrentReveals).EventId → Nat)
    (leaks : MessageNetwork.ObservationRule Player
      (WitnessedPacket (serviceGraph setup .concurrentReveals)))
    {horizon turns : Nat}
    {scheduler : (serviceApplication setup .concurrentReveals duration leaks).Scheduler}
    {delay bound : (serviceGraph setup .concurrentReveals).EventId → Nat}
    (contract : AsyncContract (serviceTimeouts setup .concurrentReveals duration) leaks
      (serviceInitialLaw setup .concurrentReveals) horizon scheduler delay bound)
    (timely : AsyncTimely (serviceTimeouts setup .concurrentReveals duration) delay bound) :
    IsεNash (concurrentLedgerGame setup duration leaks scheduler horizon)
      (concurrentConfigPayoff setup parameter utility forfeit) ε
      (concurrentLedgerClients setup duration leaks bound turns
        (setup.decodeBehavioralProfile (CommitmentInterface.forfeiture setup.program) target)) := by
  rw [isεNash_iff]
  intro who replacement
  obtain ⟨top, below⟩ := concurrentConfigPayoff_le setup parameter utility forfeit range who
  refine ⟨hasExpectation_of_le below, hasExpectation_of_le below, ?_⟩
  change extendedExpectedUtility (concurrentConfigPayoff setup parameter utility forfeit) who
      (((serviceApplication setup .concurrentReveals duration leaks).roundsFrom
        (serviceInitialLaw setup .concurrentReveals) scheduler
        (Function.update (concurrentLedgerClients setup duration leaks bound turns
          (setup.decodeBehavioralProfile (CommitmentInterface.forfeiture setup.program) target))
          who replacement) horizon).map fun final => final.application.config) ≤
    extendedExpectedUtility (concurrentConfigPayoff setup parameter utility forfeit) who
      (((serviceApplication setup .concurrentReveals duration leaks).roundsFrom
        (serviceInitialLaw setup .concurrentReveals) scheduler
        (concurrentLedgerClients setup duration leaks bound turns
          (setup.decodeBehavioralProfile (CommitmentInterface.forfeiture setup.program) target))
          horizon).map fun final => final.application.config) + ε
  rw [extendedExpectedUtility_map, extendedExpectedUtility_map]
  exact concurrentEffectiveClients_deviation_bound setup finite wellFormed parameter utility
    forfeit range intended target agrees ε equilibrium disclosing duration leaks contract timely
    who replacement

end Vegas
