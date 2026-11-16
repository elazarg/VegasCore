module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Game.RevealConcurrentNash

@[expose] public section

/-! # Intended equilibrium and complete readout on the concurrent-reveal ledger

The effective-opening clients preserve the intended joint law of the complete
source configuration and payoff vector. Their erased readout has the graph
law. That law has no defaults, so erasure changes no supported configuration
and the complete readout, including own-action recall, is preserved as well.
-/

noncomputable section

namespace Vegas

open SourceProgram GameTheory GameTheory.Math.Probability Interaction EventGraphRuntime EventGraph

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

/-- Intended approximate Nash equilibria have effective-opening ledger clients
with the same complete source-configuration/payoff law and no public default
or failed reveal, under every timely asynchronous service scheduler. -/
theorem concurrentReveal_intended_ledger (setup : Setup (Player := Player) (L := L))
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
    (duration : setup.revealRelaxedGraph.EventId → Nat)
    (leaks : MessageNetwork.ObservationRule Player
      (WitnessedPacket setup.revealRelaxedGraph))
    {horizon turns : Nat}
    {scheduler : (serviceApplication setup setup.revealDependencies duration leaks).Scheduler}
    {delay bound : setup.revealRelaxedGraph.EventId → Nat}
    (contract : AsyncContract (serviceTimeouts setup setup.revealDependencies duration) leaks
      (serviceInitialLaw setup setup.revealDependencies) horizon scheduler delay bound)
    (timely : AsyncTimely (serviceTimeouts setup setup.revealDependencies duration) delay bound) :
    IsεNash (concurrentLedgerGame setup duration leaks scheduler horizon)
        (concurrentConfigPayoff setup parameter utility forfeit) ε
        (concurrentLedgerClients setup duration leaks bound turns
          (setup.decodeBehavioralProfile (CommitmentInterface.forfeiture setup.program) target)) ∧
      (∀ config ∈ ((concurrentLedgerGame setup duration leaks scheduler horizon).play
          (concurrentLedgerClients setup duration leaks bound turns
            (setup.decodeBehavioralProfile (CommitmentInterface.forfeiture setup.program)
              target))).support,
        config.cut.Terminal ∧ config.defaulted = ∅ ∧ ∃ terminal,
          concurrentRankedRead setup config = some terminal ∧
            ∀ who, failedReveals setup.program who (publicOutcome setup.program terminal) = 0) ∧
      (((concurrentLedgerGame setup duration leaks scheduler horizon).play
          (concurrentLedgerClients setup duration leaks bound turns
            (setup.decodeBehavioralProfile (CommitmentInterface.forfeiture setup.program)
              target))).map fun config =>
            (concurrentRankedRead setup config,
              concurrentConfigPayoff setup parameter utility forfeit config)) =
        (setup.intendedModel.runBehavioral intended (instructionCount setup.program + 1)).map
          (fun final => (setup.protocolReadout final.state, fun who =>
            (setup.protocolReadout final.state).elim 0
              (fun state => utility (setup.parameterOutcome parameter state) who))) := by
  classical
  let G := setup.revealRelaxedGraph
  let source := setup.decodeBehavioralProfile (CommitmentInterface.forfeiture setup.program) target
  let reference := concurrentReference setup source
  let graphPlay := (G.gameForm (setup.graphInputs setup.revealDependencies)
      G.canonicalScheduler).play reference
  let ledgerPlay := (concurrentLedgerGame setup duration leaks scheduler horizon).play
    (concurrentLedgerClients setup duration leaks bound turns source)
  let observe := fun config : G.Config =>
    (concurrentRankedRead setup config.erase,
      concurrentConfigPayoff setup parameter utility forfeit config)
  have keyed : ∀ left right : G.Config, runKey left = runKey right →
      observe left = observe right := fun left right same =>
    Prod.ext (concurrentRankedRead_congr setup (erasedKey_congr same))
      (concurrentConfigPayoff_congr setup parameter utility forfeit same)
  have invariant : ∀ config : G.Config, observe config.erase = observe config := by
    intro config
    simp only [observe, EventGraph.Config.erase_erase, concurrentConfigPayoff_erase]
  have physical := effective_roundsFrom_outcomeLaw (duration := duration) (leaks := leaks)
    (turns := turns) contract timely
    (setup.informationGraph.relaxReveals_revealsOnlyConcurrent setup.informationGraph_total)
    (fun _ notPublication => setup.informationGraph.relaxReveals_leading
      setup.informationGraph_total notPublication)
    (concurrentEffectiveReference setup source)
    (concurrentEffectiveReference_readyIndependent setup source)
    (concurrentEffectiveReference_decides setup source)
    reference (concurrentReference_readyIndependent setup source disclosing)
    (concurrentReference_opensPublications setup source disclosing)
    observe keyed invariant
    (concurrentEffectiveReference_outcomeLaw setup source disclosing observe invariant)
  have physicalLaw : ledgerPlay.map observe =
      graphPlay.map (fun outcome => observe outcome.1) := by
    change (((serviceApplication setup setup.revealDependencies duration leaks).roundsFrom
      (serviceInitialLaw setup setup.revealDependencies) scheduler
      (concurrentLedgerClients setup duration leaks bound turns source) horizon).map
        (fun final => final.application.config)).map observe = _
    rw [PMF.map_comp]
    exact physical.trans
      (service_play_outcomeLaw setup setup.revealDependencies reference observe).symm
  obtain ⟨_, graphClean, graphLaw⟩ := setup.concurrentReveal_intended_forfeit finite wellFormed
    parameter utility forfeit range intended target agrees ε equilibrium disclosing
    G.canonicalScheduler
  have graphDefaults : ∀ outcome ∈ graphPlay.support, outcome.1.defaulted = ∅ := by
    intro outcome supported
    have clean := (graphClean outcome supported).1
    change (rankedConfig (graph := setup.revealRelaxedGraph) outcome.1 outcome.2).defaulted = ∅
        at clean
    rwa [defaulted_rankedConfig] at clean
  have graphObserve : ∀ outcome ∈ graphPlay.support,
      observe outcome.1 = (some (setup.graphReadout setup.revealDependencies outcome),
        setup.graphForfeitPayoff setup.revealDependencies parameter utility forfeit outcome) := by
    intro outcome supported
    simp only [observe, outcome.1.erase_eq_of_defaulted_empty (graphDefaults outcome supported),
      concurrentRankedRead_terminal setup outcome.1 outcome.2,
      concurrentConfigPayoff_terminal setup parameter utility forfeit outcome.1 outcome.2]
    rfl
  have represented : ∀ config ∈ ledgerPlay.support,
      ∃ outcome ∈ graphPlay.support, observe config =
        (some (setup.graphReadout setup.revealDependencies outcome),
          setup.graphForfeitPayoff setup.revealDependencies parameter utility forfeit outcome) := by
    intro config supported
    have member : observe config ∈ (ledgerPlay.map observe).support :=
      (PMF.mem_support_map_iff _ _ _).mpr ⟨config, supported, rfl⟩
    rw [physicalLaw] at member
    obtain ⟨outcome, present, same⟩ := (PMF.mem_support_map_iff _ _ _).mp member
    exact ⟨outcome, present, same.symm.trans (graphObserve outcome present)⟩
  have ledgerDefaults : ∀ config ∈ ledgerPlay.support, config.defaulted = ∅ := by
    intro config supported
    obtain ⟨outcome, present, same⟩ := represented config supported
    have read := congrArg Prod.fst same
    change concurrentRankedRead setup config.erase = some (setup.graphReadout
        setup.revealDependencies outcome)
      at read
    have terminal : config.cut.Terminal := by
      by_contra unfinished
      have notErased : ¬ config.erase.cut.Terminal := unfinished
      rw [concurrentRankedRead, ite_eq_right notErased] at read
      cases read
    rw [concurrentRankedRead_terminal setup config.erase terminal] at read
    have defaults := congrArg (fun final : Config Player L setup.program.terminalCtx =>
      final.defaulted) (Option.some.inj read)
    change (rankedConfig (graph := setup.revealRelaxedGraph) config.erase terminal).defaulted =
      (setup.graphReadout setup.revealDependencies outcome).defaulted at defaults
    rw [defaulted_rankedConfig, EventGraph.Config.erase_defaulted,
      (graphClean outcome present).1] at defaults
    exact defaults
  refine ⟨concurrentReveal_ledger_isεNash setup finite wellFormed parameter utility forfeit range
    intended target agrees ε equilibrium disclosing duration leaks contract timely, ?_, ?_⟩
  · intro config supported
    obtain ⟨outcome, present, same⟩ := represented config supported
    have reads := congrArg Prod.fst same
    change concurrentRankedRead setup config.erase = some (setup.graphReadout
        setup.revealDependencies outcome)
      at reads
    rw [config.erase_eq_of_defaulted_empty (ledgerDefaults config supported)] at reads
    refine ⟨?_, ledgerDefaults config supported, setup.graphReadout setup.revealDependencies
        outcome, reads,
      (graphClean outcome present).2⟩
    by_contra unfinished
    rw [concurrentRankedRead, ite_eq_right unfinished] at reads
    cases reads
  · calc
      _ = ledgerPlay.map observe := map_congr_on_support _ fun config supported => by
        simp only [observe, config.erase_eq_of_defaulted_empty (ledgerDefaults config supported)]
      _ = graphPlay.map (fun outcome => observe outcome.1) := physicalLaw
      _ = _ := (map_congr_on_support _ graphObserve).trans graphLaw

end Vegas
