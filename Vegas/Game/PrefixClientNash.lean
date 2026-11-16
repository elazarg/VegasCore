module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Game.PrefixClientDeviation
public import Vegas.Game.PrefixClientOutcomeLaw
public import Vegas.Game.GraphForfeit
public import GameTheory.Core.UtilityTransfer

@[expose] public section

/-! # Intended Nash equilibrium on the native source-prefix service

The canonical source game bounds each native deviation. Honest native play has the
intended complete source-configuration law and no failed reveals, so the actual forfeited
payoff agrees with ordinary utility. Binding repair and forced source disclosure leave
the effective-opening physical clients unchanged, allowing every intended extension.
-/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

private theorem graphObservation_read_eq_serviceRankedReadout
    (setup : Setup (Player := Player) (L := L)) (deps : setup.dataflowGraph.Dependencies)
    (duration : (serviceGraph setup deps).EventId → Nat)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup deps)))
    {Parameter : Type} (parameter : State L setup.context → Parameter)
    (utility : Parameter × PublicOutcome setup.program → Player → ℝ) (excluded : Player → ℝ)
    (final : (serviceApplication setup deps duration leaks).Execution) :
    (setup.graphObservation deps parameter utility excluded final.application.config).1 =
      serviceRankedReadout setup deps duration leaks
        ((serviceApplication setup deps duration leaks).finished final) := by
  let G := serviceGraph setup deps
  let config := final.application.config
  unfold Setup.graphObservation serviceRankedReadout ReactiveApplication.finished
  simp only [Option.bind_some]
  by_cases terminal : config.cut.Terminal
  · simp only [show final.application.config.cut.Terminal from terminal, ↓reduceDIte, ↓reduceIte]
    let ranked := rankedConfig (graph := G) config terminal
    have storeEq : ranked.store = config.store := by
      funext field
      cases field <;> rfl
    have decoded := decodeConfig?_terminal setup.program
      ⟨ranked, rankedConfig_terminal (graph := G) config terminal⟩
    rw [storeEq] at decoded
    exact decoded.symm
  · simp only [show ¬ final.application.config.cut.Terminal from terminal, ↓reduceDIte, ↓reduceIte]

end Vegas

namespace Vegas

open SourceProgram SourceProgram.Setup EventGraph EventGraphRuntime Interaction GameTheory
  GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

private theorem graphForfeitConfigPayoff_eq_of_native_clean
    (setup : Setup (Player := Player) (L := L)) (deps : setup.dataflowGraph.Dependencies)
    (duration : (serviceGraph setup deps).EventId → Nat)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup deps)))
    {Parameter : Type} (parameter : State L setup.context → Parameter)
    (utility : Parameter × PublicOutcome setup.program → Player → ℝ) (forfeit : ℝ)
    (excluded : Player → ℝ) (final : (serviceApplication setup deps duration leaks).Execution)
    (terminal : final.application.config.cut.Terminal)
    (clear : final.application.config.defaulted = ∅)
    (source : Config Player L setup.program.terminalCtx)
    (read : serviceRankedReadout setup deps duration leaks
      ((serviceApplication setup deps duration leaks).finished final) = some source)
    (clean : ∀ who, failedReveals setup.program who (publicOutcome setup.program source) = 0) :
    setup.graphForfeitConfigPayoff deps parameter utility forfeit final.application.config =
      fun who => setup.graphPayoff deps parameter utility excluded who
        final.application.config := by
  let G := serviceGraph setup deps
  let outcome : G.gameSignature.Outcome := ⟨final.application.config, terminal⟩
  let ranked := rankedConfig (graph := G) final.application.config terminal
  have storeEq : ranked.store = final.application.config.store := by
    funext field
    cases field <;> rfl
  have decoded := decodeConfig?_terminal setup.program
    ⟨ranked, rankedConfig_terminal (graph := G) final.application.config terminal⟩
  change decodeConfig? _ _ _ _ _ _ ranked.store ranked.history =
    some (setup.graphReadout deps outcome) at decoded
  rw [storeEq] at decoded
  simp only [serviceRankedReadout, ReactiveApplication.finished, Option.bind_some,
    ite_eq_left terminal] at read
  have sourceEq : setup.graphReadout deps outcome = source :=
    Option.some.inj (decoded.symm.trans read)
  have sourceClear : (setup.graphReadout deps outcome).defaulted = ∅ := by
    change ranked.defaulted = ∅
    rw [defaulted_rankedConfig]
    exact clear
  rw [setup.graphForfeitConfigPayoff_terminal deps parameter utility forfeit _ terminal]
  funext who
  exact setup.graphForfeitPayoff_eq_graphPayoff_of_clean deps parameter utility forfeit excluded
    outcome who (by rw [sourceClear]; simp) (by rw [sourceEq]; exact clean who)

private theorem native_compileIntendedExtension_isεNash_of_comparison
    (setup : Setup (Player := Player) (L := L)) [Finite Player]
    (deps : setup.dataflowGraph.Dependencies)
    (relaxed : (serviceGraph setup deps).RevealRelaxedOrdered)
    (finite : setup.program.FiniteBindingTypes) [setup.FiniteInitialLaw]
    (wellFormed : setup.WellFormed) {Parameter : Type}
    (parameter : State L setup.context → Parameter)
    (utility : Parameter × PublicOutcome setup.program → Player → ℝ) (forfeit : ℝ)
    (range : ∀ high low who, utility high who - utility low who ≤ forfeit)
    (intended : Profile setup.intendedModel.behavioralSignature)
    (target : Profile (setup.informationModel
      (CommitmentInterface.forfeiture setup.program)).behavioralSignature)
    (agrees : (setup.intendedRestriction
      (CommitmentInterface.forfeiture setup.program)).ExtendsProfile intended target)
    (ε : ℝ)
    (equilibrium : IsεNash (setup.intendedModel.toBehavioralGameForm
      (instructionCount setup.program + 1))
      (fun final who => (setup.protocolReadout final.state).elim 0
        (fun state => utility (setup.parameterOutcome parameter state) who)) ε intended)
    (duration : (serviceGraph setup deps).EventId → Nat)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup deps)))
    {horizon turns : Nat}
    (scheduler : (serviceApplication setup deps duration leaks).Scheduler)
    (bound : (serviceGraph setup deps).EventId → Nat)
    {delay : (serviceGraph setup deps).EventId → Nat}
    (contract : AsyncContract (serviceTimeouts setup deps duration) leaks
      (serviceInitialLaw setup deps) horizon scheduler delay bound)
    (timely : AsyncTimely (serviceTimeouts setup deps duration) delay bound) :
    let app := serviceApplication setup deps duration leaks
    let admission := CommitmentInterface.forfeiture setup.program
    let repaired := setup.submittedSourceProfile (setup.disclosingSourceProfile target)
    let repairedSource := setup.decodeBehavioralProfile admission repaired
    let reference := setup.informationGraph.submitProfile
      (compileEventProfile setup.program repairedSource)
    let repairedClients := serviceReferenceTurnPolicy setup deps duration leaks bound turns
      (firstTurnTiming setup turns deps)
      (effectiveOpening ((serviceGraph setup deps).prefixProfile reference))
    (∀ focal (replacement : app.Policy), ∃ policy : setup.informationGraph.BehavioralPolicy focal,
      expect (app.roundsFrom (serviceInitialLaw setup deps) scheduler
        (Function.update repairedClients focal replacement) horizon)
        (fun final => setup.graphForfeitConfigPayoff deps parameter utility forfeit
          final.application.config focal) ≤
      expect ((setup.graphInputs setup.informationDependencies).bind
        (setup.informationGraph.runPolicies setup.informationGraph.canonicalScheduler
          (Function.update (setup.informationGraph.prefixProfile reference) focal policy)))
        (setup.graphPayoff setup.informationDependencies parameter utility
          (leastUtility utility) focal)) →
    let source := setup.decodeBehavioralProfile admission target
    let clients := serviceReferenceTurnPolicy setup deps duration leaks bound turns
      (firstTurnTiming setup turns deps)
      (effectiveOpening (compilePrescribedProfile setup.program deps source))
    let nativeGame := serviceGame setup deps duration leaks scheduler horizon
    IsεNash nativeGame (setup.graphForfeitConfigPayoff deps parameter utility forfeit) ε clients ∧
      (∀ final ∈ (app.roundsFrom (serviceInitialLaw setup deps) scheduler clients horizon).support,
        final.application.config.cut.Terminal ∧ final.application.config.defaulted = ∅ ∧
          ∃ terminal, serviceRankedReadout setup deps duration leaks (app.finished final) =
            some terminal ∧ ∀ who,
              failedReveals setup.program who (publicOutcome setup.program terminal) = 0) ∧
      (app.roundsFrom (serviceInitialLaw setup deps) scheduler clients horizon).map
        (fun final => ((setup.graphObservation deps parameter utility (leastUtility utility)
          final.application.config).1,
          setup.graphForfeitConfigPayoff deps parameter utility forfeit final.application.config)) =
        (setup.intendedModel.runBehavioral intended (instructionCount setup.program + 1)).map
          (fun final => (setup.protocolReadout final.state, fun who =>
            (setup.protocolReadout final.state).elim 0
              (fun terminal => utility (setup.parameterOutcome parameter terminal) who))) := by
  classical
  intro app admission repaired repairedSource reference repairedClients comparison source clients
    nativeGame
  let G := serviceGraph setup deps
  let sourceGame := setup.informationGraph.gameForm
    (setup.graphInputs setup.informationDependencies) setup.informationGraph.canonicalScheduler
  let sourceProfile := setup.informationGraph.prefixProfile reference
  let sourceUtility := fun outcome : sourceGame.sig.Outcome => fun who =>
    setup.graphPayoff setup.informationDependencies parameter utility (leastUtility utility) who
      outcome.1
  let nativeUtility := setup.graphForfeitConfigPayoff deps parameter utility forfeit
  have repairedAgrees : (setup.intendedRestriction admission).ExtendsProfile intended repaired :=
    setup.submittedSourceProfile_extends intended _
      (setup.disclosingSourceProfile_extends intended target agrees)
  have repairedDisclosing : ∀ who, Disclosing setup.program (repairedSource who) :=
    fun who => setup.submittedSourceProfile_disclosing _ who
      (setup.disclosingSourceProfile_disclosing target who)
  have clientsEq : repairedClients = clients := by
    change serviceReferenceTurnPolicy setup deps duration leaks bound turns
      (firstTurnTiming setup turns deps)
      (effectiveOpening (compilePrescribedProfile setup.program deps repairedSource)) = clients
    dsimp only [repairedSource, repaired, admission, source, clients]
    rw [setup.decodeBehavioralProfile_submittedSourceProfile,
      compilePrescribedProfile_submitBindings,
      setup.decodeBehavioralProfile_disclosingSourceProfile,
      effectiveOpening_compilePrescribedProfile_forceDisclose]
  have infoRelaxed : setup.informationGraph.RevealRelaxedOrdered :=
    setup.dataflowGraph.sequentialize_barrierOrdered.revealRelaxedOrdered
  have sourceNash : IsεNash sourceGame sourceUtility ε sourceProfile :=
    setup.isεNash_compileIntendedExtension setup.informationDependencies infoRelaxed finite
      wellFormed parameter utility (leastUtility utility)
      (fun outcome who => leastUtility_le utility range who outcome)
      intended repaired repairedAgrees repairedDisclosing ε equilibrium
      setup.informationGraph.canonicalScheduler
  have nativeLaw := native_compileIntendedExtension_law (turns := turns) setup deps relaxed
    wellFormed parameter utility (leastUtility utility) intended target agrees duration leaks
    scheduler bound contract timely
  have graphLaw := setup.compileIntendedExtension_law setup.informationDependencies infoRelaxed
    wellFormed parameter utility (leastUtility utility) intended repaired repairedAgrees
    repairedDisclosing setup.informationGraph.canonicalScheduler
  have nativeClean (final : app.Execution)
      (supported : final ∈ (app.roundsFrom (serviceInitialLaw setup deps) scheduler clients
        horizon).support) : nativeUtility final.application.config =
        fun who => setup.graphPayoff deps parameter utility (leastUtility utility) who
          final.application.config := by
    obtain ⟨terminal, clear, source, read, clean⟩ := nativeLaw.1 final supported
    exact graphForfeitConfigPayoff_eq_of_native_clean setup deps duration leaks parameter utility
      forfeit (leastUtility utility) final terminal clear source read clean
  have honestLaw : ((nativeGame.play clients).map fun config =>
      ((setup.graphObservation deps parameter utility (leastUtility utility) config).1,
        nativeUtility config)) =
      (sourceGame.play sourceProfile).map fun outcome =>
        (some (setup.graphReadout setup.informationDependencies outcome),
          sourceUtility outcome) := by
    change ((app.roundsFrom (serviceInitialLaw setup deps) scheduler clients horizon).map
      (fun final => final.application.config)).map _ = _
    rw [PMF.map_comp]
    have same : (app.roundsFrom (serviceInitialLaw setup deps) scheduler clients horizon).map
        (fun final => ((setup.graphObservation deps parameter utility (leastUtility utility)
          final.application.config).1, nativeUtility final.application.config)) =
        (app.roundsFrom (serviceInitialLaw setup deps) scheduler clients horizon).map
          (fun final => setup.graphObservation deps parameter utility (leastUtility utility)
            final.application.config) := by
      apply map_congr_on_support _
      intro final supported
      exact Prod.ext rfl (nativeClean final supported)
    exact same.trans (nativeLaw.2.trans graphLaw.symm)
  have nativeIntegral (who : Player) (law : PMF G.Config) :
      UtilityIntegrable nativeUtility who law :=
    setup.graphForfeitConfigPayoff_integrable deps parameter utility range who law
  have sourceIntegral (who : Player) (law : PMF sourceGame.sig.Outcome) :
      UtilityIntegrable sourceUtility who law := by
    obtain ⟨payoffBound, _nonnegative, bounded⟩ := setup.graphPayoff_abs_bound
      setup.informationDependencies parameter utility range who
    exact payoffIntegrable_of_bounded law _ (fun outcome => bounded outcome.1)
  have sourceExpect (players : setup.informationGraph.BehavioralProfile) (who : Player) :
      expect (sourceGame.play players) (fun outcome => sourceUtility outcome who) =
        expect ((setup.graphInputs setup.informationDependencies).bind
          (setup.informationGraph.runPolicies setup.informationGraph.canonicalScheduler players))
          (setup.graphPayoff setup.informationDependencies parameter utility
            (leastUtility utility) who) := by
    have law := congrArg (fun law => expect law (setup.graphPayoff setup.informationDependencies
      parameter utility (leastUtility utility) who))
      (setup.informationGraph.gameForm_play_map_val
        (setup.graphInputs setup.informationDependencies)
        setup.informationGraph.canonicalScheduler players)
    simp only [expect_map, Function.comp_def] at law
    exact law
  have equilibriumNative : IsεNash nativeGame nativeUtility ε clients := by
    apply GameForm.isεNash_of_deviation_bounds (source := sourceGame) (target := nativeGame)
      sourceProfile clients
      (sourceUtility := sourceUtility) (targetUtility := nativeUtility) _ _ ε sourceNash
    · intro who _hasExpectation
      refine ⟨(nativeIntegral who _).hasExpectation, ?_⟩
      rw [extendedExpectedUtility_eq (nativeIntegral who _),
        extendedExpectedUtility_eq (sourceIntegral who _)]
      have values := congrArg (fun law => expect law (fun observed => observed.2 who)) honestLaw
      simp only [expect_map, Function.comp_def] at values
      exact congrArg (fun value : ℝ => (value : EReal)) values
    · intro who replacement
      obtain ⟨policy, bound⟩ := comparison who replacement
      rw [clientsEq] at bound
      refine ⟨policy, fun _hasExpectation => ⟨(nativeIntegral who _).hasExpectation, ?_⟩⟩
      rw [extendedExpectedUtility_eq (nativeIntegral who _),
        extendedExpectedUtility_eq (sourceIntegral who _)]
      apply EReal.coe_le_coe_iff.mpr
      change expect ((app.roundsFrom (serviceInitialLaw setup deps) scheduler
        (Function.update clients who replacement) horizon).map
          (fun final => final.application.config)) (fun config => nativeUtility config who) ≤ _
      rw [expect_map]
      exact bound.trans_eq (sourceExpect (Function.update sourceProfile who policy) who).symm
  refine ⟨equilibriumNative, nativeLaw.1, ?_⟩
  have result : ((app.roundsFrom (serviceInitialLaw setup deps) scheduler clients horizon).map
      (fun final => final.application.config)).map (fun config =>
        ((setup.graphObservation deps parameter utility (leastUtility utility) config).1,
          nativeUtility config)) = _ := honestLaw.trans graphLaw
  simpa only [PMF.map_comp, Function.comp_def] using result

end Vegas

namespace Vegas

open SourceProgram SourceProgram.Setup EventGraph EventGraphRuntime Interaction GameTheory
  GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

/-- Effective-opening prescribed clients of every intended extension preserve its Nash
error against all raw native policies. Supported honest runs are terminal and have neither
defaults nor failed reveals; the actual ranked source readout and forfeited payoff vector
have exactly the intended joint law. No disclosure premise is required of the extension. -/
theorem native_compileIntendedExtension_preserved
    (setup : Setup (Player := Player) (L := L)) [Finite Player]
    (deps : setup.dataflowGraph.Dependencies)
    (relaxed : (serviceGraph setup deps).RevealRelaxedOrdered)
    (finite : setup.program.FiniteBindingTypes) [setup.FiniteInitialLaw]
    (wellFormed : setup.WellFormed) {Parameter : Type}
    (parameter : State L setup.context → Parameter)
    (utility : Parameter × PublicOutcome setup.program → Player → ℝ) (forfeit : ℝ)
    (range : ∀ high low who, utility high who - utility low who ≤ forfeit)
    (intended : Profile setup.intendedModel.behavioralSignature)
    (target : Profile (setup.informationModel
      (CommitmentInterface.forfeiture setup.program)).behavioralSignature)
    (agrees : (setup.intendedRestriction
      (CommitmentInterface.forfeiture setup.program)).ExtendsProfile intended target)
    (ε : ℝ)
    (equilibrium : IsεNash (setup.intendedModel.toBehavioralGameForm
      (instructionCount setup.program + 1))
      (fun final who => (setup.protocolReadout final.state).elim 0
        (fun state => utility (setup.parameterOutcome parameter state) who)) ε intended)
    (duration : (serviceGraph setup deps).EventId → Nat)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup deps)))
    {horizon turns : Nat}
    (scheduler : (serviceApplication setup deps duration leaks).Scheduler)
    (bound : (serviceGraph setup deps).EventId → Nat)
    {delay : (serviceGraph setup deps).EventId → Nat}
    (contract : AsyncContract (serviceTimeouts setup deps duration) leaks
      (serviceInitialLaw setup deps) horizon scheduler delay bound)
    (timely : AsyncTimely (serviceTimeouts setup deps duration) delay bound) :
    let app := serviceApplication setup deps duration leaks
    let admission := CommitmentInterface.forfeiture setup.program
    let source := setup.decodeBehavioralProfile admission target
    let clients := serviceReferenceTurnPolicy setup deps duration leaks bound turns
      (firstTurnTiming setup turns deps)
      (effectiveOpening (compilePrescribedProfile setup.program deps source))
    let nativeGame := serviceGame setup deps duration leaks scheduler horizon
    IsεNash nativeGame (setup.graphForfeitConfigPayoff deps parameter utility forfeit) ε clients ∧
      (∀ final ∈ (app.roundsFrom (serviceInitialLaw setup deps) scheduler clients horizon).support,
        final.application.config.cut.Terminal ∧ final.application.config.defaulted = ∅ ∧
          ∃ terminal, serviceRankedReadout setup deps duration leaks (app.finished final) =
            some terminal ∧ ∀ who,
              failedReveals setup.program who (publicOutcome setup.program terminal) = 0) ∧
      (app.roundsFrom (serviceInitialLaw setup deps) scheduler clients horizon).map
        (fun final => (serviceRankedReadout setup deps duration leaks
          (app.finished final),
          setup.graphForfeitConfigPayoff deps parameter utility forfeit final.application.config)) =
        (setup.intendedModel.runBehavioral intended (instructionCount setup.program + 1)).map
          (fun final => (setup.protocolReadout final.state, fun who =>
            (setup.protocolReadout final.state).elim 0
              (fun terminal => utility (setup.parameterOutcome parameter terminal) who))) := by
  classical
  intro app admission source clients nativeGame
  let forced := setup.disclosingSourceProfile target
  let repaired := setup.submittedSourceProfile forced
  have extension : (setup.intendedRestriction admission).ExtendsProfile intended repaired :=
    setup.submittedSourceProfile_extends intended forced
      (setup.disclosingSourceProfile_extends intended target agrees)
  have submits : ∀ who, SourceProgram.SubmitsBindings setup.program
      (setup.decodeBehavioralProfile admission repaired who) :=
    setup.submittedSourceProfile_submits forced
  have disclosing : ∀ who, Disclosing setup.program
      (setup.decodeBehavioralProfile admission repaired who) :=
    fun who => setup.submittedSourceProfile_disclosing forced who
      (setup.disclosingSourceProfile_disclosing target who)
  obtain ⟨nash, safety, law⟩ := native_compileIntendedExtension_isεNash_of_comparison setup deps
    relaxed finite wellFormed parameter utility forfeit range intended target agrees ε equilibrium
    duration leaks scheduler bound contract timely (fun focal replacement => by
      exact native_prefix_deviation_bound setup deps duration leaks horizon scheduler bound turns
        wellFormed relaxed contract timely intended repaired extension submits disclosing parameter
        utility forfeit range focal replacement)
  refine ⟨nash, safety, ?_⟩
  calc
    _ = (app.roundsFrom (serviceInitialLaw setup deps) scheduler clients horizon).map
        (fun final => ((setup.graphObservation deps parameter utility (leastUtility utility)
          final.application.config).1,
          setup.graphForfeitConfigPayoff deps parameter utility forfeit
            final.application.config)) := by
      apply map_congr_on_support _
      intro final _supported
      exact Prod.ext (graphObservation_read_eq_serviceRankedReadout setup deps duration leaks
        parameter utility (leastUtility utility) final).symm rfl
    _ = _ := law

end Vegas
