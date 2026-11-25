module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Game.GraphForfeit
public import Vegas.Game.SourceReplayDebt
public import Vegas.Game.SourceServiceCompletion

@[expose] public section

/-! # Native forfeiture after irrevocable failure

An actual public default or source debt witnessed by matching own binding
records bounds every later raw native continuation by the source exit utility.
The runtime contract supplies terminal support; the utility spread supplies
integrability for arbitrary physical traffic and behavioral policies.
-/

noncomputable section

namespace Vegas

open SourceProgram SourceProgram.Setup EventGraphRuntime EventGraph Interaction
  GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)} {deps : setup.dataflowGraph.Dependencies}
  {duration : (serviceGraph setup deps).EventId → Nat}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup deps))}

private theorem runToHorizon_terminal_path
    {horizon : Nat} (scheduler : (serviceApplication setup deps duration leaks).Scheduler)
    {delay bound : (serviceGraph setup deps).EventId → Nat}
    (contract : AsyncContract (serviceTimeouts setup deps duration) leaks
      (serviceInitialDistribution setup deps) horizon scheduler delay bound)
    (players : Player → (serviceApplication setup deps duration leaks).Policy)
    (current final : (serviceApplication setup deps duration leaks).Execution)
    (supported : current ∈ ((serviceApplication setup deps duration leaks).roundsFrom
      (serviceInitialDistribution setup deps) scheduler players
        current.environmentRecall.length).support)
    (bounded : current.environmentRecall.length ≤ horizon)
    (reached : final ∈ ((serviceApplication setup deps duration leaks).runToHorizon scheduler
      players horizon current).support) :
    final.application.config.cut.Terminal ∧
      Relation.ReflTransGen EventGraph.Config.Step current.application.config
        final.application.config ∧
      ∃ inputs, final.application.config.Reachable inputs := by
  let app := serviceApplication setup deps duration leaks
  let count := horizon - current.environmentRecall.length
  have rounds : final ∈ (app.runRounds scheduler players count current).support := reached
  obtain ⟨trace⟩ := app.raw_trace_roundsFrom (serviceInitialDistribution setup deps) horizon
    scheduler
    players current.environmentRecall.length bounded current supported
  obtain ⟨finalTrace⟩ := app.raw_trace_runRounds (serviceInitialDistribution setup deps) horizon
    scheduler
    players 0 count current final (by simpa only [Nat.zero_add] using trace) rounds
  have terminal : final.application.config.cut.Terminal := contract.completes
    ⟨0, none, final⟩ finalTrace ⟨rfl, rfl⟩
  have actualTrace := finalTrace
  rw [serviceInitialDistribution_eq_inputs setup] at actualTrace
  obtain ⟨input, _inputMember, valid⟩ := reactive_history_invariant
    (serviceTimeouts setup deps duration) leaks (setup.initialDistribution.map setup.eventInputs)
    horizon scheduler actualTrace
  refine ⟨terminal, ?_, input, valid.reachable⟩
  exact reactive_runRounds_graph_steps (serviceTimeouts setup deps duration) leaks scheduler
    players count current final rounds

private theorem runToHorizon_forfeit_floor_of_defaulted
    {horizon : Nat} (scheduler : (serviceApplication setup deps duration leaks).Scheduler)
    {delay bound : (serviceGraph setup deps).EventId → Nat}
    (contract : AsyncContract (serviceTimeouts setup deps duration) leaks
      (serviceInitialDistribution setup deps) horizon scheduler delay bound)
    (players : Player → (serviceApplication setup deps duration leaks).Policy)
    {Parameter : Type} (parameter : State L setup.context → Parameter)
    (utility : Parameter × PublicOutcome setup.program → Player → ℝ) {forfeit : ℝ}
    (range : ∀ high low who, utility high who - utility low who ≤ forfeit)
    (focal : Player) (current final : (serviceApplication setup deps duration leaks).Execution)
    (supported : current ∈ ((serviceApplication setup deps duration leaks).roundsFrom
      (serviceInitialDistribution setup deps) scheduler players
        current.environmentRecall.length).support)
    (bounded : current.environmentRecall.length ≤ horizon)
    (defaulted : focal ∈ current.application.config.defaulted)
    (reached : final ∈ ((serviceApplication setup deps duration leaks).runToHorizon scheduler
      players horizon current).support) :
    setup.graphForfeitConfigPayoff deps parameter utility forfeit final.application.config focal ≤
      leastUtility utility focal := by
  obtain ⟨terminal, path, inputs, reachable⟩ := runToHorizon_terminal_path scheduler contract
    players current final supported bounded reached
  have charged := setup.failedReveals_pos_of_graph_defaulted deps reachable terminal
    (Config.Step.path_defaulted_mono path defaulted)
  exact (congrFun (setup.graphForfeitConfigPayoff_terminal deps parameter utility forfeit
    final.application.config terminal) focal).trans_le
      (setup.graphForfeitPayoff_le_leastUtility_of_failed deps parameter utility range
        ⟨final.application.config, terminal⟩ focal charged)

/-- Actual public default bounds every raw native continuation in expectation.
The utility spread derives integrability without a finiteness premise. -/
theorem expect_runToHorizon_forfeit_le_of_defaulted
    {horizon : Nat} (scheduler : (serviceApplication setup deps duration leaks).Scheduler)
    {delay bound : (serviceGraph setup deps).EventId → Nat}
    (contract : AsyncContract (serviceTimeouts setup deps duration) leaks
      (serviceInitialDistribution setup deps) horizon scheduler delay bound)
    (players : Player → (serviceApplication setup deps duration leaks).Policy)
    {Parameter : Type} (parameter : State L setup.context → Parameter)
    (utility : Parameter × PublicOutcome setup.program → Player → ℝ) {forfeit : ℝ}
    (range : ∀ high low who, utility high who - utility low who ≤ forfeit)
    (focal : Player) (current : (serviceApplication setup deps duration leaks).Execution)
    (supported : current ∈ ((serviceApplication setup deps duration leaks).roundsFrom
      (serviceInitialDistribution setup deps) scheduler players
        current.environmentRecall.length).support)
    (bounded : current.environmentRecall.length ≤ horizon)
    (defaulted : focal ∈ current.application.config.defaulted) :
    expect ((serviceApplication setup deps duration leaks).runToHorizon scheduler players horizon
      current) (fun final =>
        setup.graphForfeitConfigPayoff deps parameter utility forfeit final.application.config
          focal) ≤ leastUtility utility focal := by
  let app := serviceApplication setup deps duration leaks
  let law := app.runToHorizon scheduler players horizon current
  let value := fun final : app.Execution => setup.graphForfeitConfigPayoff deps parameter utility
    forfeit final.application.config focal
  obtain ⟨payoffBound, _nonnegative, payoffBounded⟩ :=
    setup.graphForfeitConfigPayoff_abs_bound deps parameter utility range focal
  have integrable : PayoffIntegrable law value :=
    payoffIntegrable_of_bounded law value (fun final => payoffBounded final.application.config)
  have estimate := expect_mono (μ := law) (f := value)
    (g := fun _ => leastUtility utility focal) (by
      intro final reached
      exact runToHorizon_forfeit_floor_of_defaulted scheduler contract players parameter utility
        range focal current final supported bounded defaulted reached) integrable
    (payoffIntegrable_constant law (leastUtility utility focal))
  simpa only [expect_constant] using estimate

/-- Source debt witnessed by matching own binding records bounds every later
raw native continuation, even if foreign private bindings differ or remain pending. -/
theorem SourceResidual.expect_runToHorizon_forfeit_le_of_matching_binding_records
    (serial : (serviceGraph setup deps).ActorSerial)
    {profile : BehavioralProfile setup.program} {rank : Nat}
    {sourceGhost : setup.informationGraph.Config}
    (residual : SourceResidual setup profile rank sourceGhost)
    (initial : State L setup.context) (focal : Player)
    (origin ghost : (serviceGraph setup deps).Config) (start : Nat)
    (originReach : EventGraph.Config.Reachable (graph := serviceGraph setup deps)
      (setup.eventInputs initial) origin)
    (before : origin.cut.IsPrefix start)
    (ghostPath : Relation.ReflTransGen EventGraph.Config.Step origin ghost)
    (ghostKey : runKey ghost = runKey
      ((serviceGraph setup deps).fromSequentialConfig sourceGhost))
    (bindings : ∀ event : (serviceGraph setup deps).EventId,
      start ≤ event.val → event.val < rank →
      ∃ owner payload, (serviceGraph setup deps).outputLayout event = .binding owner payload)
    (owed : ProtocolState.OwesFailure focal setup.program
      (residual.lift (ProtocolState.entry residual.program residual.source)))
    {horizon : Nat} (scheduler : (serviceApplication setup deps duration leaks).Scheduler)
    {delay bound : (serviceGraph setup deps).EventId → Nat}
    (contract : AsyncContract (serviceTimeouts setup deps duration) leaks
      (serviceInitialDistribution setup deps) horizon scheduler delay bound)
    (players : Player → (serviceApplication setup deps duration leaks).Policy)
    {Parameter : Type} (parameter : State L setup.context → Parameter)
    (utility : Parameter × PublicOutcome setup.program → Player → ℝ) {forfeit : ℝ}
    (range : ∀ high low who, utility high who - utility low who ≤ forfeit)
    (current : (serviceApplication setup deps duration leaks).Execution)
    (supported : current ∈ ((serviceApplication setup deps duration leaks).roundsFrom
      (serviceInitialDistribution setup deps) scheduler players
        current.environmentRecall.length).support)
    (bounded : current.environmentRecall.length ≤ horizon)
    (currentPath : Relation.ReflTransGen EventGraph.Config.Step origin current.application.config)
    (records : ∀ event : (serviceGraph setup deps).EventId,
      start ≤ event.val → event.val < rank → (serviceGraph setup deps).actor? event = some focal →
      completionOf ghost event = completionOf current.application.config event) :
    expect ((serviceApplication setup deps duration leaks).runToHorizon scheduler players horizon
      current) (fun final =>
        setup.graphForfeitConfigPayoff deps parameter utility forfeit final.application.config
          focal) ≤ leastUtility utility focal := by
  let app := serviceApplication setup deps duration leaks
  let law := app.runToHorizon scheduler players horizon current
  let value := fun final : app.Execution => setup.graphForfeitConfigPayoff deps parameter utility
    forfeit final.application.config focal
  have ghostOrdered : ghost.cut.IsPrefix rank := by
    refine ⟨residual.checkpoint.ordered.1, ?_⟩
    intro event
    have same := congrArg (fun key => event ∈ key.1.completed) ghostKey
    exact same ▸ residual.checkpoint.ordered.2 event
  have below (final : app.Execution) (reached : final ∈ law.support) :
      value final ≤ leastUtility utility focal := by
    obtain ⟨terminal, path, _inputs, _reachable⟩ := runToHorizon_terminal_path scheduler contract
      players current final supported bounded reached
    have finalRecords : ∀ event : (serviceGraph setup deps).EventId,
        start ≤ event.val → event.val < rank → (serviceGraph setup deps).actor? event = some focal →
        completionOf ghost event = completionOf final.application.config event := by
      intro event lower upper actor
      obtain ⟨completion, found⟩ := Option.isSome_iff_exists.mp
        ((completionOf_isSome_iff ghost event).mpr ((ghostOrdered.2 event).mpr upper))
      rw [found]
      exact (Config.Step.path_completionOf_of_some path event completion
        ((records event lower upper actor).symm.trans found)).symm
    have charged := residual.failedReveals_of_matching_binding_records deps serial initial focal
      origin ghost final.application.config start originReach before ghostPath ghostKey
      (currentPath.trans path) terminal bindings finalRecords owed
    exact (congrFun (setup.graphForfeitConfigPayoff_terminal deps parameter utility forfeit
      final.application.config terminal) focal).trans_le
        (setup.graphForfeitPayoff_le_leastUtility_of_failed deps parameter utility range
          ⟨final.application.config, terminal⟩ focal charged)
  obtain ⟨payoffBound, _nonnegative, payoffBounded⟩ :=
    setup.graphForfeitConfigPayoff_abs_bound deps parameter utility range focal
  have integrable : PayoffIntegrable law value :=
    payoffIntegrable_of_bounded law value (fun final => payoffBounded final.application.config)
  have estimate := expect_mono below integrable
    (payoffIntegrable_constant law (leastUtility utility focal))
  simpa only [expect_constant] using estimate

end Vegas
