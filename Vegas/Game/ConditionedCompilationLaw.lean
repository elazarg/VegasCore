module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Game.ConditionedLedgerClients
public import Vegas.Source.ConditionedInitialPolicy
public import Vegas.Game.IntendedAuthenticOpening
public import Vegas.Game.ClientCompiler

@[expose] public section

/-! # The intended outcome law of component-selected ledger clients -/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory.Protocol Interaction EventGraphRuntime GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
    (setup : Setup (Player := Player) (L := L))
    {Signal : Type*} (signal : State L setup.context → Signal)

/-- Restricting the draw to a supported signal component retains all source formation checks. -/
theorem conditionInitial_wellFormed (value : Signal)
    (supported : value ∈ (setup.initialLaw.map signal).support) (formed : setup.WellFormed) :
    (setup.conditionInitial signal value).WellFormed where
  initialValues draw member := formed.initialValues draw
    (setup.conditionInitial_support_subset signal value supported member)
  guardsSatisfiable draw member := formed.guardsSatisfiable draw
    (setup.conditionInitial_support_subset signal value supported member)

private theorem conditionInitial_openingProfile (value : Signal)
    (policies : ∀ who, setup.intendedModel.BehavioralPolicy who) :
    (setup.conditionInitial signal value).intendedOpeningProfile
        (fun who => setup.conditionInitial_policy signal value who (policies who)) =
      setup.intendedOpeningProfile policies := by
  funext who
  apply congrArg (fun policy : BehavioralPolicy who setup.program =>
    policy.authenticOpening setup.program)
  apply congrArg (BehavioralPolicy.fromProtocol setup.program
    (CommitmentInterface.values setup.program))
  funext view
  change (((setup.conditionInitial_policy signal value who (policies who) (some view)).map
    (((setup.conditionInitial signal value).intendedRestriction
      (CommitmentInterface.values setup.program)).choice who (some view)))) =
    (policies who (some view)).map
      ((setup.intendedRestriction (CommitmentInterface.values setup.program)).choice who
        (some view))
  rw [conditionInitial_policy, PMF.map_comp]
  rfl

/-- Conditioning the initial source law and mixing the resulting intended play reconstructs
the original complete typed terminal state for every behavioral profile. -/
theorem conditionInitial_intendedReadout [Finite Player] (formed : setup.WellFormed)
    (policies : ∀ who, setup.intendedModel.BehavioralPolicy who) :
    (setup.initialLaw.map signal).bind (fun key =>
      (((setup.conditionInitial signal key).intendedModel.runBehavioral
        (fun who => setup.conditionInitial_policy signal key who (policies who))
          (instructionCount setup.program + 1)).map fun final =>
            (setup.conditionInitial signal key).protocolReadout final.state)) =
      (setup.intendedModel.runBehavioral policies (instructionCount setup.program + 1)).map
        (fun final => setup.protocolReadout final.state) := by
  rw [setup.intendedOpeningProfile_run formed policies, ← setup.run_conditionInitial_reconstruct
    signal (setup.intendedOpeningProfile policies), PMF.map_bind]
  apply bind_congr_on_support _
  intro key member
  exact ((setup.conditionInitial signal key).intendedOpeningProfile_run
    (setup.conditionInitial_wellFormed signal key member formed) _).trans
      (congrArg (fun profile => ((setup.conditionInitial signal key).run profile).map some)
        (setup.conditionInitial_openingProfile signal key policies))

/-- The selected component clients recover the global intended outcome law, including the
joint typed configuration and settled payoffs, when audited through the same observation. -/
theorem signalClients_intendedLaw [Finite Player]
    {timeouts : EventTimeouts setup.informationGraph}
    {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket setup.informationGraph)}
    {scheduler : (application setup timeouts leaks).Scheduler} (horizon : Nat)
    (read : Player → (application setup timeouts leaks).PlayerView → Signal)
    (observed : ∀ draw ∈ setup.initialLaw.support,
      ∀ execution : (application setup timeouts leaks).Execution,
      EventGraphRuntime.State.Invariant (graph := setup.informationGraph) (setup.eventInputs draw)
        execution.application → ∀ who, read who (execution.observe _ who) = signal draw)
    (clients : Signal → Player → (application setup timeouts leaks).Policy)
    (formed : setup.WellFormed) (policies : ∀ who, setup.intendedModel.BehavioralPolicy who)
    {Parameter : Type} (parameter : State L setup.context → Parameter)
    (utility : Parameter × PublicOutcome setup.program → Player → ℝ) (exit : Player → ℝ)
    (observation : (application setup timeouts leaks).ProtocolState →
      PMF (Option (Config Player L setup.program.terminalCtx) × (Player → ℝ)))
    (law : ∀ key ∈ (setup.initialLaw.map signal).support,
      ((application setup timeouts leaks).finish (Vegas.initialLaw (setup.conditionInitial signal
        key)) horizon scheduler (clients key) none).bind observation =
      ((setup.conditionInitial signal key).intendedModel.runBehavioral
        (fun who => setup.conditionInitial_policy signal key who (policies who))
        (instructionCount setup.program + 1)).map
        (intendedReadoutExclusion (setup.conditionInitial signal key) parameter utility exit)) :
    ((application setup timeouts leaks).finish (Vegas.initialLaw setup) horizon scheduler
      (signalClients read clients) none).bind observation =
      (setup.intendedModel.runBehavioral policies (instructionCount setup.program + 1)).map
        (intendedReadoutExclusion setup parameter utility exit) := by
  let app := application setup timeouts leaks
  have finish (initial : PMF app.State) (profile : Player → app.Policy) :
      app.finish initial horizon scheduler profile none =
        (app.roundsFrom initial scheduler profile horizon).map app.finished := by
    simp only [ReactiveApplication.finish, ReactiveApplication.roundsFrom, PMF.map_bind]
  have mixture := roundsFrom_signalClients (scheduler := scheduler) read observed clients horizon
  let outcome := fun config : Option (Config Player L setup.program.terminalCtx) =>
    (config, exclusionReadoutUtility setup parameter utility exit config)
  have source := congrArg (PMF.map outcome)
    (setup.conditionInitial_intendedReadout signal formed policies)
  rw [PMF.map_bind] at source
  simp only [PMF.map_comp] at source
  refine Eq.trans ?_ source
  rw [finish, mixture, PMF.map_bind, PMF.bind_bind]
  apply bind_congr_on_support _
  intro key supported
  exact (congrArg (fun distribution => distribution.bind observation)
    (finish _ (clients key)).symm).trans (law key supported)

end Vegas.SourceProgram.Setup
