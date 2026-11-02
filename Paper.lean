/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Source.Safety
import Vegas.Compile.EventGraphScheduling
import Vegas.Compile.EventGraphDeviation
import Vegas.Game.EventCompilation
import Vegas.Game.CompilerCorrectness
import Vegas.Pending.GraphRefinement
import Vegas.Game.IntendedPreservation
import Vegas.Game.IntendedNash
import Vegas.Game.AsyncServiceRawNash
import Vegas.Game.AsyncClientObservables
import Vegas.Game.ProgramPaymentAsyncNash
import Vegas.Game.OnePacketExtension
import Vegas.Game.SequentialCompilation
import Vegas.Game.ClientObservables
import Vegas.Game.PaymentPreservation
import Vegas.Game.ServiceRosterAsync
import Vegas.Examples.LateLeak
import Vegas.Examples.CommitRevealAuction
import Vegas.Examples.BoundedPaymentAuction
import Vegas.Examples.OddsEvensRawEquilibrium
import Vegas.Examples.OddsEvensFullSource

/-! # Mathematical statements of the maintained paper

Every result is stated here in full. Only its proof delegates to the owning
library theorem. Model definitions and the common compiler specification live
in their owning modules; every local result has an adjacent exact axiom pin.
-/

noncomputable section

universe u_1

/-- The paper statement has its proof in
`Vegas.SourceProgram.Setup.protocol_bounded`. -/
theorem Vegas.Paper.protocol_bounded
    {Player : Type}
    [inst : DecidableEq Player]
    {L : Vegas.IExpr}
    [inst_1 : L.ResultTypes]
    (setup : Vegas.SourceProgram.Setup (Player := Player) (L := L))
    (admission : setup.program.CommitmentInterface) :
    (setup.executionProtocol admission).BoundedHorizon (setup.program.instructionCount + 1) := by
  exact @Vegas.SourceProgram.Setup.protocol_bounded
    Player inst L inst_1 setup admission

/-- info: 'Vegas.Paper.protocol_bounded' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.protocol_bounded

/-- The paper statement has its proof in
`Vegas.SourceProgram.Setup.intended_forfeit_isεNash_preserved`. -/
theorem Vegas.Paper.intended_forfeit_isεNash_preserved
    {Player : Type}
    [inst : DecidableEq Player]
    {L : Vegas.IExpr}
    [inst_1 : L.ResultTypes]
    (setup : Vegas.SourceProgram.Setup (Player := Player) (L := L))
    [inst_2 : Fintype Player]
    (finite : setup.program.FiniteBindingTypes)
    [_instance7 : setup.FiniteInitialLaw]
    (wellFormed : setup.WellFormed)
    {Parameter : Type}
    (parameter : Vegas.State L setup.context → Parameter)
    (utility : Parameter × setup.program.PublicOutcome → Player → ℝ)
    (forfeit : ℝ)
    (range :
        setup.TerminalPayoffSpread (Vegas.SourceProgram.CommitmentInterface.values
          setup.program) parameter utility forfeit)
    (intended : GameTheory.Profile setup.intendedModel.behavioralSignature)
    (target :
        GameTheory.Profile
          (setup.informationModel (Vegas.SourceProgram.CommitmentInterface.values
            setup.program)).behavioralSignature)
    (agrees :
        (setup.intendedRestriction (Vegas.SourceProgram.CommitmentInterface.values
          setup.program)).ExtendsProfile intended
          target)
    (ε : ℝ)
    (_equilibrium :
        GameTheory.IsεNash (setup.intendedModel.toBehavioralGameForm
          (setup.program.instructionCount + 1))
          (fun (final : (setup.intendedModel.toBehavioralGameForm
            (setup.program.instructionCount + 1)).sig.Outcome)
              (who : Player) =>
            (setup.protocolReadout final.state).elim 0
              fun (state : Vegas.SourceProgram.Config Player L setup.program.terminalCtx) =>
              utility (setup.parameterOutcome parameter state) who)
          ε intended) :
    GameTheory.IsεNash
          ((setup.informationModel (Vegas.SourceProgram.CommitmentInterface.values
            setup.program)).toBehavioralGameForm
            (setup.program.instructionCount + 1))
          (fun
              (final :
                ((setup.informationModel
                          (Vegas.SourceProgram.CommitmentInterface.values
                            setup.program)).toBehavioralGameForm
                      (setup.program.instructionCount + 1)).sig.Outcome)
              (who : Player) =>
            (setup.protocolReadout final.state).elim 0
              fun (state : Vegas.SourceProgram.Config Player L setup.program.terminalCtx) =>
              setup.program.forfeitUtility forfeit utility (setup.parameterOutcome parameter
                state) who)
          ε target ∧
        (∀
            final ∈
              ((setup.informationModel (Vegas.SourceProgram.CommitmentInterface.values
                setup.program)).runBehavioral target
                  (setup.program.instructionCount + 1)).support,
            ∀ (terminal : Vegas.SourceProgram.Config Player L setup.program.terminalCtx),
              setup.protocolReadout final.state = some terminal →
                ∀ (who : Player), setup.program.failedReveals who (setup.program.publicOutcome
                  terminal) = 0) ∧
          PMF.map
              (fun
                  (final :
                    (setup.executionProtocol (Vegas.SourceProgram.CommitmentInterface.values
                      setup.program)).History) =>
                (setup.protocolReadout final.state, fun (who : Player) =>
                  (setup.protocolReadout final.state).elim 0
                    fun (state : Vegas.SourceProgram.Config Player L setup.program.terminalCtx) =>
                    setup.program.forfeitUtility forfeit utility (setup.parameterOutcome
                      parameter state) who))
              ((setup.informationModel (Vegas.SourceProgram.CommitmentInterface.values
                setup.program)).runBehavioral target
                (setup.program.instructionCount + 1)) =
            PMF.map
              (fun (final : setup.intendedProtocol.History) =>
                (setup.protocolReadout final.state, fun (who : Player) =>
                  (setup.protocolReadout final.state).elim 0
                    fun (state : Vegas.SourceProgram.Config Player L setup.program.terminalCtx) =>
                    utility (setup.parameterOutcome parameter state) who))
              (setup.intendedModel.runBehavioral intended (setup.program.instructionCount + 1))
                := by
  exact @Vegas.SourceProgram.Setup.intended_forfeit_isεNash_preserved
    Player inst L inst_1 setup inst_2 finite _instance7 wellFormed Parameter parameter utility
      forfeit range intended target agrees ε _equilibrium

/-- info: 'Vegas.Paper.intended_forfeit_isεNash_preserved' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.intended_forfeit_isεNash_preserved

/-- The paper statement has its proof in
`Vegas.SourceProgram.Setup.intended_forfeit_sequentialEquilibrium_preserved`. -/
theorem Vegas.Paper.intended_forfeit_sequentialEquilibrium_preserved
    {Player : Type}
    [inst : DecidableEq Player]
    {L : Vegas.IExpr}
    [inst_1 : L.ResultTypes]
    (setup : Vegas.SourceProgram.Setup (Player := Player) (L := L))
    [inst_2 : Fintype Player]
    (admission : setup.program.CommitmentInterface)
    (finite : setup.program.FiniteBindingTypes)
    [_instance8 : setup.FiniteInitialLaw]
    (wellFormed : setup.WellFormed)
    {Parameter : Type}
    (parameter : Vegas.State L setup.context → Parameter)
    (utility : Parameter × setup.program.PublicOutcome → Player → ℝ)
    (forfeit : ℝ)
    (range : setup.TerminalPayoffSpread admission parameter utility forfeit)
    (intendedTerminates : setup.intendedProtocol.WellFoundedHistories)
    (sourceTerminates : (setup.executionProtocol admission).WellFoundedHistories)
    (intended : setup.intendedModel.BehavioralAssessment)
    (_equilibrium :
        intended.IsSequentialEquilibrium (Vegas.SourceProgram.Setup.intended_decision_antichain
          setup) intendedTerminates
          fun (who : Player) (final : setup.intendedProtocol.History) =>
          (setup.protocolReadout final.state).elim 0
            fun (state : Vegas.SourceProgram.Config Player L setup.program.terminalCtx) =>
            utility (setup.parameterOutcome parameter state) who) :
    ∃ (target : (setup.informationModel admission).BehavioralAssessment),
        (target.IsSequentialEquilibrium (Vegas.SourceProgram.Setup.decision_antichain setup
          admission) sourceTerminates
            fun (who : Player) (final : (setup.executionProtocol admission).History) =>
            (setup.protocolReadout final.state).elim 0
              fun (state : Vegas.SourceProgram.Config Player L setup.program.terminalCtx) =>
              setup.program.forfeitUtility forfeit utility (setup.parameterOutcome parameter
                state) who) ∧
          (∀
              final ∈
                ((setup.informationModel admission).runBehavioralTerminalFrom sourceTerminates
                  target.strategy
                    (setup.executionProtocol admission).initHistory).support,
              ∀ (terminal : Vegas.SourceProgram.Config Player L setup.program.terminalCtx),
                setup.protocolReadout final.state = some terminal →
                  ∀ (who : Player), setup.program.failedReveals who
                    (setup.program.publicOutcome terminal) = 0) ∧
            PMF.map
                (fun (final : (setup.executionProtocol admission).History) =>
                  (setup.protocolReadout final.state, fun (who : Player) =>
                    (setup.protocolReadout final.state).elim 0
                      fun (state : Vegas.SourceProgram.Config Player L setup.program.terminalCtx) =>
                      setup.program.forfeitUtility forfeit utility (setup.parameterOutcome
                        parameter state) who))
                ((setup.informationModel admission).runBehavioralTerminalFrom sourceTerminates
                  target.strategy
                  (setup.executionProtocol admission).initHistory) =
              PMF.map
                (fun (final : setup.intendedProtocol.History) =>
                  (setup.protocolReadout final.state, fun (who : Player) =>
                    (setup.protocolReadout final.state).elim 0
                      fun (state : Vegas.SourceProgram.Config Player L setup.program.terminalCtx) =>
                      utility (setup.parameterOutcome parameter state) who))
                (setup.intendedModel.runBehavioralTerminalFrom intendedTerminates intended.strategy
                  setup.intendedProtocol.initHistory) := by
  exact @Vegas.SourceProgram.Setup.intended_forfeit_sequentialEquilibrium_preserved
    Player inst L inst_1 setup inst_2 admission finite _instance8 wellFormed Parameter
      parameter utility forfeit range intendedTerminates sourceTerminates intended _equilibrium

/-- info: 'Vegas.Paper.intended_forfeit_sequentialEquilibrium_preserved' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.intended_forfeit_sequentialEquilibrium_preserved

/-- The paper statement has its proof in
`Vegas.SourceProgram.Setup.intendedState_trace`. -/
theorem Vegas.Paper.intendedState_trace
    {Player : Type}
    [inst : DecidableEq Player]
    {L : Vegas.IExpr}
    [inst_1 : L.ResultTypes]
    (setup : Vegas.SourceProgram.Setup (Player := Player) (L := L))
    (wellFormed : setup.WellFormed)
    {state : setup.intendedProtocol.State}
    (_x : setup.intendedProtocol.Trace state) :
    setup.IntendedState state := by
  exact @Vegas.SourceProgram.Setup.intendedState_trace
    Player inst L inst_1 setup wellFormed state _x

/-- info: 'Vegas.Paper.intendedState_trace' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.intendedState_trace

/-- The paper statement has its proof in
`Vegas.SourceProgram.Setup.failedReveals_eq_zero_of_intendedState`. -/
theorem Vegas.Paper.failedReveals_eq_zero_of_intendedState
    {Player : Type}
    [inst : DecidableEq Player]
    {L : Vegas.IExpr}
    [inst_1 : L.ResultTypes]
    (setup : Vegas.SourceProgram.Setup (Player := Player) (L := L))
    {state : setup.ProtocolState}
    (intended : setup.IntendedState state)
    (who : Player)
    {terminal : Vegas.SourceProgram.Config Player L setup.program.terminalCtx}
    (read : setup.protocolReadout state = some terminal) :
    setup.program.failedReveals who (setup.program.publicOutcome terminal) = 0 := by
  exact @Vegas.SourceProgram.Setup.failedReveals_eq_zero_of_intendedState
    Player inst L inst_1 setup state intended who terminal read

/-- info: 'Vegas.Paper.failedReveals_eq_zero_of_intendedState' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.failedReveals_eq_zero_of_intendedState

/-- The paper statement has its proof in
`Vegas.SourceProgram.Setup.revealed`. -/
theorem Vegas.Paper.revealed
    {Player : Type}
    [inst : DecidableEq Player]
    {L : Vegas.IExpr}
    [inst_1 : L.ResultTypes]
    (setup : Vegas.SourceProgram.Setup (Player := Player) (L := L))
    {_owner : Player}
    {_payload : L.Ty}
    {_name : Vegas.VarId}
    (h : Vegas.HasVar setup.program.terminalCtx _name (Vegas.CellTy.commitment _owner _payload)) :
    (setup.program.finalRevelations
            (fun {_owner : Player} {_payload : L.Ty} {_name : Vegas.VarId} =>
              Vegas.Revelations.initial setup.context)
            h).isRevealed =
        true := by
  exact @Vegas.SourceProgram.Setup.revealed
    Player inst L inst_1 setup _owner _payload _name h

/-- info: 'Vegas.Paper.revealed' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.revealed

/-- The paper statement has its proof in
`Vegas.SourceProgram.Setup.terminal_guards_hold`. -/
theorem Vegas.Paper.terminal_guards_hold
    {Player : Type}
    [inst : DecidableEq Player]
    {L : Vegas.IExpr}
    [inst_1 : L.ResultTypes]
    (setup : Vegas.SourceProgram.Setup (Player := Player) (L := L))
    (profile : setup.program.BehavioralProfile)
    (outcome : Vegas.SourceProgram.Config Player L setup.program.terminalCtx)
    (supported : outcome ∈ (setup.run profile).support)
    (obligation : Vegas.SourceProgram.Obligation setup.program.terminalCtx)
    (_member : obligation ∈ setup.program.finalRegistry []) :
    (Vegas.Revelation.result outcome.state
              (setup.program.finalRevelations
                (fun {_owner : Player} {_payload : L.Ty} {_name : Vegas.VarId} =>
                  Vegas.Revelations.initial setup.context)
                obligation.source) =
            Vegas.PublicationResult.failure ∨
          ∃ (_x : Vegas.VarId) (τ : L.Ty) (h : Vegas.HasVar obligation.guard.schema _x τ),
            _x ∈ L.exprDeps obligation.guard.code ∧
              Vegas.SourceGuardRead.result
                  (fun {_owner : Player} {_payload : L.Ty} {_name : Vegas.VarId} =>
                    setup.program.finalRevelations fun {_owner : Player} {_payload : L.Ty}
                      {_name : Vegas.VarId} =>
                      Vegas.Revelations.initial setup.context)
                  outcome.state (obligation.guard.reads h) =
                Vegas.PublicationResult.failure) ∨
        ∃ (subjectValue : L.Val obligation.payload) (get :
          (_x : Vegas.VarId) →
            (σ : L.Ty) →
              Vegas.HasVar ((obligation.subject, obligation.payload) ::
                obligation.guard.schema) _x σ →
                _x ∈ L.exprDeps obligation.guard.code → L.Val σ),
          Vegas.Revelation.result outcome.state
                (setup.program.finalRevelations
                  (fun {_owner : Player} {_payload : L.Ty} {_name : Vegas.VarId} =>
                    Vegas.Revelations.initial setup.context)
                  obligation.source) =
              Vegas.PublicationResult.success subjectValue ∧
            (∀ (hx : obligation.subject ∈ L.exprDeps obligation.guard.code),
                get obligation.subject obligation.payload Vegas.HasVar.here hx = subjectValue) ∧
              (∀ {_x : Vegas.VarId} {τ : L.Ty} (h : Vegas.HasVar obligation.guard.schema _x τ)
                  (hx : _x ∈ L.exprDeps obligation.guard.code),
                  Vegas.SourceGuardRead.result
                      (fun {_owner : Player} {_payload : L.Ty} {_name : Vegas.VarId} =>
                        setup.program.finalRevelations fun {_owner : Player} {_payload : L.Ty}
                          {_name : Vegas.VarId} =>
                          Vegas.Revelations.initial setup.context)
                      outcome.state (obligation.guard.reads h) =
                    Vegas.PublicationResult.success (get _x τ h.there hx)) ∧
                L.toBool (L.evalDeps obligation.guard.code get) = true := by
  exact @Vegas.SourceProgram.Setup.terminal_guards_hold
    Player inst L inst_1 setup profile outcome supported obligation _member

/-- info: 'Vegas.Paper.terminal_guards_hold' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.terminal_guards_hold

/-- The paper statement has its proof in
`Vegas.sourceObserve_privateInput`. -/
theorem Vegas.Paper.sourceObserve_privateInput
    {Player : Type}
    [inst : DecidableEq Player]
    {L : Vegas.IExpr}
    {Γ : Vegas.SourceCtx Player L}
    (who : Player)
    (state : Vegas.State L Γ)
    {_x : Vegas.VarId}
    {_owner : Player}
    {τ : L.Ty}
    (h : Vegas.HasVar Γ _x (Vegas.CellTy.privateInput _owner τ)) :
    (Vegas.sourceObserve who state).cells _x (Vegas.CellTy.privateInput _owner τ) h =
        if _owner = who then some (Vegas.Env.get state h) else none := by
  exact @Vegas.sourceObserve_privateInput
    Player inst L Γ who state _x _owner τ h

/-- info: 'Vegas.Paper.sourceObserve_privateInput' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.sourceObserve_privateInput

/-- The paper statement has its proof in
`Vegas.scheduled_terminalConfig_law`. -/
theorem Vegas.Paper.scheduled_terminalConfig_law
    {Player : Type}
    [inst : DecidableEq Player]
    {L : Vegas.IExpr}
    [inst_1 : L.ResultTypes]
    {Γ : Vegas.SourceCtx Player L}
    {openNames : Finset Vegas.VarId}
    (program : Vegas.SourceProgram Player L Γ openNames)
    (scheduler : (Vegas.toEventGraph program).PublicScheduler)
    (profile : program.BehavioralProfile)
    (state : Vegas.State L Γ) :
    PMF.map (Vegas.terminalConfig program)
          ((Vegas.toEventGraph program).terminalOutcomes scheduler (Vegas.compileEventProfile
            program profile)
            (Vegas.encodeInputs state)) =
        program.run profile state := by
  exact @Vegas.scheduled_terminalConfig_law
    Player inst L inst_1 Γ openNames program scheduler profile state

/-- info: 'Vegas.Paper.scheduled_terminalConfig_law' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.scheduled_terminalConfig_law

/-- The paper statement has its proof in
`Vegas.scheduled_setup_deviation_law`. -/
theorem Vegas.Paper.scheduled_setup_deviation_law
    {Player : Type}
    [inst : DecidableEq Player]
    {L : Vegas.IExpr}
    [inst_1 : L.ResultTypes]
    (setup : Vegas.SourceProgram.Setup (Player := Player) (L := L))
    (scheduler : setup.eventGraph.PublicScheduler)
    (profile : setup.program.BehavioralProfile)
    (who : Player)
    (replacement : setup.eventGraph.BehavioralPolicy who) :
    (setup.initialLaw.bind fun (initial : Vegas.State L setup.context) =>
          PMF.map (Vegas.terminalConfig setup.program)
            (setup.eventGraph.terminalOutcomes scheduler
              (GameTheory.Profile.update (sig := setup.eventGraph.gameSignature)
                (Vegas.compileEventProfile setup.program profile) who replacement)
              (setup.eventInputs initial))) =
        setup.run (GameTheory.Profile.update (sig := Vegas.SourceProgram.gameSignature
          setup.program) profile who (Vegas.backtranslateEventPolicy setup.program who
            replacement)) := by
  exact @Vegas.scheduled_setup_deviation_law
    Player inst L inst_1 setup scheduler profile who replacement

/-- info: 'Vegas.Paper.scheduled_setup_deviation_law' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.scheduled_setup_deviation_law

/-- The paper statement has its proof in
`Vegas.SourceProgram.Setup.eventGame_approximate_nash_iff`. -/
theorem Vegas.Paper.eventGame_approximate_nash_iff
    {Player : Type}
    [inst : DecidableEq Player]
    {L : Vegas.IExpr}
    [R : L.ResultTypes]
    (setup : Vegas.SourceProgram.Setup (Player := Player) (L := L))
    (finite : setup.program.FiniteBindingTypes)
    [_instance6 : setup.FiniteInitialLaw]
    (scheduler : setup.eventGraph.PublicScheduler)
    (utility : setup.program.PublicOutcome → Player → ℝ)
    (ε : ℝ)
    (profile : setup.program.BehavioralProfile) :
    GameTheory.IsεNash (setup.eventGame scheduler)
          (fun (outcome : (setup.eventGame scheduler).sig.Outcome) (who : Player) =>
            utility (setup.eventPublicOutcome outcome) who)
          ε (Vegas.compileEventProfile setup.program profile) ↔
        GameTheory.IsεNash setup.gameForm utility ε profile := by
  exact @Vegas.SourceProgram.Setup.eventGame_approximate_nash_iff
    Player inst L R setup finite _instance6 scheduler utility ε profile

/-- info: 'Vegas.Paper.eventGame_approximate_nash_iff' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.eventGame_approximate_nash_iff

/-- The paper statement has its proof in
`Vegas.EventGraphRuntime.reactive_protocol_graph_refinement`. -/
theorem Vegas.Paper.reactive_protocol_graph_refinement
    {Player : Type}
    [inst : DecidableEq Player]
    {L : Vegas.IExpr}
    [inst_1 : L.ResultTypes]
    {graph : Vegas.EventGraph Player L}
    (runtime : Vegas.EventGraphRuntime graph)
    (leaks : Interaction.MessageNetwork.ObservationRule Player
      (Vegas.EventGraphRuntime.WitnessedPacket graph))
    (inputs : PMF graph.Inputs)
    (horizon : ℕ)
    (scheduler : (runtime.reactiveApplication leaks).Scheduler) :
    (∀ (before after : (runtime.reactiveApplication leaks).Control)
          (joint : Player → Option (runtime.reactiveApplication leaks).Action),
          some after ∈
              ((runtime.reactiveApplication leaks).transition (PMF.map
                Vegas.EventGraphRuntime.State.initial inputs) horizon
                  scheduler (some before) joint).support →
            Relation.ReflTransGen Vegas.EventGraph.Config.Step before.execution.application.config
              after.execution.application.config) ∧
        ∀ (control : (runtime.reactiveApplication leaks).Control)
          (_trace :
            ((runtime.reactiveApplication leaks).protocol (PMF.map
              Vegas.EventGraphRuntime.State.initial inputs) horizon
                  scheduler).Trace
              (some control)),
          (∃ initial ∈ inputs.support, Vegas.EventGraph.Config.Reachable initial
            control.execution.application.config) ∧
            (runtime.CompletesPlay leaks (PMF.map Vegas.EventGraphRuntime.State.initial inputs)
              horizon scheduler →
              ((runtime.reactiveApplication leaks).protocol (PMF.map
                Vegas.EventGraphRuntime.State.initial inputs) horizon
                      scheduler).terminal
                  (some control) →
                control.execution.application.config.cut.Terminal ∧
                  ∀ (field : graph.Field), (control.execution.application.config.store
                    field).isSome = true) := by
  exact @Vegas.EventGraphRuntime.reactive_protocol_graph_refinement
    Player inst L inst_1 graph runtime leaks inputs horizon scheduler

/-- info: 'Vegas.Paper.reactive_protocol_graph_refinement' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.reactive_protocol_graph_refinement

/-- The paper statement has its proof in
`Vegas.sourceServiceClientPolicy_outcome_law`. -/
theorem Vegas.Paper.sourceServiceClientPolicy_outcome_law
    {Player : Type}
    [inst : DecidableEq Player]
    {L : Vegas.IExpr}
    [inst_1 : L.ResultTypes]
    {setup : Vegas.SourceProgram.Setup (Player := Player) (L := L)}
    [_instance5 : Finite Player]
    (runtime : Vegas.EventGraphRuntime (Vegas.graph setup))
    (leaks :
        Interaction.MessageNetwork.ObservationRule Player
          (Vegas.EventGraphRuntime.WitnessedPacket (Vegas.graph setup)))
    {horizon turns : ℕ}
    (scheduler : (Vegas.application setup runtime leaks).Scheduler)
    (delay bound : (Vegas.graph setup).EventId → ℕ)
    (original : setup.program.BehavioralProfile)
    (contract : runtime.AsyncContract leaks (Vegas.initialLaw setup) horizon scheduler delay bound)
    (timely : runtime.AsyncTimely delay bound)
    {Outcome : Type u_1}
    (read : Vegas.State L setup.program.terminalCtx × Vegas.DefaultHistory Player → Outcome) :
    PMF.map
          (fun (execution : (Vegas.application setup runtime leaks).Execution) =>
            Option.map
              (fun (final : Vegas.SourceProgram.Config Player L setup.program.terminalCtx) =>
                read (final.state, final.defaults))
              (Vegas.sourceReadout setup runtime leaks ((Vegas.application setup runtime
                leaks).finished execution)))
          ((Vegas.application setup runtime leaks).roundsFrom (Vegas.initialLaw setup) scheduler
            (Vegas.serviceClientPolicy setup Vegas.EventGraph.ExecutionMode.sequential
              runtime.deadline leaks bound turns
              (Vegas.firstTurnTiming setup turns) (setup.program.normalizeDisclosureProfile
                original))
            horizon) =
        PMF.map
          (fun (final : Vegas.SourceProgram.Config Player L setup.program.terminalCtx) =>
            some (read (final.state, final.defaults)))
          (setup.run original) := by
  exact @Vegas.sourceServiceClientPolicy_outcome_law
    Player inst L inst_1 setup _instance5 runtime leaks horizon turns scheduler delay bound
      original contract timely Outcome read

/-- info: 'Vegas.Paper.sourceServiceClientPolicy_outcome_law' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.sourceServiceClientPolicy_outcome_law

/-- The paper statement has its proof in
`Vegas.sourceServiceClientPolicy_graph_law`. -/
theorem Vegas.Paper.sourceServiceClientPolicy_graph_law
    {Player : Type}
    [inst : DecidableEq Player]
    {L : Vegas.IExpr}
    [inst_1 : L.ResultTypes]
    {setup : Vegas.SourceProgram.Setup (Player := Player) (L := L)}
    [_instance5 : Finite Player]
    (runtime : Vegas.EventGraphRuntime (Vegas.graph setup))
    (leaks :
        Interaction.MessageNetwork.ObservationRule Player
          (Vegas.EventGraphRuntime.WitnessedPacket (Vegas.graph setup)))
    {horizon turns : ℕ}
    (scheduler : (Vegas.application setup runtime leaks).Scheduler)
    (delay bound : (Vegas.graph setup).EventId → ℕ)
    (original : setup.program.BehavioralProfile)
    (contract : runtime.AsyncContract leaks (Vegas.initialLaw setup) horizon scheduler delay bound)
    (timely : runtime.AsyncTimely delay bound)
    {Outcome : Type u_1}
    (read : Vegas.State L setup.program.terminalCtx × Vegas.DefaultHistory Player → Outcome) :
    PMF.map
          (fun (execution : (Vegas.application setup runtime leaks).Execution) =>
            Option.map
              (fun (final : Vegas.SourceProgram.Config Player L setup.program.terminalCtx) =>
                read (final.state, final.defaults))
              (Vegas.sourceReadout setup runtime leaks ((Vegas.application setup runtime
                leaks).finished execution)))
          ((Vegas.application setup runtime leaks).roundsFrom (Vegas.initialLaw setup) scheduler
            (Vegas.serviceClientPolicy setup Vegas.EventGraph.ExecutionMode.sequential
              runtime.deadline leaks bound turns
              (Vegas.firstTurnTiming setup turns) (setup.program.normalizeDisclosureProfile
                original))
            horizon) =
        PMF.map
          (fun (terminal : { config : (Vegas.toEventGraph setup.program).Config //
            config.cut.Terminal }) =>
            have final := Vegas.terminalConfig setup.program terminal;
            some (read (final.state, final.defaults)))
          ((setup.eventGraph.canonicalGame (PMF.map setup.eventInputs setup.initialLaw)).play
            (Vegas.compileEventProfile setup.program original)) := by
  exact @Vegas.sourceServiceClientPolicy_graph_law
    Player inst L inst_1 setup _instance5 runtime leaks horizon turns scheduler delay bound
      original contract timely Outcome read

/-- info: 'Vegas.Paper.sourceServiceClientPolicy_graph_law' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.sourceServiceClientPolicy_graph_law

/-- The paper statement has its proof in
`Vegas.AsyncServiceSpec.isεNash_rawClientProfile_approximate`. -/
theorem Vegas.Paper.isεNash_rawClientProfile_approximate
    {Player : Type}
    [inst : DecidableEq Player]
    [inst_1 : Fintype Player]
    {L : Vegas.IExpr}
    [inst_2 : L.ResultTypes]
    (service : Vegas.AsyncServiceSpec Player L)
    (admission : service.setup.program.CommitmentInterface)
    {Parameter : Type}
    (ordered : (Vegas.serviceGraph service.setup service.mode).BarrierOrdered)
    (parameter : Vegas.State L service.setup.context → Parameter)
    (utility : Parameter × service.setup.program.PublicOutcome → Player → ℝ)
    (sample :
        List (Vegas.SettledEvidence service.setup service.mode) →
          PMF (List (Vegas.SettledEvidence service.setup service.mode)))
    (authentic :
        ∀ (actual observed : List (Vegas.SettledEvidence service.setup service.mode)),
          observed ∈ (sample actual).support → observed ⊆ actual)
    (deposit : Player → ℝ)
    (nonnegative : ∀ (who : Player), 0 ≤ deposit who)
    {turns : ℕ}
    (timing : Vegas.TurnTiming service.setup turns service.mode)
    (low : Player → ℝ)
    (range : ℝ)
    (within : service.SettlementRange parameter utility sample deposit low fun (_x : Player) =>
      range)
    (ε : ℝ)
    (source : GameTheory.Profile (service.sourceModel admission).behavioralSignature) :
    have base :=
        Vegas.serviceBaseUtility service.setup service.mode service.deadline service.leaks
          fun (state : Vegas.SourceProgram.Config Player L service.setup.program.terminalCtx) =>
          utility (service.setup.parameterOutcome parameter state);
      have payoff :=
        GameTheory.Enforcement.TerminalAudit.utility base
          ((Vegas.serviceRuntime service.setup service.mode
            service.deadline).serviceAuditObservation service.leaks)
          (Vegas.serviceSourceAudit service.setup service.mode service.deadline service.leaks
            sample) deposit;
      (GameTheory.IsεNash
            ((service.sourceModel admission).toBehavioralGameForm
              (service.setup.program.instructionCount + 1))
            (fun
                (final :
                  ((service.sourceModel admission).toBehavioralGameForm
                        (service.setup.program.instructionCount + 1)).sig.Outcome)
                (who : Player) =>
              (service.setup.protocolReadout final.state).elim 0
                fun (state : Vegas.SourceProgram.Config Player L
                  service.setup.program.terminalCtx) =>
                utility (service.setup.parameterOutcome parameter state) who)
            ε source →
          GameTheory.IsεNash
            ((service.rawMenu.information (Vegas.serviceInitialLaw service.setup service.mode)
              service.horizon
                  service.scheduler).toBehavioralGameForm
              (2 * service.horizon + 1))
            (fun
                (history :
                  ((service.rawMenu.information (Vegas.serviceInitialLaw service.setup
                    service.mode) service.horizon
                            service.scheduler).toBehavioralGameForm
                        (2 * service.horizon + 1)).sig.Outcome)
                (who : Player) =>
              payoff history.state who)
            (ε + 2 * timing.deferralError * range) (service.clientProfile admission
              service.rawMenu timing source)) ∧
        (GameTheory.IsεNash
            ((service.rawMenu.information (Vegas.serviceInitialLaw service.setup service.mode)
              service.horizon
                  service.scheduler).toBehavioralGameForm
              (2 * service.horizon + 1))
            (fun
                (history :
                  ((service.rawMenu.information (Vegas.serviceInitialLaw service.setup
                    service.mode) service.horizon
                            service.scheduler).toBehavioralGameForm
                        (2 * service.horizon + 1)).sig.Outcome)
                (who : Player) =>
              payoff history.state who)
            ε (service.clientProfile admission service.rawMenu timing source) →
          GameTheory.IsεNash
            ((service.sourceModel admission).toBehavioralGameForm
              (service.setup.program.instructionCount + 1))
            (fun
                (final :
                  ((service.sourceModel admission).toBehavioralGameForm
                        (service.setup.program.instructionCount + 1)).sig.Outcome)
                (who : Player) =>
              (service.setup.protocolReadout final.state).elim 0
                fun (state : Vegas.SourceProgram.Config Player L
                  service.setup.program.terminalCtx) =>
                utility (service.setup.parameterOutcome parameter state) who)
            (ε + 2 * timing.deferralError * range) source) := by
  exact @Vegas.AsyncServiceSpec.isεNash_rawClientProfile_approximate
    Player inst inst_1 L inst_2 service admission Parameter ordered parameter utility sample
      authentic deposit nonnegative turns timing low range within ε source

/-- info: 'Vegas.Paper.isεNash_rawClientProfile_approximate' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.isεNash_rawClientProfile_approximate

/-- The paper statement has its proof in
`Vegas.AsyncServiceSpec.intended_rawClientProfile_isεNash`. -/
theorem Vegas.Paper.intended_rawClientProfile_isεNash
    {Player : Type}
    [inst : DecidableEq Player]
    [inst_1 : Fintype Player]
    {L : Vegas.IExpr}
    [inst_2 : L.ResultTypes]
    (service : Vegas.AsyncServiceSpec Player L)
    {Parameter : Type}
    (ordered : (Vegas.serviceGraph service.setup service.mode).BarrierOrdered)
    (wellFormed : service.setup.WellFormed)
    (parameter : Vegas.State L service.setup.context → Parameter)
    (utility : Parameter × service.setup.program.PublicOutcome → Player → ℝ)
    (forfeit : ℝ)
    (range :
        service.setup.TerminalPayoffSpread (Vegas.SourceProgram.CommitmentInterface.values
          service.setup.program) parameter
          utility forfeit)
    (sample :
        List (Vegas.SettledEvidence service.setup service.mode) →
          PMF (List (Vegas.SettledEvidence service.setup service.mode)))
    (authentic :
        ∀ (actual observed : List (Vegas.SettledEvidence service.setup service.mode)),
          observed ∈ (sample actual).support → observed ⊆ actual)
    (deposit : Player → ℝ)
    (nonnegative : ∀ (who : Player), 0 ≤ deposit who)
    {turns : ℕ}
    (timing : Vegas.TurnTiming service.setup turns service.mode)
    (low : Player → ℝ)
    (spread : ℝ)
    (within :
        service.SettlementRange parameter (service.setup.program.forfeitUtility forfeit
          utility) sample deposit low
          fun (_x : Player) => spread)
    (intended : GameTheory.Profile service.setup.intendedModel.behavioralSignature)
    (source :
        GameTheory.Profile
          (service.sourceModel (Vegas.SourceProgram.CommitmentInterface.values
            service.setup.program)).behavioralSignature)
    (agrees :
        (service.setup.intendedRestriction
              (Vegas.SourceProgram.CommitmentInterface.values service.setup.program)).ExtendsProfile
          intended source)
    (ε : ℝ)
    (_equilibrium :
        GameTheory.IsεNash (service.setup.intendedModel.toBehavioralGameForm
          (service.setup.program.instructionCount + 1))
          (fun
              (final :
                (service.setup.intendedModel.toBehavioralGameForm
                  (service.setup.program.instructionCount + 1)).sig.Outcome)
              (who : Player) =>
            (service.setup.protocolReadout final.state).elim 0
              fun (state : Vegas.SourceProgram.Config Player L service.setup.program.terminalCtx) =>
              utility (service.setup.parameterOutcome parameter state) who)
          ε intended) :
    have forfeited := service.setup.program.forfeitUtility forfeit utility;
      have base :=
        Vegas.serviceBaseUtility service.setup service.mode service.deadline service.leaks
          fun (state : Vegas.SourceProgram.Config Player L service.setup.program.terminalCtx) =>
          forfeited (service.setup.parameterOutcome parameter state);
      have payoff :=
        GameTheory.Enforcement.TerminalAudit.utility base
          ((Vegas.serviceRuntime service.setup service.mode
            service.deadline).serviceAuditObservation service.leaks)
          (Vegas.serviceSourceAudit service.setup service.mode service.deadline service.leaks
            sample) deposit;
      have settle :=
        GameTheory.Enforcement.TerminalAudit.settlement base
          ((Vegas.serviceRuntime service.setup service.mode
            service.deadline).serviceAuditObservation service.leaks)
          (Vegas.serviceSourceAudit service.setup service.mode service.deadline service.leaks
            sample) deposit;
      GameTheory.IsεNash
          ((service.rawMenu.information (Vegas.serviceInitialLaw service.setup service.mode)
            service.horizon
                service.scheduler).toBehavioralGameForm
            (2 * service.horizon + 1))
          (fun
              (history :
                ((service.rawMenu.information (Vegas.serviceInitialLaw service.setup
                  service.mode) service.horizon
                          service.scheduler).toBehavioralGameForm
                      (2 * service.horizon + 1)).sig.Outcome)
              (who : Player) =>
            payoff history.state who)
          (ε + 2 * timing.deferralError * spread)
          (service.clientProfile (Vegas.SourceProgram.CommitmentInterface.values
            service.setup.program) service.rawMenu
            timing source) ∧
        PMF.WithinTV timing.deferralError
          (((service.rawMenu.information (Vegas.serviceInitialLaw service.setup service.mode)
            service.horizon
                    service.scheduler).runBehavioral
                (service.clientProfile (Vegas.SourceProgram.CommitmentInterface.values
                  service.setup.program)
                  service.rawMenu timing source)
                (2 * service.horizon + 1)).bind
            fun
              (final :
                (service.rawMenu.protocol (Vegas.serviceInitialLaw service.setup service.mode)
                  service.horizon
                    service.scheduler).History) =>
            PMF.map
              (fun (payoffs : Player → ℝ) =>
                (Option.map
                    (fun (config : Vegas.SourceProgram.Config Player L
                      service.setup.program.terminalCtx) =>
                      (config.state, config.defaults))
                    (Vegas.serviceSourceReadout service.setup service.mode service.deadline
                      service.leaks final.state),
                  payoffs))
              (settle final.state))
          (PMF.map
            (fun (final : service.setup.intendedProtocol.History) =>
              (Option.map
                  (fun (config : Vegas.SourceProgram.Config Player L
                    service.setup.program.terminalCtx) =>
                    (config.state, config.defaults))
                  (service.setup.protocolReadout final.state),
                fun (who : Player) =>
                (service.setup.protocolReadout final.state).elim 0
                  fun (state : Vegas.SourceProgram.Config Player L
                    service.setup.program.terminalCtx) =>
                  utility (service.setup.parameterOutcome parameter state) who))
            (service.setup.intendedModel.runBehavioral intended
              (service.setup.program.instructionCount + 1))) := by
  exact @Vegas.AsyncServiceSpec.intended_rawClientProfile_isεNash
    Player inst inst_1 L inst_2 service Parameter ordered wellFormed parameter utility forfeit
      range sample authentic deposit nonnegative turns timing low spread within intended source
        agrees ε _equilibrium

/-- info: 'Vegas.Paper.intended_rawClientProfile_isεNash' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.intended_rawClientProfile_isεNash

/-- The paper statement has its proof in
`Vegas.AsyncServiceSpec.isεNash_firstTurnClientProfile_iff`. -/
theorem Vegas.Paper.isεNash_firstTurnClientProfile_iff
    {Player : Type}
    [inst : DecidableEq Player]
    [inst_1 : Fintype Player]
    {L : Vegas.IExpr}
    [inst_2 : L.ResultTypes]
    (service : Vegas.AsyncServiceSpec Player L)
    (admission : service.setup.program.CommitmentInterface)
    {Parameter : Type}
    (ordered : (Vegas.serviceGraph service.setup service.mode).BarrierOrdered)
    (parameter : Vegas.State L service.setup.context → Parameter)
    (utility : Parameter × service.setup.program.PublicOutcome → Player → ℝ)
    (sample :
        List (Vegas.SettledEvidence service.setup service.mode) →
          PMF (List (Vegas.SettledEvidence service.setup service.mode)))
    (authentic :
        ∀ (actual observed : List (Vegas.SettledEvidence service.setup service.mode)),
          observed ∈ (sample actual).support → observed ⊆ actual)
    (deposit : Player → ℝ)
    (nonnegative : ∀ (who : Player), 0 ≤ deposit who)
    (turns : ℕ)
    (low : Player → ℝ)
    (range : ℝ)
    (within : service.SettlementRange parameter utility sample deposit low fun (_x : Player) =>
      range)
    (ε : ℝ)
    (source : GameTheory.Profile (service.sourceModel admission).behavioralSignature) :
    have base :=
        Vegas.serviceBaseUtility service.setup service.mode service.deadline service.leaks
          fun (state : Vegas.SourceProgram.Config Player L service.setup.program.terminalCtx) =>
          utility (service.setup.parameterOutcome parameter state);
      have payoff :=
        GameTheory.Enforcement.TerminalAudit.utility base
          ((Vegas.serviceRuntime service.setup service.mode
            service.deadline).serviceAuditObservation service.leaks)
          (Vegas.serviceSourceAudit service.setup service.mode service.deadline service.leaks
            sample) deposit;
      GameTheory.IsεNash
          ((service.rawMenu.information (Vegas.serviceInitialLaw service.setup service.mode)
            service.horizon
                service.scheduler).toBehavioralGameForm
            (2 * service.horizon + 1))
          (fun
              (history :
                ((service.rawMenu.information (Vegas.serviceInitialLaw service.setup
                  service.mode) service.horizon
                          service.scheduler).toBehavioralGameForm
                      (2 * service.horizon + 1)).sig.Outcome)
              (who : Player) =>
            payoff history.state who)
          ε
          (service.clientProfile admission service.rawMenu (Vegas.firstTurnTiming service.setup
            turns service.mode)
            source) ↔
        GameTheory.IsεNash
          ((service.sourceModel admission).toBehavioralGameForm
            (service.setup.program.instructionCount + 1))
          (fun
              (final :
                ((service.sourceModel admission).toBehavioralGameForm
                      (service.setup.program.instructionCount + 1)).sig.Outcome)
              (who : Player) =>
            (service.setup.protocolReadout final.state).elim 0
              fun (state : Vegas.SourceProgram.Config Player L service.setup.program.terminalCtx) =>
              utility (service.setup.parameterOutcome parameter state) who)
          ε source := by
  exact @Vegas.AsyncServiceSpec.isεNash_firstTurnClientProfile_iff
    Player inst inst_1 L inst_2 service admission Parameter ordered parameter utility sample
      authentic deposit nonnegative turns low range within ε source

/-- info: 'Vegas.Paper.isεNash_firstTurnClientProfile_iff' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.isεNash_firstTurnClientProfile_iff

/-- The paper statement has its proof in
`Vegas.AsyncServiceSpec.intended_firstTurnClientProfile_isεNash`. -/
theorem Vegas.Paper.intended_firstTurnClientProfile_isεNash
    {Player : Type}
    [inst : DecidableEq Player]
    [inst_1 : Fintype Player]
    {L : Vegas.IExpr}
    [inst_2 : L.ResultTypes]
    (service : Vegas.AsyncServiceSpec Player L)
    {Parameter : Type}
    (ordered : (Vegas.serviceGraph service.setup service.mode).BarrierOrdered)
    (wellFormed : service.setup.WellFormed)
    (parameter : Vegas.State L service.setup.context → Parameter)
    (utility : Parameter × service.setup.program.PublicOutcome → Player → ℝ)
    (forfeit : ℝ)
    (range :
        service.setup.TerminalPayoffSpread (Vegas.SourceProgram.CommitmentInterface.values
          service.setup.program) parameter
          utility forfeit)
    (sample :
        List (Vegas.SettledEvidence service.setup service.mode) →
          PMF (List (Vegas.SettledEvidence service.setup service.mode)))
    (authentic :
        ∀ (actual observed : List (Vegas.SettledEvidence service.setup service.mode)),
          observed ∈ (sample actual).support → observed ⊆ actual)
    (deposit : Player → ℝ)
    (nonnegative : ∀ (who : Player), 0 ≤ deposit who)
    (turns : ℕ)
    (low : Player → ℝ)
    (spread : ℝ)
    (within :
        service.SettlementRange parameter (service.setup.program.forfeitUtility forfeit
          utility) sample deposit low
          fun (_x : Player) => spread)
    (intended : GameTheory.Profile service.setup.intendedModel.behavioralSignature)
    (source :
        GameTheory.Profile
          (service.sourceModel (Vegas.SourceProgram.CommitmentInterface.values
            service.setup.program)).behavioralSignature)
    (agrees :
        (service.setup.intendedRestriction
              (Vegas.SourceProgram.CommitmentInterface.values service.setup.program)).ExtendsProfile
          intended source)
    (ε : ℝ)
    (_equilibrium :
        GameTheory.IsεNash (service.setup.intendedModel.toBehavioralGameForm
          (service.setup.program.instructionCount + 1))
          (fun
              (final :
                (service.setup.intendedModel.toBehavioralGameForm
                  (service.setup.program.instructionCount + 1)).sig.Outcome)
              (who : Player) =>
            (service.setup.protocolReadout final.state).elim 0
              fun (state : Vegas.SourceProgram.Config Player L service.setup.program.terminalCtx) =>
              utility (service.setup.parameterOutcome parameter state) who)
          ε intended) :
    have forfeited := service.setup.program.forfeitUtility forfeit utility;
      have base :=
        Vegas.serviceBaseUtility service.setup service.mode service.deadline service.leaks
          fun (state : Vegas.SourceProgram.Config Player L service.setup.program.terminalCtx) =>
          forfeited (service.setup.parameterOutcome parameter state);
      have payoff :=
        GameTheory.Enforcement.TerminalAudit.utility base
          ((Vegas.serviceRuntime service.setup service.mode
            service.deadline).serviceAuditObservation service.leaks)
          (Vegas.serviceSourceAudit service.setup service.mode service.deadline service.leaks
            sample) deposit;
      have settle :=
        GameTheory.Enforcement.TerminalAudit.settlement base
          ((Vegas.serviceRuntime service.setup service.mode
            service.deadline).serviceAuditObservation service.leaks)
          (Vegas.serviceSourceAudit service.setup service.mode service.deadline service.leaks
            sample) deposit;
      GameTheory.IsεNash
          ((service.rawMenu.information (Vegas.serviceInitialLaw service.setup service.mode)
            service.horizon
                service.scheduler).toBehavioralGameForm
            (2 * service.horizon + 1))
          (fun
              (history :
                ((service.rawMenu.information (Vegas.serviceInitialLaw service.setup
                  service.mode) service.horizon
                          service.scheduler).toBehavioralGameForm
                      (2 * service.horizon + 1)).sig.Outcome)
              (who : Player) =>
            payoff history.state who)
          ε
          (service.clientProfile (Vegas.SourceProgram.CommitmentInterface.values
            service.setup.program) service.rawMenu
            (Vegas.firstTurnTiming service.setup turns service.mode) source) ∧
        (((service.rawMenu.information (Vegas.serviceInitialLaw service.setup service.mode)
          service.horizon
                    service.scheduler).runBehavioral
                (service.clientProfile (Vegas.SourceProgram.CommitmentInterface.values
                  service.setup.program)
                  service.rawMenu (Vegas.firstTurnTiming service.setup turns service.mode) source)
                (2 * service.horizon + 1)).bind
            fun
              (final :
                (service.rawMenu.protocol (Vegas.serviceInitialLaw service.setup service.mode)
                  service.horizon
                    service.scheduler).History) =>
            PMF.map
              (fun (payoffs : Player → ℝ) =>
                (Option.map
                    (fun (config : Vegas.SourceProgram.Config Player L
                      service.setup.program.terminalCtx) =>
                      (config.state, config.defaults))
                    (Vegas.serviceSourceReadout service.setup service.mode service.deadline
                      service.leaks final.state),
                  payoffs))
              (settle final.state)) =
          PMF.map
            (fun (final : service.setup.intendedProtocol.History) =>
              (Option.map
                  (fun (config : Vegas.SourceProgram.Config Player L
                    service.setup.program.terminalCtx) =>
                    (config.state, config.defaults))
                  (service.setup.protocolReadout final.state),
                fun (who : Player) =>
                (service.setup.protocolReadout final.state).elim 0
                  fun (state : Vegas.SourceProgram.Config Player L
                    service.setup.program.terminalCtx) =>
                  utility (service.setup.parameterOutcome parameter state) who))
            (service.setup.intendedModel.runBehavioral intended
              (service.setup.program.instructionCount + 1)) := by
  exact @Vegas.AsyncServiceSpec.intended_firstTurnClientProfile_isεNash
    Player inst inst_1 L inst_2 service Parameter ordered wellFormed parameter utility forfeit
      range sample authentic deposit nonnegative turns low spread within intended source agrees
        ε _equilibrium

/-- info: 'Vegas.Paper.intended_firstTurnClientProfile_isεNash' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.intended_firstTurnClientProfile_isεNash

/-- The paper statement has its proof in
`Vegas.AsyncServiceSpec.clientSettlementLaw_withinTV`. -/
theorem Vegas.Paper.clientSettlementLaw_withinTV
    {Player : Type}
    [inst : DecidableEq Player]
    [inst_1 : Fintype Player]
    {L : Vegas.IExpr}
    [inst_2 : L.ResultTypes]
    (service : Vegas.AsyncServiceSpec Player L)
    (admission : service.setup.program.CommitmentInterface)
    (ordered : (Vegas.serviceGraph service.setup service.mode).BarrierOrdered)
    {turns : ℕ}
    (timing : Vegas.TurnTiming service.setup turns service.mode)
    (source : GameTheory.Profile (service.sourceModel admission).behavioralSignature)
    (sample :
        List (Vegas.SettledEvidence service.setup service.mode) →
          PMF (List (Vegas.SettledEvidence service.setup service.mode)))
    (authentic :
        ∀ (actual observed : List (Vegas.SettledEvidence service.setup service.mode)),
          observed ∈ (sample actual).support → observed ⊆ actual)
    (utility : Vegas.State L service.setup.program.terminalCtx × Vegas.DefaultHistory Player →
      Player → ℝ)
    (deposit : Player → ℝ) :
    PMF.WithinTV timing.deferralError (service.clientSettlementLaw admission timing source
      sample utility deposit)
        (service.sourceSettlementLaw admission source utility) := by
  exact @Vegas.AsyncServiceSpec.clientSettlementLaw_withinTV
    Player inst inst_1 L inst_2 service admission ordered turns timing source sample authentic
      utility deposit

/-- info: 'Vegas.Paper.clientSettlementLaw_withinTV' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.clientSettlementLaw_withinTV

/-- The paper statement has its proof in
`Vegas.AsyncServiceSpec.clientSettlementLaw_event_lower_bound`. -/
theorem Vegas.Paper.clientSettlementLaw_event_lower_bound
    {Player : Type}
    [inst : DecidableEq Player]
    [inst_1 : Fintype Player]
    {L : Vegas.IExpr}
    [inst_2 : L.ResultTypes]
    (service : Vegas.AsyncServiceSpec Player L)
    (admission : service.setup.program.CommitmentInterface)
    (ordered : (Vegas.serviceGraph service.setup service.mode).BarrierOrdered)
    {turns : ℕ}
    (timing : Vegas.TurnTiming service.setup turns service.mode)
    (source : GameTheory.Profile (service.sourceModel admission).behavioralSignature)
    (sample :
        List (Vegas.SettledEvidence service.setup service.mode) →
          PMF (List (Vegas.SettledEvidence service.setup service.mode)))
    (authentic :
        ∀ (actual observed : List (Vegas.SettledEvidence service.setup service.mode)),
          observed ∈ (sample actual).support → observed ⊆ actual)
    (utility : Vegas.State L service.setup.program.terminalCtx × Vegas.DefaultHistory Player →
      Player → ℝ)
    (deposit : Player → ℝ)
    (event : Set (Vegas.TerminalObservation service.setup))
    (lower : ℝ)
    (sourceLower :
        lower ≤
          (((service.sourceSettlementLaw admission source utility).toOuterMeasure :
                (a : Set (Vegas.TerminalObservation service.setup)) → ENNReal)
              event).toReal) :
    lower - timing.deferralError ≤
        (((service.clientSettlementLaw admission timing source sample utility
          deposit).toOuterMeasure :
              (a : Set (Vegas.TerminalObservation service.setup)) → ENNReal)
            event).toReal := by
  exact @Vegas.AsyncServiceSpec.clientSettlementLaw_event_lower_bound
    Player inst inst_1 L inst_2 service admission ordered turns timing source sample authentic
      utility deposit event lower sourceLower

/-- info: 'Vegas.Paper.clientSettlementLaw_event_lower_bound' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.clientSettlementLaw_event_lower_bound

/-- The paper statement has its proof in
`Vegas.AsyncServiceSpec.clientSettlementLaw_expect_lower_bound`. -/
theorem Vegas.Paper.clientSettlementLaw_expect_lower_bound
    {Player : Type}
    [inst : DecidableEq Player]
    [inst_1 : Fintype Player]
    {L : Vegas.IExpr}
    [inst_2 : L.ResultTypes]
    (service : Vegas.AsyncServiceSpec Player L)
    (admission : service.setup.program.CommitmentInterface)
    (ordered : (Vegas.serviceGraph service.setup service.mode).BarrierOrdered)
    {turns : ℕ}
    (timing : Vegas.TurnTiming service.setup turns service.mode)
    (source : GameTheory.Profile (service.sourceModel admission).behavioralSignature)
    (sample :
        List (Vegas.SettledEvidence service.setup service.mode) →
          PMF (List (Vegas.SettledEvidence service.setup service.mode)))
    (authentic :
        ∀ (actual observed : List (Vegas.SettledEvidence service.setup service.mode)),
          observed ∈ (sample actual).support → observed ⊆ actual)
    (utility : Vegas.State L service.setup.program.terminalCtx × Vegas.DefaultHistory Player →
      Player → ℝ)
    (deposit : Player → ℝ)
    (observable : Vegas.TerminalObservation service.setup → ℝ)
    (low width lower : ℝ)
    (bounded :
        ∀ (result : Vegas.TerminalObservation service.setup),
          result ∈ (service.clientSettlementLaw admission timing source sample utility
            deposit).support ∨
              result ∈ (service.sourceSettlementLaw admission source utility).support →
            low ≤ observable result ∧ observable result ≤ low + width)
    (sourceLower :
        lower ≤ GameTheory.Math.Probability.expect (service.sourceSettlementLaw admission
          source utility) observable) :
    GameTheory.Math.Probability.PayoffIntegrable
          (service.clientSettlementLaw admission timing source sample utility deposit) observable ∧
        GameTheory.Math.Probability.PayoffIntegrable (service.sourceSettlementLaw admission
          source utility) observable ∧
          lower - timing.deferralError * width ≤
            GameTheory.Math.Probability.expect (service.clientSettlementLaw admission timing
              source sample utility deposit)
              observable := by
  exact @Vegas.AsyncServiceSpec.clientSettlementLaw_expect_lower_bound
    Player inst inst_1 L inst_2 service admission ordered turns timing source sample authentic
      utility deposit observable low width lower bounded sourceLower

/-- info: 'Vegas.Paper.clientSettlementLaw_expect_lower_bound' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.clientSettlementLaw_expect_lower_bound

/-- The paper statement has its proof in
`Vegas.asyncDeviation_readout_law`. -/
theorem Vegas.Paper.asyncDeviation_readout_law
    {Player : Type}
    [inst : DecidableEq Player]
    {L : Vegas.IExpr}
    [inst_1 : L.ResultTypes]
    (setup : Vegas.SourceProgram.Setup (Player := Player) (L := L))
    {mode : Vegas.EventGraph.ExecutionMode}
    {deadline : (Vegas.serviceGraph setup mode).EventId → ℕ}
    (leaks :
        Interaction.MessageNetwork.ObservationRule Player
          (Vegas.EventGraphRuntime.WitnessedPacket (Vegas.serviceGraph setup mode)))
    (ordered : (Vegas.serviceGraph setup mode).BarrierOrdered)
    {horizon : ℕ}
    {scheduler : (Vegas.serviceApplication setup mode deadline leaks).Scheduler}
    {delay bound : (Vegas.serviceGraph setup mode).EventId → ℕ}
    (contract :
        (Vegas.serviceRuntime setup mode deadline).AsyncContract leaks (Vegas.serviceInitialLaw
          setup mode) horizon
          scheduler delay bound)
    (timely : (Vegas.serviceRuntime setup mode deadline).AsyncTimely delay bound)
    (turns : ℕ)
    (original : setup.program.BehavioralProfile)
    (who : Player)
    (deviation : (Vegas.serviceApplication setup mode deadline leaks).Policy) :
    ∃ (policy : Vegas.SourceProgram.BehavioralPolicy who setup.program),
        PMF.map
            (fun (execution : (Vegas.serviceApplication setup mode deadline leaks).Execution) =>
              Option.map
                (fun (final : Vegas.SourceProgram.Config Player L setup.program.terminalCtx) =>
                  (final.state, final.defaults))
                (Vegas.serviceSourceReadout setup mode deadline leaks
                  ((Vegas.serviceApplication setup mode deadline leaks).finished execution)))
            ((Vegas.serviceApplication setup mode deadline leaks).roundsFrom
              (Vegas.serviceInitialLaw setup mode) scheduler
              (Function.update
                (Vegas.serviceTurnPolicy setup mode deadline leaks bound turns
                  (Vegas.firstTurnTiming setup turns mode)
                  (setup.program.normalizeDisclosureProfile original))
                who deviation)
              horizon) =
          PMF.map
            (fun (final : Vegas.SourceProgram.Config Player L setup.program.terminalCtx) =>
              some (final.state, final.defaults))
            (setup.run (Function.update original who policy)) := by
  exact @Vegas.asyncDeviation_readout_law
    Player inst L inst_1 setup mode deadline leaks ordered horizon scheduler delay bound
      contract timely turns original who deviation

/-- info: 'Vegas.Paper.asyncDeviation_readout_law' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.asyncDeviation_readout_law

/-- The paper statement has its proof in
`Vegas.AsyncServiceSpec.payment_firstTurnClientProfile_settlement_law`. -/
theorem Vegas.Paper.payment_firstTurnClientProfile_settlement_law
    {Player : Type}
    [inst : DecidableEq Player]
    {L : Vegas.IExpr}
    [inst_1 : L.ResultTypes]
    (service : Vegas.AsyncServiceSpec Player L)
    [inst_2 : Fintype Player]
    (admission : service.setup.program.CommitmentInterface)
    (ordered : (Vegas.serviceGraph service.setup service.mode).BarrierOrdered)
    (sample :
        List (Vegas.SettledEvidence service.setup service.mode) →
          PMF (List (Vegas.SettledEvidence service.setup service.mode)))
    (authentic :
        ∀ (actual observed : List (Vegas.SettledEvidence service.setup service.mode)),
          observed ∈ (sample actual).support → observed ⊆ actual)
    (deposit : Player → ℝ)
    (turns : ℕ)
    (source : GameTheory.Profile (service.sourceModel admission).behavioralSignature) :
    (((service.rawMenu.information (Vegas.serviceInitialLaw service.setup service.mode)
      service.horizon
                  service.scheduler).runBehavioral
              (service.clientProfile admission service.rawMenu (Vegas.firstTurnTiming
                service.setup turns service.mode)
                source)
              (2 * service.horizon + 1)).bind
          fun
            (final :
              (service.rawMenu.protocol (Vegas.serviceInitialLaw service.setup service.mode)
                service.horizon
                  service.scheduler).History) =>
          PMF.map
            (fun (receipts : Player → ℝ) =>
              (Option.map
                  (fun (config : Vegas.SourceProgram.Config Player L
                    service.setup.program.terminalCtx) =>
                    (config.state, config.defaults))
                  (Vegas.serviceSourceReadout service.setup service.mode service.deadline
                    service.leaks final.state),
                receipts))
            (service.paymentSettlement sample deposit final.state)) =
        PMF.map
          (fun (terminal : Vegas.SourceProgram.Config Player L service.setup.program.terminalCtx) =>
            (some (terminal.state, terminal.defaults), fun (who : Player) =>
              service.setup.transfers (service.setup.program.publicOutcome terminal) who))
          (service.setup.run (service.setup.decodeBehavioralProfile admission source)) := by
  exact @Vegas.AsyncServiceSpec.payment_firstTurnClientProfile_settlement_law
    Player inst L inst_1 service inst_2 admission ordered sample authentic deposit turns source

/-- info: 'Vegas.Paper.payment_firstTurnClientProfile_settlement_law' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.payment_firstTurnClientProfile_settlement_law

/-- The paper statement has its proof in
`Vegas.intended_raw_programPayments_preserved`. -/
theorem Vegas.Paper.intended_raw_programPayments_preserved
    {Player : Type}
    [instDecEq : DecidableEq Player]
    [instFintype : Fintype Player]
    {L : Vegas.IExpr}
    [instResult : L.ResultTypes]
    (setup : Vegas.SourceProgram.Setup (Player := Player) (L := L))
    (runtime : Vegas.EventGraphRuntime (Vegas.graph setup))
    (leaks :
        Interaction.MessageNetwork.ObservationRule Player
          (Vegas.EventGraphRuntime.WitnessedPacket (Vegas.graph setup)))
    (bounds : Vegas.EventGraphRuntime.MessageBounds (Vegas.graph setup))
    (horizon : ℕ)
    (scheduler : (Vegas.application setup runtime leaks).Scheduler)
    {Parameter : Type}
    (parameter : Vegas.State L setup.context → Parameter)
    (_valuation : Parameter × setup.program.PublicOutcome → Player → ℝ)
    (exitValuation : Player → ℝ)
    (spec :
        Vegas.ClientSpec setup runtime leaks bounds horizon scheduler parameter
          (setup.parameterPaymentUtility _valuation)
          fun (who : Player) => exitValuation who + (fun (who : Player) =>
            (↑(setup.exitTransfers who) : ℝ)) who)
    (intended : setup.intendedModel.BehavioralAssessment)
    (_equilibrium : setup.IntendedSequentialEquilibrium parameter
      (setup.parameterPaymentUtility _valuation) intended) :
    have observe := (Vegas.application setup runtime leaks).stateTraffic;
      have audit := runtime.countAudit leaks spec.evidenceService.sample;
      ∃ (compiled : Vegas.ClientCompilation spec intended),
        have target := compiled.assessment;
        ((((bounds.rawMenu runtime leaks).information (Vegas.initialLaw setup) horizon
          scheduler).runBehavioral
                target.strategy (2 * horizon + 1)).bind
            fun (final : ((bounds.rawMenu runtime leaks).protocol (Vegas.initialLaw setup)
              horizon scheduler).History) =>
            PMF.map
              (fun (receipts : Player → ℝ) =>
                Vegas.TerminalObservation.read setup
                  (Option.map
                    (fun (config : Vegas.SourceProgram.Config Player L setup.program.terminalCtx) =>
                      (config.state, config.defaults))
                    (Vegas.sourceReadout setup runtime leaks final.state))
                  receipts)
              (GameTheory.Enforcement.TerminalAudit.settlement
                (Vegas.exclusionBase setup runtime parameter
                  (fun (outcome : Parameter × setup.program.PublicOutcome) (who : Player) =>
                    setup.transfers outcome.2 who)
                  (fun (who : Player) => (↑(setup.exitTransfers who) : ℝ)) leaks)
                observe audit spec.deposit final.state)) =
          PMF.map
            (fun (final : setup.intendedProtocol.History) =>
              Vegas.TerminalObservation.read setup
                (Option.map
                  (fun (config : Vegas.SourceProgram.Config Player L setup.program.terminalCtx) =>
                    (config.state, config.defaults))
                  (setup.protocolReadout final.state))
                fun (who : Player) =>
                (setup.protocolReadout final.state).elim 0
                  fun (terminal : Vegas.SourceProgram.Config Player L setup.program.terminalCtx) =>
                  setup.transfers (setup.program.publicOutcome terminal) who)
            (setup.intendedModel.runBehavioral intended.strategy
              (setup.program.instructionCount + 1)) := by
  exact @Vegas.intended_raw_programPayments_preserved
    Player instDecEq instFintype L instResult setup runtime leaks bounds horizon scheduler
      Parameter parameter _valuation exitValuation spec intended _equilibrium

/-- info: 'Vegas.Paper.intended_raw_programPayments_preserved' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.intended_raw_programPayments_preserved

/-- The paper statement has its proof in
`Vegas.EventGraphRuntime.MessageBounds.onePacket_raw_sequentialEquilibrium`. -/
theorem Vegas.Paper.onePacket_raw_sequentialEquilibrium
    {Player : Type}
    [inst : DecidableEq Player]
    [inst_1 : Fintype Player]
    {L : Vegas.IExpr}
    [inst_2 : L.ResultTypes]
    {graph : Vegas.EventGraph Player L}
    (bounds : Vegas.EventGraphRuntime.MessageBounds graph)
    (runtime : Vegas.EventGraphRuntime graph)
    (leaks : Interaction.MessageNetwork.ObservationRule Player
      (Vegas.EventGraphRuntime.WitnessedPacket graph))
    (initial : PMF (Vegas.EventGraphRuntime.State graph))
    (horizon : ℕ)
    (scheduler : (runtime.reactiveApplication leaks).Scheduler)
    [_instance12 : (runtime.reactiveApplication leaks).FiniteNature initial scheduler]
    (service : Interaction.EvidenceReportService (Vegas.EventGraphRuntime.CountEvidence graph))
    (observationRate deliveryRate : Player → ℝ)
    (delivery_nonnegative : ∀ (who : Player), 0 ≤ deliveryRate who)
    (coverage : Vegas.EventGraphRuntime.CountEvidenceCoverage service observationRate deliveryRate)
    (utility : (runtime.reactiveApplication leaks).ProtocolState → Player → ℝ)
    (normalized :
        ∀ (state : (runtime.reactiveApplication leaks).ProtocolState),
          utility ((runtime.reactiveNormalization leaks).state state) = utility state)
    (lower upper deposit : Player → ℝ)
    (lower_le :
        ∀ (history : ((bounds.rawMenu runtime leaks).protocol initial horizon
          scheduler).History) (who : Player),
          lower who ≤ utility history.state who)
    (le_upper :
        ∀ (history : ((bounds.rawMenu runtime leaks).protocol initial horizon
          scheduler).History) (who : Player),
          utility history.state who ≤ upper who)
    (deposit_nonnegative : ∀ (who : Player), 0 ≤ deposit who)
    (sufficient : ∀ (who : Player), upper who - lower who ≤ observationRate who * deliveryRate
      who * deposit who) :
    have onePacket := Vegas.EventGraphRuntime.MessageBounds.onePacketMenu runtime leaks bounds;
      have raw := bounds.rawMenu runtime leaks;
      have sourceCertificate :=
        GameTheory.Protocol.ExecutionProtocol.BoundedHorizon.wellFoundedHistories
          (Interaction.ReactiveApplication.ResponseMenu.bounded onePacket initial horizon
            scheduler);
      have normalize := (runtime.reactiveNormalization leaks).state;
      have observe := (runtime.reactiveApplication leaks).stateTraffic;
      have audit := runtime.countAudit leaks service.sample;
      have payoff := GameTheory.Enforcement.TerminalAudit.utility utility observe audit deposit;
      have settle := GameTheory.Enforcement.TerminalAudit.settlement utility observe audit deposit;
      ∀ (source : (onePacket.information initial horizon scheduler).BehavioralAssessment),
        (source.IsSequentialEquilibrium
            (Interaction.ReactiveApplication.ResponseMenu.decisionInformationAntichain
              onePacket initial horizon scheduler)
            sourceCertificate fun (who : Player) (final : (onePacket.protocol initial horizon
              scheduler).History) =>
            utility final.state who) →
          ∃ (target : (raw.information initial horizon scheduler).BehavioralAssessment),
            (target.IsSequentialEquilibriumFor
                (Interaction.ReactiveApplication.ResponseMenu.decisionInformationAntichain raw
                  initial horizon scheduler)
                fun (who : Player) (site : (raw.information initial horizon
                  scheduler).InformationSite who) =>
                target.truncatedContinuationContext site
                  (fun (history : (raw.protocol initial horizon scheduler).History) => payoff
                    history.state who)
                  (2 * horizon + 1)) ∧
              (∀
                  final ∈
                    ((raw.information initial horizon scheduler).runBehavioral target.strategy
                      (2 * horizon + 1)).support,
                  ∀ (who : Player), GameTheory.Enforcement.TerminalAudit.charge observe audit
                    final.state who = 0) ∧
                PMF.map (fun (final : (raw.protocol initial horizon scheduler).History) =>
                  normalize final.state)
                      ((raw.information initial horizon scheduler).runBehavioral
                        target.strategy (2 * horizon + 1)) =
                    PMF.map GameTheory.Protocol.ExecutionProtocol.History.state
                      ((onePacket.information initial horizon scheduler).runBehavioral
                        source.strategy (2 * horizon + 1)) ∧
                  (((raw.information initial horizon scheduler).runBehavioral target.strategy
                    (2 * horizon + 1)).bind
                      fun (final : (raw.protocol initial horizon scheduler).History) =>
                      PMF.map (fun (payoffs : Player → ℝ) => (normalize final.state, payoffs))
                        (settle final.state)) =
                    PMF.map
                      (fun (final : (onePacket.protocol initial horizon scheduler).History) =>
                        (final.state, utility final.state))
                      ((onePacket.information initial horizon scheduler).runBehavioral
                        source.strategy (2 * horizon + 1)) := by
  exact @Vegas.EventGraphRuntime.MessageBounds.onePacket_raw_sequentialEquilibrium
    Player inst inst_1 L inst_2 graph bounds runtime leaks initial horizon scheduler
      _instance12 service observationRate deliveryRate delivery_nonnegative coverage utility
        normalized lower upper deposit lower_le le_upper deposit_nonnegative sufficient

/-- info: 'Vegas.Paper.onePacket_raw_sequentialEquilibrium' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.onePacket_raw_sequentialEquilibrium

/-- The paper statement has its proof in
`Vegas.intended_raw_sequentialEquilibrium_preserved`. -/
theorem Vegas.Paper.intended_raw_sequentialEquilibrium_preserved
    {Player : Type}
    [inst : DecidableEq Player]
    [inst_1 : Fintype Player]
    {L : Vegas.IExpr}
    [inst_2 : L.ResultTypes]
    {setup : Vegas.SourceProgram.Setup (Player := Player) (L := L)}
    {runtime : Vegas.EventGraphRuntime (Vegas.graph setup)}
    {leaks :
        Interaction.MessageNetwork.ObservationRule Player
          (Vegas.EventGraphRuntime.WitnessedPacket (Vegas.graph setup))}
    {bounds : Vegas.EventGraphRuntime.MessageBounds (Vegas.graph setup)}
    {horizon : ℕ}
    {scheduler : (Vegas.application setup runtime leaks).Scheduler}
    {Parameter : Type}
    {parameter : Vegas.State L setup.context → Parameter}
    {utility : Parameter × setup.program.PublicOutcome → Player → ℝ}
    {excludedPayoff : Player → ℝ}
    (spec : Vegas.ClientSpec setup runtime leaks bounds horizon scheduler parameter utility
      excludedPayoff)
    (intended : setup.intendedModel.BehavioralAssessment)
    (_equilibrium : setup.IntendedSequentialEquilibrium parameter utility intended) :
    Nonempty (Vegas.ClientCompilation spec intended) := by
  exact @Vegas.intended_raw_sequentialEquilibrium_preserved
    Player inst inst_1 L inst_2 setup runtime leaks bounds horizon scheduler Parameter
      parameter utility excludedPayoff spec intended _equilibrium

/-- info: 'Vegas.Paper.intended_raw_sequentialEquilibrium_preserved' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.intended_raw_sequentialEquilibrium_preserved

/-- The paper statement has its proof in
`Vegas.ClientSpec.compile_correct`. -/
theorem Vegas.Paper.compile_correct
    {Player : Type}
    [inst : DecidableEq Player]
    [inst_1 : Fintype Player]
    {L : Vegas.IExpr}
    [inst_2 : L.ResultTypes]
    {setup : Vegas.SourceProgram.Setup (Player := Player) (L := L)}
    {runtime : Vegas.EventGraphRuntime (Vegas.graph setup)}
    {leaks :
        Interaction.MessageNetwork.ObservationRule Player
          (Vegas.EventGraphRuntime.WitnessedPacket (Vegas.graph setup))}
    {bounds : Vegas.EventGraphRuntime.MessageBounds (Vegas.graph setup)}
    {horizon : ℕ}
    {scheduler : (Vegas.application setup runtime leaks).Scheduler}
    {Parameter : Type}
    {parameter : Vegas.State L setup.context → Parameter}
    {utility : Parameter × setup.program.PublicOutcome → Player → ℝ}
    {excludedPayoff : Player → ℝ}
    (spec : Vegas.ClientSpec setup runtime leaks bounds horizon scheduler parameter utility
      excludedPayoff)
    (intended : setup.intendedModel.BehavioralAssessment)
    (_equilibrium : setup.IntendedSequentialEquilibrium parameter utility intended) :
    have compiled := spec.compile intended _equilibrium;
      (compiled.assessment.IsSequentialEquilibriumFor
          (Interaction.ReactiveApplication.ResponseMenu.decisionInformationAntichain
            (bounds.rawMenu runtime leaks)
            (Vegas.initialLaw setup) horizon scheduler)
          fun (who : Player)
            (site :
              ((bounds.rawMenu runtime leaks).information (Vegas.initialLaw setup) horizon
                scheduler).InformationSite
                who) =>
          compiled.assessment.truncatedContinuationContext site
            (fun (final : ((bounds.rawMenu runtime leaks).protocol (Vegas.initialLaw setup)
              horizon scheduler).History) =>
              spec.payoff who final.state)
            (2 * horizon + 1)) ∧
        (∀ (who : Player),
            (bounds.rawMenu runtime leaks).restrictPolicy (Vegas.initialLaw setup) horizon
              scheduler who
                (compiled.clients who) =
              compiled.assessment.strategy who) ∧
          ((Vegas.application setup runtime leaks).finish (Vegas.initialLaw setup) horizon
            scheduler compiled.clients
                  none).bind
              spec.observation =
            PMF.map (Vegas.intendedReadoutExclusion setup parameter utility excludedPayoff)
              (setup.intendedModel.runBehavioral intended.strategy
                (setup.program.instructionCount + 1)) := by
  exact @Vegas.ClientSpec.compile_correct
    Player inst inst_1 L inst_2 setup runtime leaks bounds horizon scheduler Parameter
      parameter utility excludedPayoff spec intended _equilibrium

/-- info: 'Vegas.Paper.compile_correct' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.compile_correct

/-- The paper statement has its proof in
`Vegas.ClientCompilation.clients_sequentiallyRational`. -/
theorem Vegas.Paper.clients_sequentiallyRational
    {Player : Type}
    [inst : DecidableEq Player]
    [inst_1 : Fintype Player]
    {L : Vegas.IExpr}
    [inst_2 : L.ResultTypes]
    {setup : Vegas.SourceProgram.Setup (Player := Player) (L := L)}
    {runtime : Vegas.EventGraphRuntime (Vegas.graph setup)}
    {leaks :
        Interaction.MessageNetwork.ObservationRule Player
          (Vegas.EventGraphRuntime.WitnessedPacket (Vegas.graph setup))}
    {bounds : Vegas.EventGraphRuntime.MessageBounds (Vegas.graph setup)}
    {horizon : ℕ}
    {scheduler : (Vegas.application setup runtime leaks).Scheduler}
    {Parameter : Type}
    {parameter : Vegas.State L setup.context → Parameter}
    {utility : Parameter × setup.program.PublicOutcome → Player → ℝ}
    {excludedPayoff : Player → ℝ}
    {spec : Vegas.ClientSpec setup runtime leaks bounds horizon scheduler parameter utility
      excludedPayoff}
    {intended : setup.intendedModel.BehavioralAssessment}
    (compiled : Vegas.ClientCompilation spec intended)
    (who : Player)
    (site : ((bounds.rawMenu runtime leaks).information (Vegas.initialLaw setup) horizon
      scheduler).InformationSite who)
    (alternative : (Vegas.application setup runtime leaks).Policy)
    (covered : (bounds.rawMenu runtime leaks).Admissible (Vegas.initialLaw setup) horizon
      scheduler who alternative) :
    GameTheory.Math.Probability.expect
          ((compiled.assessment.belief who site).bind
            fun
              (history :
                ((bounds.rawMenu runtime leaks).information (Vegas.initialLaw setup) horizon
                  scheduler).InformationHistory
                  who
                  (site.1 :
                    ((bounds.rawMenu runtime leaks).information (Vegas.initialLaw setup)
                      horizon scheduler).InfoState
                      who)) =>
            (Vegas.application setup runtime leaks).finish (Vegas.initialLaw setup) horizon
              scheduler
              (Function.update compiled.clients who alternative)
              (↑history :
                  ((bounds.rawMenu runtime leaks).protocol (Vegas.initialLaw setup) horizon
                    scheduler).History).state)
          (spec.payoff who) ≤
        GameTheory.Math.Probability.expect
          ((compiled.assessment.belief who site).bind
            fun
              (history :
                ((bounds.rawMenu runtime leaks).information (Vegas.initialLaw setup) horizon
                  scheduler).InformationHistory
                  who
                  (site.1 :
                    ((bounds.rawMenu runtime leaks).information (Vegas.initialLaw setup)
                      horizon scheduler).InfoState
                      who)) =>
            (Vegas.application setup runtime leaks).finish (Vegas.initialLaw setup) horizon
              scheduler compiled.clients
              (↑history :
                  ((bounds.rawMenu runtime leaks).protocol (Vegas.initialLaw setup) horizon
                    scheduler).History).state)
          (spec.payoff who) := by
  exact @Vegas.ClientCompilation.clients_sequentiallyRational
    Player inst inst_1 L inst_2 setup runtime leaks bounds horizon scheduler Parameter
      parameter utility excludedPayoff spec intended compiled who site alternative covered

/-- info: 'Vegas.Paper.clients_sequentiallyRational' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.clients_sequentiallyRational

/-- The paper statement has its proof in
`Vegas.ClientSpec.compile_ledger_correct`. -/
theorem Vegas.Paper.compile_ledger_correct
    {Player : Type}
    [inst : DecidableEq Player]
    [inst_1 : Fintype Player]
    {L : Vegas.IExpr}
    [inst_2 : L.ResultTypes]
    {setup : Vegas.SourceProgram.Setup (Player := Player) (L := L)}
    {runtime : Vegas.EventGraphRuntime (Vegas.graph setup)}
    {leaks :
        Interaction.MessageNetwork.ObservationRule Player
          (Vegas.EventGraphRuntime.WitnessedPacket (Vegas.graph setup))}
    {bounds : Vegas.EventGraphRuntime.MessageBounds (Vegas.graph setup)}
    {horizon : ℕ}
    {scheduler : (Vegas.application setup runtime leaks).Scheduler}
    {Parameter : Type}
    {parameter : Vegas.State L setup.context → Parameter}
    {utility : Parameter × setup.program.PublicOutcome → Player → ℝ}
    {excludedPayoff : Player → ℝ}
    (spec : Vegas.ClientSpec setup runtime leaks bounds horizon scheduler parameter utility
      excludedPayoff)
    (intended : setup.intendedModel.BehavioralAssessment)
    (_equilibrium : setup.IntendedSequentialEquilibrium parameter utility intended)
    (unobserved : leaks.DeliversNothing) :
    have compiled := spec.compile intended _equilibrium;
      (compiled.assessment.IsSequentialEquilibriumFor
          (Interaction.ReactiveApplication.ResponseMenu.decisionInformationAntichain
            (bounds.rawMenu runtime leaks)
            (Vegas.initialLaw setup) horizon scheduler)
          fun (who : Player)
            (site :
              ((bounds.rawMenu runtime leaks).information (Vegas.initialLaw setup) horizon
                scheduler).InformationSite
                who) =>
          compiled.assessment.truncatedContinuationContext site
            (fun (final : ((bounds.rawMenu runtime leaks).protocol (Vegas.initialLaw setup)
              horizon scheduler).History) =>
              spec.payoff who final.state)
            (2 * horizon + 1)) ∧
        (∀ (who : Player),
            Interaction.ReactiveApplication.Policy.UsesLedgerOnly (Vegas.application setup
              runtime leaks)
              (compiled.ledgerClients who)) ∧
          (∀ (history : ((bounds.rawMenu runtime leaks).protocol (Vegas.initialLaw setup)
            horizon scheduler).History)
              (who : Player),
              (bounds.rawMenu runtime leaks).restrictPolicy (Vegas.initialLaw setup) horizon
                scheduler who
                  (compiled.ledgerClients who)
                  (((bounds.rawMenu runtime leaks).information (Vegas.initialLaw setup) horizon
                    scheduler).infoOf who
                    history.trace) =
                compiled.assessment.strategy who
                  (((bounds.rawMenu runtime leaks).information (Vegas.initialLaw setup) horizon
                    scheduler).infoOf who
                    history.trace)) ∧
            ((Vegas.application setup runtime leaks).finish (Vegas.initialLaw setup) horizon
              scheduler
                    compiled.ledgerClients none).bind
                spec.observation =
              PMF.map (Vegas.intendedReadoutExclusion setup parameter utility excludedPayoff)
                (setup.intendedModel.runBehavioral intended.strategy
                  (setup.program.instructionCount + 1)) := by
  exact @Vegas.ClientSpec.compile_ledger_correct
    Player inst inst_1 L inst_2 setup runtime leaks bounds horizon scheduler Parameter
      parameter utility excludedPayoff spec intended _equilibrium unobserved

/-- info: 'Vegas.Paper.compile_ledger_correct' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.compile_ledger_correct

/-- The paper statement has its proof in
`Vegas.ClientCompilation.ledgerClients_sequentiallyRational`. -/
theorem Vegas.Paper.ledgerClients_sequentiallyRational
    {Player : Type}
    [inst : DecidableEq Player]
    [inst_1 : Fintype Player]
    {L : Vegas.IExpr}
    [inst_2 : L.ResultTypes]
    {setup : Vegas.SourceProgram.Setup (Player := Player) (L := L)}
    {runtime : Vegas.EventGraphRuntime (Vegas.graph setup)}
    {leaks :
        Interaction.MessageNetwork.ObservationRule Player
          (Vegas.EventGraphRuntime.WitnessedPacket (Vegas.graph setup))}
    {bounds : Vegas.EventGraphRuntime.MessageBounds (Vegas.graph setup)}
    {horizon : ℕ}
    {scheduler : (Vegas.application setup runtime leaks).Scheduler}
    {Parameter : Type}
    {parameter : Vegas.State L setup.context → Parameter}
    {utility : Parameter × setup.program.PublicOutcome → Player → ℝ}
    {excludedPayoff : Player → ℝ}
    {spec : Vegas.ClientSpec setup runtime leaks bounds horizon scheduler parameter utility
      excludedPayoff}
    {intended : setup.intendedModel.BehavioralAssessment}
    (compiled : Vegas.ClientCompilation spec intended)
    (unobserved : leaks.DeliversNothing)
    (who : Player)
    (site : ((bounds.rawMenu runtime leaks).information (Vegas.initialLaw setup) horizon
      scheduler).InformationSite who)
    (alternative : (Vegas.application setup runtime leaks).Policy)
    (covered : (bounds.rawMenu runtime leaks).Admissible (Vegas.initialLaw setup) horizon
      scheduler who alternative) :
    GameTheory.Math.Probability.expect
          ((compiled.assessment.belief who site).bind
            fun
              (history :
                ((bounds.rawMenu runtime leaks).information (Vegas.initialLaw setup) horizon
                  scheduler).InformationHistory
                  who
                  (site.1 :
                    ((bounds.rawMenu runtime leaks).information (Vegas.initialLaw setup)
                      horizon scheduler).InfoState
                      who)) =>
            (Vegas.application setup runtime leaks).finish (Vegas.initialLaw setup) horizon
              scheduler
              (Function.update compiled.ledgerClients who alternative)
              (↑history :
                  ((bounds.rawMenu runtime leaks).protocol (Vegas.initialLaw setup) horizon
                    scheduler).History).state)
          (spec.payoff who) ≤
        GameTheory.Math.Probability.expect
          ((compiled.assessment.belief who site).bind
            fun
              (history :
                ((bounds.rawMenu runtime leaks).information (Vegas.initialLaw setup) horizon
                  scheduler).InformationHistory
                  who
                  (site.1 :
                    ((bounds.rawMenu runtime leaks).information (Vegas.initialLaw setup)
                      horizon scheduler).InfoState
                      who)) =>
            (Vegas.application setup runtime leaks).finish (Vegas.initialLaw setup) horizon
              scheduler compiled.ledgerClients
              (↑history :
                  ((bounds.rawMenu runtime leaks).protocol (Vegas.initialLaw setup) horizon
                    scheduler).History).state)
          (spec.payoff who) := by
  exact @Vegas.ClientCompilation.ledgerClients_sequentiallyRational
    Player inst inst_1 L inst_2 setup runtime leaks bounds horizon scheduler Parameter
      parameter utility excludedPayoff spec intended compiled unobserved who site alternative
        covered

/-- info: 'Vegas.Paper.ledgerClients_sequentiallyRational' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.ledgerClients_sequentiallyRational

/-- The paper statement has its proof in
`Vegas.ClientSpec.intended_outcomeLaws_subset`. -/
theorem Vegas.Paper.intended_outcomeLaws_subset
    {Player : Type}
    [inst : DecidableEq Player]
    [inst_1 : Fintype Player]
    {L : Vegas.IExpr}
    [inst_2 : L.ResultTypes]
    {setup : Vegas.SourceProgram.Setup (Player := Player) (L := L)}
    {runtime : Vegas.EventGraphRuntime (Vegas.graph setup)}
    {leaks :
        Interaction.MessageNetwork.ObservationRule Player
          (Vegas.EventGraphRuntime.WitnessedPacket (Vegas.graph setup))}
    {bounds : Vegas.EventGraphRuntime.MessageBounds (Vegas.graph setup)}
    {horizon : ℕ}
    {scheduler : (Vegas.application setup runtime leaks).Scheduler}
    {Parameter : Type}
    {parameter : Vegas.State L setup.context → Parameter}
    {utility : Parameter × setup.program.PublicOutcome → Player → ℝ}
    {excludedPayoff : Player → ℝ}
    (spec : Vegas.ClientSpec setup runtime leaks bounds horizon scheduler parameter utility
      excludedPayoff) :
    {law : PMF (Option (Vegas.SourceProgram.Config Player L setup.program.terminalCtx) ×
      (Player → ℝ)) |
          ∃ (intended : setup.intendedModel.BehavioralAssessment),
            setup.IntendedSequentialEquilibrium parameter utility intended ∧
              PMF.map (Vegas.intendedReadoutExclusion setup parameter utility excludedPayoff)
                  (setup.intendedModel.runBehavioral intended.strategy
                    (setup.program.instructionCount + 1)) =
                law} ⊆
        {law : PMF (Option (Vegas.SourceProgram.Config Player L setup.program.terminalCtx) ×
          (Player → ℝ)) |
          ∃ (target :
            ((bounds.rawMenu runtime leaks).information (Vegas.initialLaw setup) horizon
              scheduler).BehavioralAssessment),
            (target.IsSequentialEquilibriumFor
                (Interaction.ReactiveApplication.ResponseMenu.decisionInformationAntichain
                  (bounds.rawMenu runtime leaks)
                  (Vegas.initialLaw setup) horizon scheduler)
                fun (who : Player)
                  (site :
                    ((bounds.rawMenu runtime leaks).information (Vegas.initialLaw setup)
                      horizon scheduler).InformationSite
                      who) =>
                target.truncatedContinuationContext site
                  (fun
                      (final :
                        ((bounds.rawMenu runtime leaks).protocol (Vegas.initialLaw setup)
                          horizon scheduler).History) =>
                    spec.payoff who final.state)
                  (2 * horizon + 1)) ∧
              (∀
                  final ∈
                    (((bounds.rawMenu runtime leaks).information (Vegas.initialLaw setup)
                      horizon scheduler).runBehavioral
                        target.strategy (2 * horizon + 1)).support,
                  ∀ (control : (runtime.reactiveApplication leaks).Control),
                    final.state = some control → control.execution.application.config.defaulted
                      = ∅) ∧
                (∀
                    final ∈
                      (((bounds.rawMenu runtime leaks).information (Vegas.initialLaw setup)
                        horizon scheduler).runBehavioral
                          target.strategy (2 * horizon + 1)).support,
                    ∀ (who : Player),
                      GameTheory.Enforcement.TerminalAudit.charge (Vegas.application setup
                        runtime leaks).stateTraffic
                          (runtime.countAudit leaks spec.evidenceService.sample) final.state who =
                        0) ∧
                  ((((bounds.rawMenu runtime leaks).information (Vegas.initialLaw setup)
                    horizon scheduler).runBehavioral
                          target.strategy (2 * horizon + 1)).bind
                      fun
                        (final :
                          ((bounds.rawMenu runtime leaks).protocol (Vegas.initialLaw setup)
                            horizon scheduler).History) =>
                      spec.observation final.state) =
                    law} := by
  exact @Vegas.ClientSpec.intended_outcomeLaws_subset
    Player inst inst_1 L inst_2 setup runtime leaks bounds horizon scheduler Parameter
      parameter utility excludedPayoff spec

/-- info: 'Vegas.Paper.intended_outcomeLaws_subset' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.intended_outcomeLaws_subset

/-- The paper statement has its proof in
`Vegas.ClientCompilation.clients_postprocessLaw`. -/
theorem Vegas.Paper.clients_postprocessLaw
    {Player : Type}
    [inst : DecidableEq Player]
    [inst_1 : Fintype Player]
    {L : Vegas.IExpr}
    [inst_2 : L.ResultTypes]
    {setup : Vegas.SourceProgram.Setup (Player := Player) (L := L)}
    {runtime : Vegas.EventGraphRuntime (Vegas.graph setup)}
    {leaks :
        Interaction.MessageNetwork.ObservationRule Player
          (Vegas.EventGraphRuntime.WitnessedPacket (Vegas.graph setup))}
    {bounds : Vegas.EventGraphRuntime.MessageBounds (Vegas.graph setup)}
    {horizon : ℕ}
    {scheduler : (Vegas.application setup runtime leaks).Scheduler}
    {Parameter : Type}
    {parameter : Vegas.State L setup.context → Parameter}
    {utility : Parameter × setup.program.PublicOutcome → Player → ℝ}
    {excludedPayoff : Player → ℝ}
    {spec : Vegas.ClientSpec setup runtime leaks bounds horizon scheduler parameter utility
      excludedPayoff}
    {intended : setup.intendedModel.BehavioralAssessment}
    (compiled : Vegas.ClientCompilation spec intended)
    {Result : Type}
    (read : Option (Vegas.SourceProgram.Config Player L setup.program.terminalCtx) × (Player →
      ℝ) → PMF Result) :
    (((Vegas.application setup runtime leaks).finish (Vegas.initialLaw setup) horizon scheduler
      compiled.clients
              none).bind
          fun (state : (Vegas.application setup runtime leaks).ProtocolState) =>
            (spec.observation state).bind read) =
        (setup.intendedModel.runBehavioral intended.strategy (setup.program.instructionCount +
          1)).bind
          fun (final : setup.intendedProtocol.History) =>
          read (Vegas.intendedReadoutExclusion setup parameter utility excludedPayoff final) := by
  exact @Vegas.ClientCompilation.clients_postprocessLaw
    Player inst inst_1 L inst_2 setup runtime leaks bounds horizon scheduler Parameter
      parameter utility excludedPayoff spec intended compiled Result read

/-- info: 'Vegas.Paper.clients_postprocessLaw' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.clients_postprocessLaw

/-- The paper statement has its proof in
`Vegas.intended_onePacket_sequentialEquilibrium_preserved`. -/
theorem Vegas.Paper.intended_onePacket_sequentialEquilibrium_preserved
    {Player : Type}
    [inst : DecidableEq Player]
    [inst_1 : Fintype Player]
    {L : Vegas.IExpr}
    [inst_2 : L.ResultTypes]
    {setup : Vegas.SourceProgram.Setup (Player := Player) (L := L)}
    {runtime : Vegas.EventGraphRuntime (Vegas.graph setup)}
    {leaks :
        Interaction.MessageNetwork.ObservationRule Player
          (Vegas.EventGraphRuntime.WitnessedPacket (Vegas.graph setup))}
    {bounds : Vegas.EventGraphRuntime.MessageBounds (Vegas.graph setup)}
    {horizon : ℕ}
    {scheduler : (Vegas.application setup runtime leaks).Scheduler}
    [_instance11 : (Vegas.application setup runtime leaks).FiniteNature (Vegas.initialLaw
      setup) scheduler]
    [_instance12 : Finite setup.intendedProtocol.History]
    {Public : Type u_1}
    {signal : Vegas.State L setup.context → Public}
    {Parameter : Type}
    (parameter : Vegas.State L setup.context → Parameter)
    (utility : Parameter × setup.program.PublicOutcome → Player → ℝ)
    (excludedPayoff : Player → ℝ)
    (wellFormed : setup.WellFormed)
    (independent : setup.PrivateInputsIndependentGiven signal)
    (observable : setup.PublicInitialSignal signal)
    {delay bound : (Vegas.graph setup).EventId → ℕ}
    (opportunity : runtime.Opportunity leaks (Vegas.initialLaw setup) horizon scheduler delay)
    (inclusion : runtime.ProtectedInclusion leaks (Vegas.initialLaw setup) horizon scheduler bound)
    (completes : runtime.CompletesPlay leaks (Vegas.initialLaw setup) horizon scheduler)
    (timely : runtime.AsyncTimely delay bound)
    (below :
        ∀ (final : setup.intendedProtocol.History)
          (terminal : Vegas.SourceProgram.Config Player L setup.program.terminalCtx),
          setup.protocolReadout final.state = some terminal →
            ∀ (who : Player), excludedPayoff who ≤ utility (setup.parameterOutcome parameter
              terminal) who)
    (intended : setup.intendedModel.BehavioralAssessment)
    (_equilibrium : setup.IntendedSequentialEquilibrium parameter utility intended)
    (covers : bounds.CoversOutputValues)
    (coversInputs : bounds.CoversInputValues)
    (capacity : ∀ (who : Player), Vegas.bindingEventCount (Vegas.graph setup) who <
      bounds.candidateCount) :
    ∃ (native :
        (Vegas.onePacketModel setup runtime leaks bounds (Vegas.initialLaw setup) horizon
          scheduler).BehavioralAssessment),
        (native.IsSequentialEquilibriumFor
            (Interaction.ReactiveApplication.ResponseMenu.decisionInformationAntichain
              (Vegas.EventGraphRuntime.MessageBounds.onePacketMenu runtime leaks bounds)
                (Vegas.initialLaw setup) horizon
              scheduler)
            fun (who : Player)
              (site :
                (Vegas.onePacketModel setup runtime leaks bounds (Vegas.initialLaw setup)
                  horizon scheduler).InformationSite
                  who) =>
            native.truncatedContinuationContext site
              (fun
                  (final :
                    ((Vegas.EventGraphRuntime.MessageBounds.onePacketMenu runtime leaks
                      bounds).protocol
                        (Vegas.initialLaw setup) horizon scheduler).History) =>
                Vegas.exclusionBase setup runtime parameter utility excludedPayoff leaks
                  final.state who)
              (2 * horizon + 1)) ∧
          (∀
              final ∈
                ((Vegas.onePacketModel setup runtime leaks bounds (Vegas.initialLaw setup)
                  horizon scheduler).runBehavioral
                    native.strategy (2 * horizon + 1)).support,
              ∀ (control : (runtime.reactiveApplication leaks).Control),
                final.state = some control → control.execution.application.config.defaulted = ∅) ∧
            PMF.map
                (Vegas.readoutExclusion setup runtime leaks bounds (Vegas.initialLaw setup)
                  horizon scheduler parameter
                  utility excludedPayoff)
                ((Vegas.onePacketModel setup runtime leaks bounds (Vegas.initialLaw setup)
                  horizon scheduler).runBehavioral
                  native.strategy (2 * horizon + 1)) =
              PMF.map (Vegas.intendedReadoutExclusion setup parameter utility excludedPayoff)
                (setup.intendedModel.runBehavioral intended.strategy
                  (setup.program.instructionCount + 1)) := by
  exact @Vegas.intended_onePacket_sequentialEquilibrium_preserved
    Player inst inst_1 L inst_2 setup runtime leaks bounds horizon scheduler _instance11
      _instance12 Public signal Parameter parameter utility excludedPayoff wellFormed
        independent observable delay bound opportunity inclusion completes timely below
          intended _equilibrium covers coversInputs capacity

/-- info: 'Vegas.Paper.intended_onePacket_sequentialEquilibrium_preserved' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.intended_onePacket_sequentialEquilibrium_preserved

/-- The paper statement has its proof in
`Vegas.rosterScheduler_asyncContract`. -/
theorem Vegas.Paper.rosterScheduler_asyncContract
    {Player : Type}
    [inst : DecidableEq Player]
    {L : Vegas.IExpr}
    [inst_1 : L.ResultTypes]
    (setup : Vegas.SourceProgram.Setup (Player := Player) (L := L))
    (leaks :
        Interaction.MessageNetwork.ObservationRule Player
          (Vegas.EventGraphRuntime.WitnessedPacket (Vegas.graph setup)))
    (rosters : (Vegas.graph setup).EventId → List Player)
    (network : (Vegas.runtime setup).NetworkPolicy leaks)
    (opportunities : Vegas.ActorOpportunities setup rosters) :
    (Vegas.runtime setup).AsyncContract leaks (Vegas.initialLaw setup) (Vegas.rosterPlan setup
      rosters).length
        (Vegas.rosterScheduler setup leaks rosters network) (fun (event : (Vegas.graph
          setup).EventId) => (↑event : ℕ))
        fun (_x : (Vegas.graph setup).EventId) => 0 := by
  exact @Vegas.rosterScheduler_asyncContract
    Player inst L inst_1 setup leaks rosters network opportunities

/-- info: 'Vegas.Paper.rosterScheduler_asyncContract' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.rosterScheduler_asyncContract

/-- The paper statement has its proof in
`Vegas.rosterScheduler_asyncTimely`. -/
theorem Vegas.Paper.rosterScheduler_asyncTimely
    {Player : Type}
    [inst : DecidableEq Player]
    {L : Vegas.IExpr}
    [inst_1 : L.ResultTypes]
    (setup : Vegas.SourceProgram.Setup (Player := Player) (L := L)) :
    (Vegas.runtime setup).AsyncTimely (fun (event : (Vegas.graph setup).EventId) => (↑event : ℕ))
        fun (_x : (Vegas.graph setup).EventId) => 0 := by
  exact @Vegas.rosterScheduler_asyncTimely
    Player inst L inst_1 setup

/-- info: 'Vegas.Paper.rosterScheduler_asyncTimely' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.rosterScheduler_asyncTimely

/-- The paper statement has its proof in
`Vegas.Examples.OddsEvensRaw.intended_equilibrium_preserved`. -/
theorem Vegas.Paper.intended_equilibrium_preserved :
    ∀
      (intended : Vegas.Examples.OddsEvensService.fixture.intendedModel.BehavioralAssessment)
      (_equilibrium :
        Vegas.Examples.OddsEvensService.fixture.IntendedSequentialEquilibrium
          (fun (_x : Vegas.State Vegas.simpleExpr
            Vegas.Examples.OddsEvensService.fixture.context) => ())
          Vegas.Examples.OddsEvens.sourceUtility intended),
      have raw :=
        Vegas.Examples.OddsEvens.bounds.rawMenu Vegas.Examples.OddsEvensService.runtime
          Vegas.Examples.OddsEvensService.leaks;
      have observe := Vegas.Examples.OddsEvensService.app.stateTraffic;
      have audit :=
        Vegas.Examples.OddsEvensService.runtime.countAudit Vegas.Examples.OddsEvensService.leaks
          Vegas.Examples.OddsEvensRaw.evidenceService.sample;
      have base :=
        Vegas.exclusionBase Vegas.Examples.OddsEvensService.fixture
          Vegas.Examples.OddsEvensService.runtime
          (fun (_x : Vegas.State Vegas.simpleExpr
            Vegas.Examples.OddsEvensService.fixture.context) => ())
          Vegas.Examples.OddsEvens.sourceUtility (fun (_x : Vegas.Examples.OddsEvens.Player) => 0)
          Vegas.Examples.OddsEvensService.leaks;
      have payoff :=
        GameTheory.Enforcement.TerminalAudit.utility base observe audit fun (_x :
          Vegas.Examples.OddsEvens.Player) => 800;
      have settle :=
        GameTheory.Enforcement.TerminalAudit.settlement base observe audit fun (_x :
          Vegas.Examples.OddsEvens.Player) => 800;
      ∃ (target :
        (raw.information Vegas.Examples.OddsEvensService.initial
          Vegas.Examples.OddsEvensService.horizon
            Vegas.Examples.OddsEvensService.scheduler).BehavioralAssessment),
        (target.IsSequentialEquilibrium
            (Interaction.ReactiveApplication.ResponseMenu.decisionInformationAntichain raw
              Vegas.Examples.OddsEvensService.initial Vegas.Examples.OddsEvensService.horizon
              Vegas.Examples.OddsEvensService.scheduler)
            (GameTheory.Protocol.ExecutionProtocol.BoundedHorizon.wellFoundedHistories
              (Interaction.ReactiveApplication.ResponseMenu.bounded raw
                Vegas.Examples.OddsEvensService.initial
                Vegas.Examples.OddsEvensService.horizon Vegas.Examples.OddsEvensService.scheduler))
            fun (who : Vegas.Examples.OddsEvens.Player)
              (final :
                (raw.protocol Vegas.Examples.OddsEvensService.initial
                  Vegas.Examples.OddsEvensService.horizon
                    Vegas.Examples.OddsEvensService.scheduler).History) =>
            payoff final.state who) ∧
          (∀
              final ∈
                ((raw.information Vegas.Examples.OddsEvensService.initial
                  Vegas.Examples.OddsEvensService.horizon
                        Vegas.Examples.OddsEvensService.scheduler).runBehavioral
                    target.strategy (2 * Vegas.Examples.OddsEvensService.horizon + 1)).support,
              ∀
                (control :
                  (Vegas.Examples.OddsEvensService.runtime.reactiveApplication
                      Vegas.Examples.OddsEvensService.leaks).Control),
                final.state = some control → control.execution.application.config.defaulted = ∅) ∧
            (∀
                final ∈
                  ((raw.information Vegas.Examples.OddsEvensService.initial
                    Vegas.Examples.OddsEvensService.horizon
                          Vegas.Examples.OddsEvensService.scheduler).runBehavioral
                      target.strategy (2 * Vegas.Examples.OddsEvensService.horizon + 1)).support,
                ∀ (who : Vegas.Examples.OddsEvens.Player),
                  GameTheory.Enforcement.TerminalAudit.charge observe audit final.state who = 0) ∧
              (((raw.information Vegas.Examples.OddsEvensService.initial
                Vegas.Examples.OddsEvensService.horizon
                          Vegas.Examples.OddsEvensService.scheduler).runBehavioral
                      target.strategy (2 * Vegas.Examples.OddsEvensService.horizon + 1)).bind
                  fun
                    (final :
                      (raw.protocol Vegas.Examples.OddsEvensService.initial
                        Vegas.Examples.OddsEvensService.horizon
                          Vegas.Examples.OddsEvensService.scheduler).History) =>
                  PMF.map
                    (fun (payoffs : Vegas.Examples.OddsEvens.Player → ℝ) =>
                      (Vegas.sourceReadout Vegas.Examples.OddsEvensService.fixture
                        Vegas.Examples.OddsEvensService.runtime
                          Vegas.Examples.OddsEvensService.leaks final.state,
                        payoffs))
                    (settle final.state)) =
                PMF.map
                  (Vegas.intendedReadoutExclusion Vegas.Examples.OddsEvensService.fixture
                    (fun (_x : Vegas.State Vegas.simpleExpr
                      Vegas.Examples.OddsEvensService.fixture.context) => ())
                    Vegas.Examples.OddsEvens.sourceUtility fun (_x :
                      Vegas.Examples.OddsEvens.Player) => 0)
                  (Vegas.Examples.OddsEvensService.fixture.intendedModel.runBehavioral
                    intended.strategy
                    (Vegas.Examples.OddsEvensService.fixture.program.instructionCount + 1)) := by
  exact @Vegas.Examples.OddsEvensRaw.intended_equilibrium_preserved

/-- info: 'Vegas.Paper.intended_equilibrium_preserved' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.intended_equilibrium_preserved

/-- The paper statement has its proof in
`Vegas.Examples.OddsEvensRaw.fair_equilibrium_exists`. -/
theorem Vegas.Paper.fair_equilibrium_exists :
    have raw :=
      Vegas.Examples.OddsEvens.bounds.rawMenu Vegas.Examples.OddsEvensService.runtime
        Vegas.Examples.OddsEvensService.leaks;
    have observe := Vegas.Examples.OddsEvensService.app.stateTraffic;
    have audit :=
      Vegas.Examples.OddsEvensService.runtime.countAudit Vegas.Examples.OddsEvensService.leaks
        Vegas.Examples.OddsEvensRaw.evidenceService.sample;
    have base :=
      Vegas.exclusionBase Vegas.Examples.OddsEvensService.fixture
        Vegas.Examples.OddsEvensService.runtime
        (fun (_x : Vegas.State Vegas.simpleExpr
          Vegas.Examples.OddsEvensService.fixture.context) => ())
        Vegas.Examples.OddsEvens.sourceUtility (fun (_x : Vegas.Examples.OddsEvens.Player) => 0)
        Vegas.Examples.OddsEvensService.leaks;
    have payoff :=
      GameTheory.Enforcement.TerminalAudit.utility base observe audit fun (_x :
        Vegas.Examples.OddsEvens.Player) => 800;
    have settle :=
      GameTheory.Enforcement.TerminalAudit.settlement base observe audit fun (_x :
        Vegas.Examples.OddsEvens.Player) => 800;
    ∃ (target :
      (raw.information Vegas.Examples.OddsEvensService.initial
        Vegas.Examples.OddsEvensService.horizon
          Vegas.Examples.OddsEvensService.scheduler).BehavioralAssessment),
      (target.IsSequentialEquilibrium
          (Interaction.ReactiveApplication.ResponseMenu.decisionInformationAntichain raw
            Vegas.Examples.OddsEvensService.initial Vegas.Examples.OddsEvensService.horizon
            Vegas.Examples.OddsEvensService.scheduler)
          (GameTheory.Protocol.ExecutionProtocol.BoundedHorizon.wellFoundedHistories
            (Interaction.ReactiveApplication.ResponseMenu.bounded raw
              Vegas.Examples.OddsEvensService.initial
              Vegas.Examples.OddsEvensService.horizon Vegas.Examples.OddsEvensService.scheduler))
          fun (who : Vegas.Examples.OddsEvens.Player)
            (final :
              (raw.protocol Vegas.Examples.OddsEvensService.initial
                Vegas.Examples.OddsEvensService.horizon
                  Vegas.Examples.OddsEvensService.scheduler).History) =>
          payoff final.state who) ∧
        (∀
            final ∈
              ((raw.information Vegas.Examples.OddsEvensService.initial
                Vegas.Examples.OddsEvensService.horizon
                      Vegas.Examples.OddsEvensService.scheduler).runBehavioral
                  target.strategy (2 * Vegas.Examples.OddsEvensService.horizon + 1)).support,
            ∀
              (control :
                (Vegas.Examples.OddsEvensService.runtime.reactiveApplication
                    Vegas.Examples.OddsEvensService.leaks).Control),
              final.state = some control → control.execution.application.config.defaulted = ∅) ∧
          (∀
              final ∈
                ((raw.information Vegas.Examples.OddsEvensService.initial
                  Vegas.Examples.OddsEvensService.horizon
                        Vegas.Examples.OddsEvensService.scheduler).runBehavioral
                    target.strategy (2 * Vegas.Examples.OddsEvensService.horizon + 1)).support,
              ∀ (who : Vegas.Examples.OddsEvens.Player),
                GameTheory.Enforcement.TerminalAudit.charge observe audit final.state who = 0) ∧
            (((raw.information Vegas.Examples.OddsEvensService.initial
              Vegas.Examples.OddsEvensService.horizon
                          Vegas.Examples.OddsEvensService.scheduler).runBehavioral
                      target.strategy (2 * Vegas.Examples.OddsEvensService.horizon + 1)).bind
                  fun
                    (final :
                      (raw.protocol Vegas.Examples.OddsEvensService.initial
                        Vegas.Examples.OddsEvensService.horizon
                          Vegas.Examples.OddsEvensService.scheduler).History) =>
                  PMF.map
                    (fun (payoffs : Vegas.Examples.OddsEvens.Player → ℝ) =>
                      (Vegas.sourceReadout Vegas.Examples.OddsEvensService.fixture
                        Vegas.Examples.OddsEvensService.runtime
                          Vegas.Examples.OddsEvensService.leaks final.state,
                        payoffs))
                    (settle final.state)) =
                Vegas.Examples.OddsEvens.uniformJointLaw ∧
              ∀ (who : Vegas.Examples.OddsEvens.Player),
                (GameTheory.Math.Probability.expect
                    (((raw.information Vegas.Examples.OddsEvensService.initial
                      Vegas.Examples.OddsEvensService.horizon
                              Vegas.Examples.OddsEvensService.scheduler).runBehavioral
                          target.strategy (2 * Vegas.Examples.OddsEvensService.horizon + 1)).bind
                      fun
                        (final :
                          (raw.protocol Vegas.Examples.OddsEvensService.initial
                            Vegas.Examples.OddsEvensService.horizon
                              Vegas.Examples.OddsEvensService.scheduler).History) =>
                      PMF.map
                        (fun (payoffs : Vegas.Examples.OddsEvens.Player → ℝ) =>
                          (Vegas.sourceReadout Vegas.Examples.OddsEvensService.fixture
                              Vegas.Examples.OddsEvensService.runtime
                                Vegas.Examples.OddsEvensService.leaks final.state,
                            payoffs))
                        (settle final.state))
                    fun
                      (realized :
                        Option
                            (Vegas.SourceProgram.Config Vegas.Examples.OddsEvens.Player
                              Vegas.simpleExpr
                              Vegas.Examples.OddsEvensService.fixture.program.terminalCtx) ×
                          (Vegas.Examples.OddsEvens.Player → ℝ)) =>
                    realized.2 who) =
                  100 := by
  exact @Vegas.Examples.OddsEvensRaw.fair_equilibrium_exists

/-- info: 'Vegas.Paper.fair_equilibrium_exists' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.fair_equilibrium_exists

/-- The paper statement has its proof in
`Vegas.Examples.OddsEvensRaw.collection_probability`. -/
theorem Vegas.Paper.collection_probability :
    ∀
      (actual : List (Vegas.EventGraphRuntime.CountEvidence
        Vegas.Examples.OddsEvensService.compiled))
      (evidence : Vegas.EventGraphRuntime.CountEvidence Vegas.Examples.OddsEvensService.compiled)
      (_member : evidence ∈ actual),
      (((Vegas.Examples.OddsEvensRaw.evidenceService.sample actual).toOuterMeasure :
              (a : Set (List (Vegas.EventGraphRuntime.CountEvidence
                Vegas.Examples.OddsEvensService.compiled))) → ENNReal)
            {collected : List (Vegas.EventGraphRuntime.CountEvidence
              Vegas.Examples.OddsEvensService.compiled) |
              evidence ∈ collected}).toReal =
        1 / 4 := by
  exact @Vegas.Examples.OddsEvensRaw.collection_probability

/-- info: 'Vegas.Paper.collection_probability' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.collection_probability

/-- The paper statement has its proof in
`Vegas.Examples.OddsEvens.fair_full_source_equilibrium_exists`. -/
theorem Vegas.Paper.fair_full_source_equilibrium_exists :
    ∃ (target :
      Vegas.Examples.OddsEvens.fullModel.BehavioralAssessment),
      target.IsSequentialEquilibrium
          (Vegas.SourceProgram.Setup.decision_antichain Vegas.Examples.OddsEvens.setup
            Vegas.Examples.OddsEvens.fullAdmission)
          (GameTheory.Protocol.ExecutionProtocol.BoundedHorizon.wellFoundedHistories
            Vegas.Examples.OddsEvens.fullBounded)
          Vegas.Examples.OddsEvens.fullPayoff ∧
        (Vegas.Examples.OddsEvens.setup.intendedRestriction
          Vegas.Examples.OddsEvens.fullAdmission).ExtendsProfile
            Vegas.Examples.OddsEvens.uniformProfile target.strategy ∧
          PMF.map
              (fun (final : Vegas.Examples.OddsEvens.fullProtocol.History) =>
                (Vegas.Examples.OddsEvens.setup.protocolReadout final.state, fun (who :
                  Vegas.Examples.OddsEvens.Player) =>
                  Vegas.Examples.OddsEvens.fullPayoff who final))
              (Vegas.Examples.OddsEvens.fullModel.runBehavioralTerminalFrom
                (GameTheory.Protocol.ExecutionProtocol.BoundedHorizon.wellFoundedHistories
                  Vegas.Examples.OddsEvens.fullBounded)
                target.strategy Vegas.Examples.OddsEvens.fullProtocol.initHistory) =
            Vegas.Examples.OddsEvens.uniformJointLaw := by
  exact @Vegas.Examples.OddsEvens.fair_full_source_equilibrium_exists

/-- info: 'Vegas.Paper.fair_full_source_equilibrium_exists' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.fair_full_source_equilibrium_exists

/-- The paper statement has its proof in
`Vegas.Examples.CommitRevealAuction.truthful_not_dominant`. -/
theorem Vegas.Paper.commitRevealAuction_truthful_not_dominant
    (values : Vegas.Examples.CommitRevealAuction.Player → ℝ)
    (forfeiture : ℝ)
    (_valuation : values Vegas.Examples.CommitRevealAuction.Player.alice = 5) :
    ¬GameTheory.IsDominant Vegas.Examples.CommitRevealAuction.setup.valueBindingGame
          (GameTheory.euPreference (Vegas.Examples.CommitRevealAuction.utility values forfeiture))
          Vegas.Examples.CommitRevealAuction.Player.alice
            (Vegas.Examples.CommitRevealAuction.aliceStrategy 5) := by
  exact @Vegas.Examples.CommitRevealAuction.truthful_not_dominant
    values forfeiture _valuation

/-- info: 'Vegas.Paper.commitRevealAuction_truthful_not_dominant' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.commitRevealAuction_truthful_not_dominant

/-- The paper statement has its proof in
`Vegas.Examples.CommitRevealAuction.translated_truthful_not_dominant`. -/
theorem Vegas.Paper.translated_truthful_not_dominant :
    ∀
      (values : Vegas.Examples.CommitRevealAuction.Player → ℝ) (forfeiture : ℝ)
      (_valuation : values Vegas.Examples.CommitRevealAuction.Player.alice = 5)
      (target : GameTheory.GameForm Vegas.Examples.CommitRevealAuction.Player)
      (compile :
        (who : Vegas.Examples.CommitRevealAuction.Player) →
          Vegas.Examples.CommitRevealAuction.setup.valueBindingGame.sig.Strategy who →
            target.sig.Strategy who)
      (targetUtility : target.sig.Outcome → Vegas.Examples.CommitRevealAuction.Player → ℝ)
      (_preserves :
        ∀ (players : GameTheory.Profile
          Vegas.Examples.CommitRevealAuction.setup.valueBindingGame.sig),
          GameTheory.expectedUtility targetUtility Vegas.Examples.CommitRevealAuction.Player.alice
              (target.play (GameTheory.Profile.map compile players)) =
            GameTheory.expectedUtility (Vegas.Examples.CommitRevealAuction.utility values
              forfeiture)
              Vegas.Examples.CommitRevealAuction.Player.alice
              (Vegas.Examples.CommitRevealAuction.setup.valueBindingGame.play players))
      (_targetIntegrable :
        ∀ (players : GameTheory.Profile
          Vegas.Examples.CommitRevealAuction.setup.valueBindingGame.sig),
          GameTheory.UtilityIntegrable targetUtility Vegas.Examples.CommitRevealAuction.Player.alice
            (target.play (GameTheory.Profile.map compile players))),
      ¬GameTheory.IsDominant target (GameTheory.euPreference targetUtility)
        Vegas.Examples.CommitRevealAuction.Player.alice
          (compile Vegas.Examples.CommitRevealAuction.Player.alice
            (Vegas.Examples.CommitRevealAuction.aliceStrategy 5)) := by
  exact @Vegas.Examples.CommitRevealAuction.translated_truthful_not_dominant

/-- info: 'Vegas.Paper.translated_truthful_not_dominant' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.translated_truthful_not_dominant

/-- The paper statement has its proof in
`Vegas.Examples.BoundedPaymentAuction.truthful_not_dominant`. -/
theorem Vegas.Paper.boundedPaymentAuction_truthful_not_dominant
    (penalty : ℤ)
    (values : Vegas.Examples.CommitRevealAuction.Player → ℝ)
    (valueAlice : values Vegas.Examples.CommitRevealAuction.Player.alice = 5) :
    ¬GameTheory.IsDominant (Vegas.Examples.BoundedPaymentAuction.setup penalty).gameForm
          (GameTheory.euPreference
            ((Vegas.Examples.BoundedPaymentAuction.program penalty).paymentUtility
              (Vegas.Examples.BoundedPaymentAuction.valuation penalty values)))
          Vegas.Examples.CommitRevealAuction.Player.alice
          (Vegas.Examples.BoundedPaymentAuction.alicePolicy penalty
            (⟨5, by decide⟩ : Vegas.Examples.BoundedPaymentAuction.Bid)) := by
  exact @Vegas.Examples.BoundedPaymentAuction.truthful_not_dominant
    penalty values valueAlice

/-- info: 'Vegas.Paper.boundedPaymentAuction_truthful_not_dominant' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.boundedPaymentAuction_truthful_not_dominant

/-- The paper statement has its proof in
`Vegas.Examples.OddsEvens.uniformAssessment_equilibrium`. -/
theorem Vegas.Paper.uniformAssessment_equilibrium :
    Vegas.Examples.OddsEvens.uniformAssessment.IsSequentialEquilibrium
      (Vegas.SourceProgram.Setup.intended_decision_antichain Vegas.Examples.OddsEvens.setup)
      (GameTheory.Protocol.ExecutionProtocol.BoundedHorizon.wellFoundedHistories
        (Vegas.SourceProgram.Setup.intended_bounded Vegas.Examples.OddsEvens.setup))
      Vegas.Examples.OddsEvens.terminalUtility := by
  exact @Vegas.Examples.OddsEvens.uniformAssessment_equilibrium

/-- info: 'Vegas.Paper.uniformAssessment_equilibrium' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.uniformAssessment_equilibrium

/-- The paper statement has its proof in
`Vegas.Examples.OddsEvens.uniformJointLaw_expected`. -/
theorem Vegas.Paper.uniformJointLaw_expected
    (who : Vegas.Examples.OddsEvens.Player) :
    (GameTheory.Math.Probability.expect Vegas.Examples.OddsEvens.uniformJointLaw
          fun
            (realized :
              Option
                  (Vegas.SourceProgram.Config Vegas.Examples.OddsEvens.Player Vegas.simpleExpr
                    Vegas.Examples.OddsEvens.program.terminalCtx) ×
                (Vegas.Examples.OddsEvens.Player → ℝ)) =>
          realized.2 who) =
        100 := by
  exact @Vegas.Examples.OddsEvens.uniformJointLaw_expected
    who

/-- info: 'Vegas.Paper.uniformJointLaw_expected' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.uniformJointLaw_expected

/-- The paper statement has its proof in
`Vegas.lateLeak_intended_outcome_not_preserved`. -/
theorem Vegas.Paper.lateLeak_intended_outcome_not_preserved
    (G : Vegas.LateLeakParameters)
    (pays : G.DeferralPays) :
    (∃ (A : (Vegas.lateLeakModel G false).BehavioralAssessment),
          A.IsSequentialEquilibrium (Vegas.lateLeak_antichain G false)
            (Vegas.lateLeak_terminates G false)
            (Vegas.lateLeakPayoff G false)) ∧
        (∀ (A : (Vegas.lateLeakModel G false).BehavioralAssessment),
            A.IsSequentialEquilibrium (Vegas.lateLeak_antichain G false)
              (Vegas.lateLeak_terminates G false)
                (Vegas.lateLeakPayoff G false) →
              Vegas.lateLeakOutcomeLaw G false A.strategy = Vegas.lateLeakIntendedOutcome) ∧
          (∃ (A : (Vegas.lateLeakModel G true).BehavioralAssessment),
              A.IsSequentialEquilibrium (Vegas.lateLeak_antichain G true)
                (Vegas.lateLeak_terminates G true)
                (Vegas.lateLeakPayoff G true)) ∧
            ∀ (A : (Vegas.lateLeakModel G true).BehavioralAssessment),
              A.IsSequentialEquilibrium (Vegas.lateLeak_antichain G true)
                (Vegas.lateLeak_terminates G true)
                  (Vegas.lateLeakPayoff G true) →
                Vegas.lateLeakOutcomeLaw G true A.strategy ≠ Vegas.lateLeakIntendedOutcome := by
  exact @Vegas.lateLeak_intended_outcome_not_preserved
    G pays

/-- info: 'Vegas.Paper.lateLeak_intended_outcome_not_preserved' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.lateLeak_intended_outcome_not_preserved

/-- The paper statement has its proof in
`Vegas.lateLeak_not_preserved_for_every_margin`. -/
theorem Vegas.Paper.lateLeak_not_preserved_for_every_margin
    (R D c : ℝ)
    (reward_pos : 0 < R)
    (margin : R < D)
    (charge : 0 ≤ c) :
    Vegas.lateLeakInclusionThreshold R D c < 1 ∧
        ∀ (q : (↑(Set.Ioo 0 1) : Type)),
          Vegas.lateLeakInclusionThreshold R D c < (↑q : ℝ) →
            (∃ (A :
                (Vegas.lateLeakModel (⟨R, D, c, q⟩ : Vegas.LateLeakParameters)
                    false).BehavioralAssessment),
                A.IsSequentialEquilibrium
                  (Vegas.lateLeak_antichain (⟨R, D, c, q⟩ : Vegas.LateLeakParameters) false)
                  (Vegas.lateLeak_terminates (⟨R, D, c, q⟩ : Vegas.LateLeakParameters) false)
                  (Vegas.lateLeakPayoff (⟨R, D, c, q⟩ : Vegas.LateLeakParameters) false)) ∧
              (∀
                  (A :
                    (Vegas.lateLeakModel (⟨R, D, c, q⟩ : Vegas.LateLeakParameters)
                        false).BehavioralAssessment),
                  A.IsSequentialEquilibrium
                      (Vegas.lateLeak_antichain (⟨R, D, c, q⟩ : Vegas.LateLeakParameters) false)
                      (Vegas.lateLeak_terminates (⟨R, D, c, q⟩ : Vegas.LateLeakParameters) false)
                      (Vegas.lateLeakPayoff (⟨R, D, c, q⟩ : Vegas.LateLeakParameters) false) →
                    Vegas.lateLeakOutcomeLaw (⟨R, D, c, q⟩ : Vegas.LateLeakParameters) false
                        A.strategy =
                      Vegas.lateLeakIntendedOutcome) ∧
                (∃ (A :
                    (Vegas.lateLeakModel (⟨R, D, c, q⟩ : Vegas.LateLeakParameters)
                        true).BehavioralAssessment),
                    A.IsSequentialEquilibrium
                      (Vegas.lateLeak_antichain (⟨R, D, c, q⟩ : Vegas.LateLeakParameters) true)
                      (Vegas.lateLeak_terminates (⟨R, D, c, q⟩ : Vegas.LateLeakParameters) true)
                      (Vegas.lateLeakPayoff (⟨R, D, c, q⟩ : Vegas.LateLeakParameters) true)) ∧
                  ∀
                    (A :
                      (Vegas.lateLeakModel (⟨R, D, c, q⟩ : Vegas.LateLeakParameters)
                          true).BehavioralAssessment),
                    A.IsSequentialEquilibrium
                        (Vegas.lateLeak_antichain (⟨R, D, c, q⟩ : Vegas.LateLeakParameters) true)
                        (Vegas.lateLeak_terminates (⟨R, D, c, q⟩ : Vegas.LateLeakParameters) true)
                        (Vegas.lateLeakPayoff (⟨R, D, c, q⟩ : Vegas.LateLeakParameters) true) →
                      Vegas.lateLeakOutcomeLaw (⟨R, D, c, q⟩ : Vegas.LateLeakParameters) true
                          A.strategy ≠
                        Vegas.lateLeakIntendedOutcome := by
  exact @Vegas.lateLeak_not_preserved_for_every_margin
    R D c reward_pos margin charge

/-- info: 'Vegas.Paper.lateLeak_not_preserved_for_every_margin' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.lateLeak_not_preserved_for_every_margin

/-- The paper statement has its proof in
`Vegas.settleLate_not_preserved_for_every_margin`. -/
theorem Vegas.Paper.settleLate_not_preserved_for_every_margin
    (R D c : ℝ)
    (reward_pos : 0 < R)
    (margin : R < D)
    (charge : R / 2 < c)
    (leak : (↑(Set.Ioo 0 1) : Type))
    (packetCost : ℝ) :
    Vegas.settleLateInclusionThreshold R D c (↑leak : ℝ) < 1 ∧
        ∀ (q : (↑(Set.Ioo 0 1) : Type)),
          Vegas.settleLateInclusionThreshold R D c (↑leak : ℝ) < (↑q : ℝ) →
            (∃ (A :
                (Vegas.settleLateModel
                    { reward := R, forfeit := D, dropCharge := c, inclusion := q, leak := leak,
                      packetCost := packetCost }
                    false).BehavioralAssessment),
                A.IsSequentialEquilibrium
                  (Vegas.settleLate_antichain
                    { reward := R, forfeit := D, dropCharge := c, inclusion := q, leak := leak,
                      packetCost := packetCost }
                    false)
                  (Vegas.settleLate_terminates
                    { reward := R, forfeit := D, dropCharge := c, inclusion := q, leak := leak,
                      packetCost := packetCost }
                    false)
                  (Vegas.settleLatePayoff
                    { reward := R, forfeit := D, dropCharge := c, inclusion := q, leak := leak,
                      packetCost := packetCost }
                    false)) ∧
              (∀
                  (A :
                    (Vegas.settleLateModel
                        { reward := R, forfeit := D, dropCharge := c, inclusion := q, leak := leak,
                          packetCost := packetCost }
                        false).BehavioralAssessment),
                  A.IsSequentialEquilibrium
                      (Vegas.settleLate_antichain
                        { reward := R, forfeit := D, dropCharge := c, inclusion := q, leak := leak,
                          packetCost := packetCost }
                        false)
                      (Vegas.settleLate_terminates
                        { reward := R, forfeit := D, dropCharge := c, inclusion := q, leak := leak,
                          packetCost := packetCost }
                        false)
                      (Vegas.settleLatePayoff
                        { reward := R, forfeit := D, dropCharge := c, inclusion := q, leak := leak,
                          packetCost := packetCost }
                        false) →
                    Vegas.settleLateOutcomeLaw
                        { reward := R, forfeit := D, dropCharge := c, inclusion := q, leak := leak,
                          packetCost := packetCost }
                        false A.strategy =
                      Vegas.settleLateIntendedOutcome) ∧
                (∃ (A :
                    (Vegas.settleLateModel
                        { reward := R, forfeit := D, dropCharge := c, inclusion := q, leak := leak,
                          packetCost := packetCost }
                        true).BehavioralAssessment),
                    A.IsSequentialEquilibrium
                      (Vegas.settleLate_antichain
                        { reward := R, forfeit := D, dropCharge := c, inclusion := q, leak := leak,
                          packetCost := packetCost }
                        true)
                      (Vegas.settleLate_terminates
                        { reward := R, forfeit := D, dropCharge := c, inclusion := q, leak := leak,
                          packetCost := packetCost }
                        true)
                      (Vegas.settleLatePayoff
                        { reward := R, forfeit := D, dropCharge := c, inclusion := q, leak := leak,
                          packetCost := packetCost }
                        true)) ∧
                  ∀
                    (A :
                      (Vegas.settleLateModel
                          { reward := R, forfeit := D, dropCharge := c, inclusion := q, leak :=
                            leak,
                            packetCost := packetCost }
                          true).BehavioralAssessment),
                    A.IsSequentialEquilibrium
                        (Vegas.settleLate_antichain
                          { reward := R, forfeit := D, dropCharge := c, inclusion := q, leak :=
                            leak,
                            packetCost := packetCost }
                          true)
                        (Vegas.settleLate_terminates
                          { reward := R, forfeit := D, dropCharge := c, inclusion := q, leak :=
                            leak,
                            packetCost := packetCost }
                          true)
                        (Vegas.settleLatePayoff
                          { reward := R, forfeit := D, dropCharge := c, inclusion := q, leak :=
                            leak,
                            packetCost := packetCost }
                          true) →
                      Vegas.settleLateOutcomeLaw
                          { reward := R, forfeit := D, dropCharge := c, inclusion := q, leak :=
                            leak,
                            packetCost := packetCost }
                          true A.strategy ≠
                        Vegas.settleLateIntendedOutcome := by
  exact @Vegas.settleLate_not_preserved_for_every_margin
    R D c reward_pos margin charge leak packetCost

/-- info: 'Vegas.Paper.settleLate_not_preserved_for_every_margin' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.settleLate_not_preserved_for_every_margin

/-- The paper statement has its proof in
`Vegas.lateLeak_sample_totalVariation_lower_bound`. -/
theorem Vegas.Paper.lateLeak_sample_totalVariation_lower_bound :
    ∀
      {A : (Vegas.lateLeakModel Vegas.LateLeakParameters.sample true).BehavioralAssessment}
      (_equilibrium :
        A.IsSequentialEquilibrium (Vegas.lateLeak_antichain Vegas.LateLeakParameters.sample true)
          (Vegas.lateLeak_terminates Vegas.LateLeakParameters.sample true)
          (Vegas.lateLeakPayoff Vegas.LateLeakParameters.sample true))
      {error : ℝ}
      (_close :
        PMF.WithinTV error (Vegas.lateLeakOutcomeLaw Vegas.LateLeakParameters.sample true
          A.strategy)
          Vegas.lateLeakIntendedOutcome),
      267 / 2000 ≤ error := by
  exact @Vegas.lateLeak_sample_totalVariation_lower_bound

/-- info: 'Vegas.Paper.lateLeak_sample_totalVariation_lower_bound' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.lateLeak_sample_totalVariation_lower_bound

/-- The paper statement has its proof in
`Vegas.lateLeak_sample_result_totalVariation_lower_bound`. -/
theorem Vegas.Paper.lateLeak_sample_result_totalVariation_lower_bound :
    ∀
      {A : (Vegas.lateLeakModel Vegas.LateLeakParameters.sample true).BehavioralAssessment}
      (_equilibrium :
        A.IsSequentialEquilibrium (Vegas.lateLeak_antichain Vegas.LateLeakParameters.sample true)
          (Vegas.lateLeak_terminates Vegas.LateLeakParameters.sample true)
          (Vegas.lateLeakPayoff Vegas.LateLeakParameters.sample true))
      {error : ℝ}
      (_close :
        PMF.WithinTV error (Vegas.lateLeakResultLaw Vegas.LateLeakParameters.sample true A.strategy)
          Vegas.lateLeakIntendedResultLaw),
      3 / 2000 ≤ error := by
  exact @Vegas.lateLeak_sample_result_totalVariation_lower_bound

/-- info: 'Vegas.Paper.lateLeak_sample_result_totalVariation_lower_bound' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.lateLeak_sample_result_totalVariation_lower_bound

/-- The paper statement has its proof in
`Vegas.lateLeak_outcome_preserved_of_half_reward_costs`. -/
theorem Vegas.Paper.lateLeak_outcome_preserved_of_half_reward_costs
    {G : Vegas.LateLeakParameters}
    (reward : 0 ≤ G.reward)
    (never : G.reward / 2 < G.forfeit)
    (attempt : G.reward / 2 < (1 - Vegas.lateLeakInclusionProb G) * (G.forfeit + G.dropCharge))
    (A : (Vegas.lateLeakModel G true).BehavioralAssessment)
    (_equilibrium :
        A.IsSequentialEquilibrium (Vegas.lateLeak_antichain G true) (Vegas.lateLeak_terminates
          G true)
          (Vegas.lateLeakPayoff G true)) :
    Vegas.lateLeakOutcomeLaw G true A.strategy = Vegas.lateLeakIntendedOutcome := by
  exact @Vegas.lateLeak_outcome_preserved_of_half_reward_costs
    G reward never attempt A _equilibrium

/-- info: 'Vegas.Paper.lateLeak_outcome_preserved_of_half_reward_costs' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.lateLeak_outcome_preserved_of_half_reward_costs
