/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.EventMessages
import Vegas.Pending.EventStrategicLaw
import GameTheoryExtensions.Core.UtilitySimulation

/-! # Strategic correctness of asynchronous source-to-message compilation

The graph-relative native deviation law composes with canonical graph-to-source
backtranslation. Both edges retain one deviation mixture across private setup.
-/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory GameTheory.Math.Probability Interaction

variable {Player : Type} [DecidableEq Player]
variable {L : IExpr} [IExpr.ResultTypes L]

/-- Every unilateral native policy has exactly the terminal source-state law
of a finite mixture of source policies, against unchanged opponents. -/
theorem eventPendingGame_deviation_law
    (setup : Setup (Player := Player) (L := L))
    (mode : Vegas.EventGraph.ExecutionMode)
    (runtime : EventGraphRuntime (setup.eventGraph.withMode mode))
    (feasible : runtime.ServiceFeasible)
    (roster : List Player) (reactionRounds : Nat)
    (wire : runtime.application.WirePolicy) (order : runtime.ServiceOrderPolicy)
    (profile : BehavioralProfile setup.program) (who : Player)
    (replacement : runtime.application.PlayerPolicy) :
    ∃ mixture : FinDist (BehavioralPolicy who setup.program),
      ((setup.eventPendingGame mode runtime roster reactionRounds wire order).play
        (Profile.update (sig := (setup.eventPendingGame mode runtime
          roster reactionRounds wire order).sig)
          (fun actor => setup.compileEventPendingStrategy mode runtime actor (profile actor))
          who replacement)).map (setup.eventPendingOutcome mode runtime) =
      mixture.bind fun alternative =>
        (setup.run (Profile.update (sig := SourceProgram.gameSignature setup.program)
          profile who alternative)).map some := by
  obtain ⟨mixture, law⟩ := runtime.exists_deviation_mixture_store_law feasible
    (setup.eventGraph.withMode_barrierOrdered
      (EventLowering.toEventGraph_barrierOrdered setup.program setup.namesNodup) mode)
    (setup.initialLaw.map fun initial => setup.eventInputs initial.1)
    (setup.eventGraph.toModeProfile mode
      (EventLowering.compileEventProfile setup.program setup.namesNodup profile))
    roster reactionRounds who replacement wire order
  refine ⟨mixture.map (fun alternative =>
    EventLowering.backtranslateEventPolicy setup.program setup.namesNodup who
      (setup.eventGraph.fromModePolicy mode who alternative)), ?_⟩
  rw [setup.eventPendingGame_map_outcome]
  change (((runtime.servicedEventGame _ roster reactionRounds wire order).play
    (Profile.update (sig := MessageApplication.policySignature Player runtime.application)
      (runtime.compileProfile
        (setup.eventGraph.toModeProfile mode
          (EventLowering.compileEventProfile setup.program setup.namesNodup profile)))
      who replacement)).map (fun execution => execution.native.application.config.store)).map _ = _
  rw [law]
  simp only [FinDist.map_bind, FinDist.bind_map]
  apply FinDist.bind_congr
  intro alternative _
  simp_rw [← (setup.eventGraph.withMode mode).runPolicies_canonical_normalize_eq,
    setup.eventGraph.runPolicies_withMode_store, setup.eventGraph.fromModeProfile_update,
    setup.eventGraph.fromModeProfile_toModeProfile]
  have canonical := EventLowering.canonical_setup_deviation_decode setup profile who
    (setup.eventGraph.fromModePolicy mode who alternative)
  simp only [← Vegas.EventGraph.runPolicies_canonical_normalize_eq] at canonical
  exact canonical

/-- A composable exact strategic certificate for the concrete source compiler
and public pending-message service. All native unilateral policies are admitted. -/
def eventPendingSimulation (setup : Setup (Player := Player) (L := L))
    (mode : Vegas.EventGraph.ExecutionMode)
    (runtime : EventGraphRuntime (setup.eventGraph.withMode mode))
    (feasible : runtime.ServiceFeasible)
    (roster : List Player) (reactionRounds : Nat)
    (wire : runtime.application.WirePolicy) (order : runtime.ServiceOrderPolicy) :
    GameForm.MixtureSimulationOn setup.gameForm
      (setup.eventPendingGame mode runtime roster reactionRounds wire order) some
      (setup.eventPendingOutcome mode runtime) (fun _ _ => True) where
  compileStrategy := setup.compileEventPendingStrategy mode runtime
  honest_law profile :=
    setup.eventPendingGame_honest_law mode runtime feasible roster reactionRounds wire order profile
  compiled_considered _ _ := trivial
  deviation_mixture profile who replacement _ :=
    setup.eventPendingGame_deviation_law mode runtime feasible roster reactionRounds wire order
      profile who replacement

/-- Every lower bound on a terminal-state observation against unilateral
source deviations holds against arbitrary unilateral native deviations. The
observation need not describe the deviating player's preferences. -/
theorem eventPendingGame_deviation_guarantee
    (setup : Setup (Player := Player) (L := L))
    (mode : Vegas.EventGraph.ExecutionMode)
    (runtime : EventGraphRuntime (setup.eventGraph.withMode mode))
    (feasible : runtime.ServiceFeasible)
    (roster : List Player) (reactionRounds : Nat)
    (wire : runtime.application.WirePolicy) (order : runtime.ServiceOrderPolicy)
    (profile : BehavioralProfile setup.program) (who : Player)
    (value : State L setup.program.terminalCtx → ℝ) (missing bound : ℝ)
    (sourceBound : ∀ alternative : BehavioralPolicy who setup.program,
      bound ≤ (setup.run (Profile.update (sig := SourceProgram.gameSignature setup.program)
        profile who alternative)).expect value)
    (replacement : runtime.application.PlayerPolicy) :
    bound ≤ ((setup.eventPendingGame mode runtime roster reactionRounds wire order).play
      (Profile.update (sig := (setup.eventPendingGame mode runtime
        roster reactionRounds wire order).sig)
        (fun actor => setup.compileEventPendingStrategy mode runtime actor (profile actor))
        who replacement)).expect
          (fun outcome => (setup.eventPendingOutcome mode runtime outcome).elim missing value) := by
  let optionValue : Option (State L setup.program.terminalCtx) → ℝ :=
    fun outcome => outcome.elim missing value
  let simulation :=
    setup.eventPendingSimulation mode runtime feasible roster reactionRounds wire order
  apply simulation.guarantee profile who optionValue bound
  · intro alternative
    exact sourceBound alternative
  · trivial

/-- Against fixed opponents, each native deviation's expected terminal-state
test value is bounded above by that of some legal source deviation. The witness
may depend on both the profile and the chosen test. -/
theorem eventPendingGame_deviation_utility_bound
    (setup : Setup (Player := Player) (L := L))
    (mode : Vegas.EventGraph.ExecutionMode)
    (runtime : EventGraphRuntime (setup.eventGraph.withMode mode))
    (feasible : runtime.ServiceFeasible)
    (roster : List Player) (reactionRounds : Nat)
    (wire : runtime.application.WirePolicy) (order : runtime.ServiceOrderPolicy)
    (profile : BehavioralProfile setup.program) (who : Player)
    (value : State L setup.program.terminalCtx → ℝ) (missing : ℝ)
    (replacement : runtime.application.PlayerPolicy) :
    ∃ alternative : BehavioralPolicy who setup.program,
      ((setup.eventPendingGame mode runtime roster reactionRounds wire order).play
        (Profile.update
          (sig := (setup.eventPendingGame mode runtime roster reactionRounds wire order).sig)
          (fun actor => setup.compileEventPendingStrategy mode runtime actor (profile actor))
          who replacement)).expect
            (fun outcome => (setup.eventPendingOutcome mode runtime outcome).elim missing value) ≤
      (setup.run (Profile.update (sig := SourceProgram.gameSignature setup.program)
        profile who alternative)).expect (fun state => value state) := by
  let optionValue : Option (State L setup.program.terminalCtx) → Player → ℝ :=
    fun outcome _ => outcome.elim missing value
  let simulation :=
    setup.eventPendingSimulation mode runtime feasible roster reactionRounds wire order
  obtain ⟨alternative, hbound⟩ :=
    (simulation.toUtilitySimulation optionValue (fun _ _ => trivial)).deviation_bound
      profile who replacement
  refine ⟨alternative, ?_⟩
  change
    ((setup.eventPendingGame mode runtime roster reactionRounds wire order).play
      (Profile.update
        (sig := (setup.eventPendingGame mode runtime roster reactionRounds wire order).sig)
        (fun actor => setup.compileEventPendingStrategy mode runtime actor (profile actor))
        who replacement)).expect
          (fun outcome => optionValue (setup.eventPendingOutcome mode runtime outcome) who) ≤
      (setup.gameForm.play (Profile.update profile who alternative)).expect
        (fun state => optionValue (some state) who) at hbound
  exact hbound

/-- Same-error Nash preservation and reflection at compiled profiles for every
utility of the terminal source state, against arbitrary native deviations. -/
theorem eventPendingGame_approximate_nash_iff
    (setup : Setup (Player := Player) (L := L))
    (mode : Vegas.EventGraph.ExecutionMode)
    (runtime : EventGraphRuntime (setup.eventGraph.withMode mode))
    (feasible : runtime.ServiceFeasible)
    (roster : List Player) (reactionRounds : Nat)
    (wire : runtime.application.WirePolicy) (order : runtime.ServiceOrderPolicy)
    (utility : State L setup.program.terminalCtx → Player → ℝ)
    (missing : Player → ℝ) (ε : ℝ) (profile : BehavioralProfile setup.program) :
    IsεNash (setup.eventPendingGame mode runtime roster reactionRounds wire order)
        (fun outcome who => (setup.eventPendingOutcome mode runtime outcome).elim
          (missing who) (fun state => utility state who))
        ε (fun who => setup.compileEventPendingStrategy mode runtime who (profile who)) ↔
      IsεNash setup.gameForm utility ε profile := by
  let optionUtility : Option (State L setup.program.terminalCtx) → Player → ℝ :=
    fun outcome who => outcome.elim (missing who) (fun state => utility state who)
  exact GameForm.MixtureSimulationOn.isεNash_compileProfile_iff
    (setup.eventPendingSimulation mode runtime feasible roster reactionRounds wire order)
    optionUtility ε profile (fun _ _ => trivial)

end Vegas.SourceProgram.Setup
