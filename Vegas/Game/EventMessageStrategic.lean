/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.EventMessages
import Vegas.Pending.EventStrategicLaw

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
    (runtime : EventGraphRuntime setup.eventGraph) (feasible : runtime.ServiceFeasible)
    (roster : List Player) (reactionRounds : Nat)
    (wire : runtime.application.WirePolicy) (order : runtime.ServiceOrderPolicy)
    (profile : BehavioralProfile setup.program) (who : Player)
    (replacement : runtime.application.PlayerPolicy) :
    ∃ mixture : FinDist (BehavioralPolicy who setup.program),
      ((setup.eventPendingGame runtime roster reactionRounds wire order).play
        (Profile.update (sig := (setup.eventPendingGame runtime
          roster reactionRounds wire order).sig)
          (fun actor => setup.compileEventPendingStrategy runtime actor (profile actor))
          who replacement)).map (setup.eventPendingOutcome runtime) =
      mixture.bind fun alternative =>
        (setup.run (Profile.update (sig := SourceProgram.gameSignature setup.program)
          profile who alternative)).map some := by
  obtain ⟨mixture, law⟩ := runtime.exists_deviation_mixture_store_law feasible
    (EventLowering.toEventGraph_barrierOrdered setup.program setup.namesNodup)
    (setup.initialLaw.map fun initial => setup.eventInputs initial.1)
    (EventLowering.compileEventProfile setup.program setup.namesNodup profile)
    roster reactionRounds who replacement wire order
  refine ⟨mixture.map (EventLowering.backtranslateEventPolicy setup.program setup.namesNodup who),
    ?_⟩
  rw [setup.eventPendingGame_map_outcome]
  change (((runtime.servicedEventGame _ roster reactionRounds wire order).play
    (Profile.update (sig := MessageApplication.policySignature Player runtime.application)
      (runtime.compileProfile
        (EventLowering.compileEventProfile setup.program setup.namesNodup profile))
      who replacement)).map (fun execution => execution.native.application.config.store)).map _ = _
  rw [law]
  simp only [FinDist.map_bind, FinDist.bind_map]
  apply FinDist.bind_congr
  intro alternative _
  exact EventLowering.canonical_setup_deviation_decode setup profile who alternative

/-- A composable exact strategic certificate for the concrete source compiler
and public pending-message service. All native unilateral policies are admitted. -/
def eventPendingSimulation (setup : Setup (Player := Player) (L := L))
    (runtime : EventGraphRuntime setup.eventGraph) (feasible : runtime.ServiceFeasible)
    (roster : List Player) (reactionRounds : Nat)
    (wire : runtime.application.WirePolicy) (order : runtime.ServiceOrderPolicy) :
    GameForm.MixtureSimulationOn setup.gameForm
      (setup.eventPendingGame runtime roster reactionRounds wire order) some
      (setup.eventPendingOutcome runtime) (fun _ _ => True) where
  compileStrategy := setup.compileEventPendingStrategy runtime
  honest_law profile :=
    setup.eventPendingGame_honest_law runtime feasible roster reactionRounds wire order profile
  compiled_considered _ _ := trivial
  deviation_mixture profile who replacement _ :=
    setup.eventPendingGame_deviation_law runtime feasible roster reactionRounds wire order
      profile who replacement

/-- Every lower bound on a terminal-state observation against unilateral
source deviations holds against arbitrary unilateral native deviations. The
observation need not describe the deviating player's preferences. -/
theorem eventPendingGame_deviation_guarantee
    (setup : Setup (Player := Player) (L := L))
    (runtime : EventGraphRuntime setup.eventGraph) (feasible : runtime.ServiceFeasible)
    (roster : List Player) (reactionRounds : Nat)
    (wire : runtime.application.WirePolicy) (order : runtime.ServiceOrderPolicy)
    (profile : BehavioralProfile setup.program) (who : Player)
    (value : State L setup.program.terminalCtx → ℝ) (missing bound : ℝ)
    (sourceBound : ∀ alternative : BehavioralPolicy who setup.program,
      bound ≤ (setup.run (Profile.update (sig := SourceProgram.gameSignature setup.program)
        profile who alternative)).expect value)
    (replacement : runtime.application.PlayerPolicy) :
    bound ≤ ((setup.eventPendingGame runtime roster reactionRounds wire order).play
      (Profile.update (sig := (setup.eventPendingGame runtime
        roster reactionRounds wire order).sig)
        (fun actor => setup.compileEventPendingStrategy runtime actor (profile actor))
        who replacement)).expect
          (fun outcome => (setup.eventPendingOutcome runtime outcome).elim missing value) := by
  let optionValue : Option (State L setup.program.terminalCtx) → ℝ :=
    fun outcome => outcome.elim missing value
  apply (setup.eventPendingSimulation runtime feasible roster reactionRounds wire order).guarantee
    profile who optionValue bound
  · intro alternative
    exact sourceBound alternative
  · trivial

/-- Same-error Nash preservation and reflection at compiled profiles for every
utility of the terminal source state, against arbitrary native deviations. -/
theorem eventPendingGame_approximate_nash_iff
    (setup : Setup (Player := Player) (L := L))
    (runtime : EventGraphRuntime setup.eventGraph) (feasible : runtime.ServiceFeasible)
    (roster : List Player) (reactionRounds : Nat)
    (wire : runtime.application.WirePolicy) (order : runtime.ServiceOrderPolicy)
    (utility : State L setup.program.terminalCtx → Player → ℝ)
    (missing : Player → ℝ) (ε : ℝ) (profile : BehavioralProfile setup.program) :
    IsεNash (setup.eventPendingGame runtime roster reactionRounds wire order)
        (fun outcome who => (setup.eventPendingOutcome runtime outcome).elim
          (missing who) (fun state => utility state who))
        ε (fun who => setup.compileEventPendingStrategy runtime who (profile who)) ↔
      IsεNash setup.gameForm utility ε profile := by
  let optionUtility : Option (State L setup.program.terminalCtx) → Player → ℝ :=
    fun outcome who => outcome.elim (missing who) (fun state => utility state who)
  exact GameForm.MixtureSimulationOn.isεNash_compileProfile_iff
    (setup.eventPendingSimulation runtime feasible roster reactionRounds wire order)
    optionUtility ε profile (fun _ _ => trivial)

end Vegas.SourceProgram.Setup
