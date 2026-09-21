/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.EventMessages
import Vegas.Game.EventServiceEdge
import Vegas.Pending.EventStrategicLaw
import GameTheoryExtensions.Core.UtilitySimulation
import GameTheoryExtensions.Core.MixtureSimulationComposition

/-! # Strategic correctness of asynchronous source-to-message compilation

The certificate is three edges composed. The compiler reaches the canonical
graph with a single backtranslated policy; the execution mode is a second edge,
also a single policy; the message service is the third, and the only one that
needs a mixture. Each retains one deviation across private setup.

The last step replaces the store reading by the semantic one. They agree on
every serviced play -- completion discharges the terminality test -- and differ
only where the game never goes.
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
      (EventLowering.toEventGraph_barrierOrdered setup.program) mode)
    (setup.initialLaw.map fun initial => setup.eventInputs initial)
    (setup.eventGraph.toModeProfile mode
      (EventLowering.compileEventProfile setup.program profile))
    roster reactionRounds who replacement wire order
  refine ⟨mixture.map (fun alternative =>
    EventLowering.backtranslateEventPolicy setup.program who
      (setup.eventGraph.fromModePolicy mode who alternative)), ?_⟩
  rw [setup.eventPendingGame_map_outcome]
  change (((runtime.servicedEventGame _ roster reactionRounds wire order).play
    (Profile.update (sig := MessageApplication.policySignature Player runtime.application)
      (runtime.compileProfile
        (setup.eventGraph.toModeProfile mode
          (EventLowering.compileEventProfile setup.program profile)))
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

/-- The semantic readout and the store decoder induce the same law on every
serviced play, whatever the players do. -/
private theorem eventPendingGame_map_publicOutcome (setup : Setup (Player := Player) (L := L))
    (mode : Vegas.EventGraph.ExecutionMode)
    (runtime : EventGraphRuntime (setup.eventGraph.withMode mode))
    (roster : List Player) (reactionRounds : Nat)
    (wire : runtime.application.WirePolicy) (order : runtime.ServiceOrderPolicy)
    (players : Profile
      (setup.eventPendingGame mode runtime roster reactionRounds wire order).sig) :
    ((setup.eventPendingGame mode runtime roster reactionRounds wire order).play players).map
        (setup.eventPendingPublicOutcome mode runtime) =
      ((setup.eventPendingGame mode runtime roster reactionRounds wire order).play players).map
        (fun execution => setup.eventPublicDecode execution.native.application.config.store) := by
  have base := congrArg (FinDist.map (Option.map (publicOutcome setup.program)))
    (setup.eventPendingGame_map_outcome mode runtime roster reactionRounds wire order players)
  rw [eventPendingPublicOutcome_eq, ← FinDist.map_comp, base]
  simp only [FinDist.map_comp, Function.comp_def, eventPublicDecode]

/-- A composable exact strategic certificate for the concrete source compiler
and public pending-message service: the compiler's edge to the canonical graph,
the execution mode's edge above it, and the message service's edge above that.
All native unilateral policies are admitted, and the mixture is the service's
contribution. -/
def eventPendingSimulation (setup : Setup (Player := Player) (L := L))
    (mode : Vegas.EventGraph.ExecutionMode)
    (runtime : EventGraphRuntime (setup.eventGraph.withMode mode))
    (feasible : runtime.ServiceFeasible)
    (roster : List Player) (reactionRounds : Nat)
    (wire : runtime.application.WirePolicy) (order : runtime.ServiceOrderPolicy) :
    GameForm.MixtureSimulationOn setup.gameForm
      (setup.eventPendingGame mode runtime roster reactionRounds wire order) some
      (setup.eventPendingPublicOutcome mode runtime) (fun _ _ => True) :=
  (((setup.canonicalEventSimulation.reobserve some some
        (fun outcome => setup.eventPublicDecode (setup.eventGraph.terminalStore outcome))
        (fun _ => rfl) setup.eventPublicDecode_terminalStore).trans
      (((setup.eventGraph.eventModeSimulation mode
            (setup.initialLaw.map fun initial => setup.eventInputs initial)).trans
          (runtime.servicedCanonicalSimulation
            (setup.eventGraph.withMode_barrierOrdered
              (EventLowering.toEventGraph_barrierOrdered setup.program) mode)
            feasible (setup.initialLaw.map fun initial => setup.eventInputs initial)
            roster reactionRounds wire order)
          (fun _ _ => trivial)).reobserve setup.eventPublicDecode
            (fun outcome => setup.eventPublicDecode (setup.eventGraph.terminalStore outcome))
            (fun execution =>
              setup.eventPublicDecode execution.native.application.config.store)
            (fun _ => rfl) (fun _ => rfl))
      (fun _ _ => trivial)).reobserveTarget (setup.eventPendingPublicOutcome mode runtime)
    (setup.eventPendingGame_map_publicOutcome mode runtime roster reactionRounds wire order))

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
    (value : PublicOutcome setup.program → ℝ) (missing bound : ℝ)
    (sourceBound : ∀ alternative : BehavioralPolicy who setup.program,
      bound ≤ (setup.publicRun (Profile.update (sig := SourceProgram.gameSignature setup.program)
        profile who alternative)).expect value)
    (replacement : runtime.application.PlayerPolicy) :
    bound ≤ ((setup.eventPendingGame mode runtime roster reactionRounds wire order).play
      (Profile.update (sig := (setup.eventPendingGame mode runtime
        roster reactionRounds wire order).sig)
        (fun actor => setup.compileEventPendingStrategy mode runtime actor (profile actor))
        who replacement)).expect
          (fun outcome =>
            (setup.eventPendingPublicOutcome mode runtime outcome).elim missing value) := by
  let optionValue : Option (PublicOutcome setup.program) → ℝ :=
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
    (value : PublicOutcome setup.program → ℝ) (missing : ℝ)
    (replacement : runtime.application.PlayerPolicy) :
    ∃ alternative : BehavioralPolicy who setup.program,
      ((setup.eventPendingGame mode runtime roster reactionRounds wire order).play
        (Profile.update
          (sig := (setup.eventPendingGame mode runtime roster reactionRounds wire order).sig)
          (fun actor => setup.compileEventPendingStrategy mode runtime actor (profile actor))
          who replacement)).expect
            (fun outcome =>
              (setup.eventPendingPublicOutcome mode runtime outcome).elim missing value) ≤
      (setup.publicRun (Profile.update (sig := SourceProgram.gameSignature setup.program)
        profile who alternative)).expect (fun result => value result) := by
  let optionValue : Option (PublicOutcome setup.program) → Player → ℝ :=
    fun outcome _ => outcome.elim missing value
  let simulation :=
    setup.eventPendingSimulation mode runtime feasible roster reactionRounds wire order
  obtain ⟨alternative, hbound⟩ :=
    (simulation.toUtilitySimulation optionValue (fun _ _ => trivial)).unilateral_bound
      subset_rfl profile who replacement
  refine ⟨alternative, ?_⟩
  change
    ((setup.eventPendingGame mode runtime roster reactionRounds wire order).play
      (Profile.update
        (sig := (setup.eventPendingGame mode runtime roster reactionRounds wire order).sig)
        (fun actor => setup.compileEventPendingStrategy mode runtime actor (profile actor))
        who replacement)).expect
          (fun outcome => optionValue (setup.eventPendingPublicOutcome mode runtime outcome) who) ≤
      (setup.gameForm.play (Profile.update profile who alternative)).expect
        (fun result => optionValue (some result) who) at hbound
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
    (utility : PublicOutcome setup.program → Player → ℝ)
    (missing : Player → ℝ) (ε : ℝ) (profile : BehavioralProfile setup.program) :
    IsεNash (setup.eventPendingGame mode runtime roster reactionRounds wire order)
        (fun outcome who => (setup.eventPendingPublicOutcome mode runtime outcome).elim
          (missing who) (fun result => utility result who))
        ε (fun who => setup.compileEventPendingStrategy mode runtime who (profile who)) ↔
      IsεNash setup.gameForm utility ε profile := by
  let optionUtility : Option (PublicOutcome setup.program) → Player → ℝ :=
    fun outcome who => outcome.elim (missing who) (fun result => utility result who)
  exact GameForm.MixtureSimulationOn.isεNash_compileProfile_iff
    (setup.eventPendingSimulation mode runtime feasible roster reactionRounds wire order)
    optionUtility ε profile (fun _ _ => trivial)

/-- A source best response compiles to a best response against the same
opponents compiled, now against arbitrary native deviations. Only one player is
fixed, so the opponents need not be best responding themselves. -/
theorem eventPendingGame_isBestResponse_compileProfile
    (setup : Setup (Player := Player) (L := L))
    (mode : Vegas.EventGraph.ExecutionMode)
    (runtime : EventGraphRuntime (setup.eventGraph.withMode mode))
    (feasible : runtime.ServiceFeasible)
    (roster : List Player) (reactionRounds : Nat)
    (wire : runtime.application.WirePolicy) (order : runtime.ServiceOrderPolicy)
    (utility : PublicOutcome setup.program → Player → ℝ)
    (missing : Player → ℝ) (profile : BehavioralProfile setup.program) (who : Player)
    (best : IsBestResponse setup.gameForm (euPreference utility) who profile (profile who)) :
    IsBestResponse (setup.eventPendingGame mode runtime roster reactionRounds wire order)
      (euPreference fun outcome actor =>
        (setup.eventPendingPublicOutcome mode runtime outcome).elim
          (missing actor) (fun result => utility result actor)) who
      (fun actor => setup.compileEventPendingStrategy mode runtime actor (profile actor))
      (setup.compileEventPendingStrategy mode runtime who (profile who)) := by
  let optionUtility : Option (PublicOutcome setup.program) → Player → ℝ :=
    fun outcome actor => outcome.elim (missing actor) (fun result => utility result actor)
  exact ((setup.eventPendingSimulation mode runtime feasible roster reactionRounds wire
    order).toUtilitySimulation optionUtility
      (fun _ _ => trivial)).isBestResponse_compileProfile subset_rfl profile who best

/-- A dominant source policy compiles to a best response against every compiled
opponent profile, against arbitrary native deviations. The environment ranges
over compiled source profiles only, so this is dominance relative to
source-expressible opponents, not native dominance. -/
theorem eventPendingGame_isBestResponse_of_isDominant
    (setup : Setup (Player := Player) (L := L))
    (mode : Vegas.EventGraph.ExecutionMode)
    (runtime : EventGraphRuntime (setup.eventGraph.withMode mode))
    (feasible : runtime.ServiceFeasible)
    (roster : List Player) (reactionRounds : Nat)
    (wire : runtime.application.WirePolicy) (order : runtime.ServiceOrderPolicy)
    (utility : PublicOutcome setup.program → Player → ℝ)
    (missing : Player → ℝ) (who : Player) (policy : BehavioralPolicy who setup.program)
    (dominant : IsDominant setup.gameForm (euPreference utility) who policy)
    (opponents : BehavioralProfile setup.program) :
    IsBestResponse (setup.eventPendingGame mode runtime roster reactionRounds wire order)
      (euPreference fun outcome actor =>
        (setup.eventPendingPublicOutcome mode runtime outcome).elim
          (missing actor) (fun result => utility result actor)) who
      (fun actor => setup.compileEventPendingStrategy mode runtime actor (opponents actor))
      (setup.compileEventPendingStrategy mode runtime who policy) := by
  let optionUtility : Option (PublicOutcome setup.program) → Player → ℝ :=
    fun outcome actor => outcome.elim (missing actor) (fun result => utility result actor)
  exact ((setup.eventPendingSimulation mode runtime feasible roster reactionRounds wire
    order).toUtilitySimulation optionUtility
      (fun _ _ => trivial)).isBestResponse_compileStrategy_of_isDominant subset_rfl who
        policy dominant opponents

/-- Strong Nash reflects from a compiled profile: if no native coalition gains
at the compiled profile, then no source coalition gains at the source profile.
Only the honest law is used. The converse direction fails in general, because a
target may offer a coalition a channel the source lacks; see
`GameTheory.GameForm.CoalitionWitness.isEmpty_coalitionSimulation`. -/
theorem eventPendingGame_isStrongNash_of_compileProfile
    (setup : Setup (Player := Player) (L := L))
    (mode : Vegas.EventGraph.ExecutionMode)
    (runtime : EventGraphRuntime (setup.eventGraph.withMode mode))
    (feasible : runtime.ServiceFeasible)
    (roster : List Player) (reactionRounds : Nat)
    (wire : runtime.application.WirePolicy) (order : runtime.ServiceOrderPolicy)
    (utility : PublicOutcome setup.program → Player → ℝ)
    (missing : Player → ℝ) (ε : ℝ) (profile : BehavioralProfile setup.program)
    (strong : IsStrongNash (setup.eventPendingGame mode runtime roster reactionRounds wire order)
      (euPreferenceWithin ε fun outcome actor =>
        (setup.eventPendingPublicOutcome mode runtime outcome).elim
          (missing actor) (fun result => utility result actor))
      (fun actor => setup.compileEventPendingStrategy mode runtime actor (profile actor))) :
    IsStrongNash setup.gameForm (euPreferenceWithin ε utility) profile := by
  let optionUtility : Option (PublicOutcome setup.program) → Player → ℝ :=
    fun outcome actor => outcome.elim (missing actor) (fun result => utility result actor)
  exact ((setup.eventPendingSimulation mode runtime feasible roster reactionRounds wire
    order).toUtilitySimulation optionUtility
      (fun _ _ => trivial)).isStrongNash_of_compileProfile ε profile strong

end Vegas.SourceProgram.Setup
