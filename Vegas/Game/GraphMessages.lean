/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Compile.GraphSetup
import Vegas.Compile.GraphBindingDiscipline
import Vegas.Graph.MessageHonestLaw
import Vegas.Graph.MessageServiceTermination
import GameTheoryExtensions.Core.UtilitySimulation

/-! # The source compiler's serviced pending-message target

The target first samples the specified initial setup, then runs the actual
compiled graph in the shared public-message policy game. Player strategies
range over arbitrary native policies. Only the service realization fixes
invocation opportunities and reserved inclusion/clock commands; its wire
policy remains adaptive.

The composed target always completes under its concrete service, even with
arbitrary player policies. Its honest outcome law composes the checked graph
edges. The unilateral-deviation and Nash capstones remain separate obligations.
-/

noncomputable section
namespace Vegas.SourceProgram.Setup

open GameTheory GameTheory.Math.Probability Interaction

variable {Player : Type} [DecidableEq Player] {L : IExpr} [R : IExpr.ResultTypes L]

/-- Every sampled private setup is initialized separately; players use one
native policy across the setup distribution. -/
def pendingGame (setup : Setup (Player := Player) (L := L))
    (runtime : GraphRuntime Player L (graphCtx setup.program.terminalCtx))
    (roster : List Player) (reactionRounds : Nat)
    (wire : runtime.application.WirePolicy) : GameForm Player :=
  runtime.servicedGame setup.graph (setup.initialLaw.map fun initial => encodeState initial.1)
    roster reactionRounds wire

/-- Source strategy translation is the composition of the two actual compilers. -/
def compilePendingStrategy (setup : Setup (Player := Player) (L := L))
    (runtime : GraphRuntime Player L (graphCtx setup.program.terminalCtx))
    (who : Player) (policy : BehavioralPolicy who setup.program) :
    runtime.application.PlayerPolicy :=
  runtime.compilePlayerPolicy setup.graph who
    (compileGraphPolicy setup.program setup.namesNodup initialMap [] who policy)

/-- Missing terminal outcomes stay explicit until completion is established.
The full typed environment is an ideal semantic readout, not a ledger decoder
for undisclosed private values. -/
def pendingOutcome (setup : Setup (Player := Player) (L := L))
    (runtime : GraphRuntime Player L (graphCtx setup.program.terminalCtx))
    (execution : runtime.application.PolicyExecution) :
    Option (State L setup.program.terminalCtx) :=
  execution.native.application.outcome?.map setup.decodeGraph

/-- The concrete bounded service produces a decoded terminal state for every
supported target play, including arbitrary deviations and private initial setup.
This is completion, not a source execution-law or incentive correspondence. -/
theorem pendingGame_complete (setup : Setup (Player := Player) (L := L))
    (runtime : GraphRuntime Player L (graphCtx setup.program.terminalCtx))
    (roster : List Player) (reactionRounds : Nat)
    (wire : runtime.application.WirePolicy)
    (players : Player → runtime.application.PlayerPolicy)
    (outcome : runtime.application.PolicyExecution)
    (supported : outcome ∈
      ((setup.pendingGame runtime roster reactionRounds wire).play players).support) :
    (setup.pendingOutcome runtime outcome).isSome = true := by
  have completed : outcome.native.application.outcome?.isSome = true := by
    apply runtime.servicedGame_complete setup.graph
      (setup.initialLaw.map fun initial => encodeState initial.1)
      roster reactionRounds wire players outcome
    exact supported
  simpa only [pendingOutcome, Option.isSome_map] using completed

/-- Full-language honest execution preserves the source outcome law through
both compiler edges, including the same finite distribution of private setup. -/
theorem pendingGame_honest_law (setup : Setup (Player := Player) (L := L))
    (runtime : GraphRuntime Player L (graphCtx setup.program.terminalCtx))
    (roster : List Player) (reactionRounds : Nat) (wire : runtime.application.WirePolicy)
    (profile : BehavioralProfile setup.program) :
    ((setup.pendingGame runtime roster reactionRounds wire).play
      (fun who => setup.compilePendingStrategy runtime who (profile who))).map
        (setup.pendingOutcome runtime) = (setup.run profile).map some := by
  have graphLaw := runtime.servicedGame_honest_law setup.graph
    (setup.compileGraphProfile profile)
    (setup.initialLaw.map fun initial => encodeState initial.1)
    (by simpa only [graphCtx_names] using setup.namesNodup)
    setup.graph_bindingDiscipline roster reactionRounds wire
  have decoded := congrArg (fun law => law.map (Option.map setup.decodeGraph)) graphLaw
  simp only [FinDist.map_comp, FinDist.bind_map, Function.comp_def, Option.map_some] at decoded
  have sourceLaw := congrArg (fun law => law.map some) (setup.graph_honest_law profile)
  change ((setup.initialLaw.bind fun initial => Graph.run setup.graph
    (setup.compileGraphProfile profile) (encodeState initial.1)).map
      setup.decodeGraph).map some = (setup.run profile).map some at sourceLaw
  rw [FinDist.map_comp] at sourceLaw
  exact decoded.trans sourceLaw

/-- Approximate Nash at the compiled pending-message profile reflects back to
the source profile. Honest outcome-law preservation suffices for this one-way
implication; no claim about arbitrary native deviations is used. -/
theorem pendingGame_approximate_nash_of_compiled
    (setup : Setup (Player := Player) (L := L))
    (runtime : GraphRuntime Player L (graphCtx setup.program.terminalCtx))
    (roster : List Player) (reactionRounds : Nat) (wire : runtime.application.WirePolicy)
    (utility : State L setup.program.terminalCtx → Player → ℝ)
    (missing : Player → ℝ) (ε : ℝ)
    (profile : BehavioralProfile setup.program)
    (compiledNash : IsεNash (setup.pendingGame runtime roster reactionRounds wire)
      (fun outcome who => (setup.pendingOutcome runtime outcome).elim
        (missing who) (fun state => utility state who)) ε
      (fun who => setup.compilePendingStrategy runtime who (profile who))) :
    IsεNash setup.gameForm utility ε profile := by
  let target := setup.pendingGame runtime roster reactionRounds wire
  let compile := fun (who : Player) (policy : BehavioralPolicy who setup.program) =>
    setup.compilePendingStrategy runtime who policy
  let targetUtility := fun (outcome : target.sig.Outcome) (who : Player) =>
    (setup.pendingOutcome runtime outcome).elim (missing who) (fun state => utility state who)
  have honestUtility : ∀ alternative who,
      (target.play (fun player => compile player (alternative player))).expect
          (fun outcome => targetUtility outcome who) =
        (setup.gameForm.play alternative).expect (fun state => utility state who) := by
    intro alternative who
    have law := setup.pendingGame_honest_law runtime roster reactionRounds wire alternative
    have expected := congrArg
      (fun distribution => distribution.expect
        (fun outcome => outcome.elim (missing who) (fun state => utility state who))) law
    change (target.play (fun player => compile player (alternative player))).expect
        (fun outcome => targetUtility outcome who) =
      (setup.run alternative).expect (fun state => utility state who)
    simp only [FinDist.expect_map, Option.elim_some] at expected
    dsimp only [target, compile, targetUtility]
    exact expected
  exact GameTheory.GameForm.isεNash_of_compileProfile
    (source := setup.gameForm) (target := target)
    (sourceUtility := utility) (targetUtility := targetUtility)
    compile honestUtility profile ε compiledNash

/-- info: 'Vegas.SourceProgram.Setup.pendingGame_honest_law' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.pendingGame_honest_law

/-- info: 'Vegas.SourceProgram.Setup.pendingGame_approximate_nash_of_compiled' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.pendingGame_approximate_nash_of_compiled

end Vegas.SourceProgram.Setup
