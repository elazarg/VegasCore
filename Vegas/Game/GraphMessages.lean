/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Compile.GraphSetup
import Vegas.Game.GraphSetup
import Vegas.Compile.GraphBindingDiscipline
import Vegas.Graph.MessageHonestLaw
import Vegas.Graph.MessageServiceTermination
import Vegas.Graph.MessageDeviationMixture
import GameTheoryExtensions.Core.UtilitySimulation

/-! # The source compiler's serviced pending-message target

The target first samples the specified initial setup, then runs the actual
compiled graph in the shared public-message policy game. Player strategies
range over arbitrary native policies. Only the service realization fixes
invocation opportunities and reserved inclusion/clock commands; its wire
policy remains adaptive.

The composed target always completes under its concrete service, even with
arbitrary player policies. Its honest outcome law composes the checked graph
edges. The checked unilateral-deviation mixture and Nash correspondence compose
those runtime and compiler edges through the source game.
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

/-- A graph-policy deviation mixture for the actual pending target composes
with source/graph backtranslation into a source behavioral-policy mixture.
This is a conditional compiler-edge reduction, not the pending deviation
capstone itself. -/
theorem pendingGame_deviation_law_of_graph
    (setup : Setup (Player := Player) (L := L))
    (runtime : GraphRuntime Player L (graphCtx setup.program.terminalCtx))
    (roster : List Player) (reactionRounds : Nat) (wire : runtime.application.WirePolicy)
    (profile : BehavioralProfile setup.program) (who : Player)
    (replacement : runtime.application.PlayerPolicy)
    (hGraph : ∃ mixture : FinDist (Graph.BehavioralPolicy who setup.graph),
      ((setup.pendingGame runtime roster reactionRounds wire).play
        (Profile.update
          (fun actor => setup.compilePendingStrategy runtime actor (profile actor))
          who replacement)).map (setup.pendingOutcome runtime) =
      mixture.bind (fun alternative =>
        (setup.graphGameForm.play
          (Profile.update (sig := Graph.gameSignature setup.graph)
            (setup.compileGraphProfile profile) who alternative)).map
            (fun outcome => some (setup.decodeGraph outcome)))) :
    ∃ mixture : FinDist (BehavioralPolicy who setup.program),
      ((setup.pendingGame runtime roster reactionRounds wire).play
        (Profile.update
          (fun actor => setup.compilePendingStrategy runtime actor (profile actor))
          who replacement)).map (setup.pendingOutcome runtime) =
      mixture.bind (fun alternative =>
        (setup.run (Profile.update (sig := SourceProgram.gameSignature setup.program)
          profile who alternative)).map some) := by
  obtain ⟨graphMixture, graphLaw⟩ := hGraph
  let backtranslate (alternative : Graph.BehavioralPolicy who setup.graph) :
      BehavioralPolicy who setup.program :=
    backtranslateGraphPolicy setup.program setup.namesNodup initialMap [] who alternative
  refine ⟨graphMixture.map backtranslate, graphLaw.trans ?_⟩
  rw [FinDist.bind_map]
  apply FinDist.bind_congr
  intro alternative _
  have law := setup.graph_deviation_law profile who alternative
  have mapped := congrArg (FinDist.map some) law
  simpa only [FinDist.map_comp, Function.comp_def, backtranslate] using mapped

/-- Every native unilateral deviation of the serviced pending target is an
exact finite mixture of legal source behavioral deviations. -/
theorem pendingGame_deviation_law
    (setup : Setup (Player := Player) (L := L))
    (runtime : GraphRuntime Player L (graphCtx setup.program.terminalCtx))
    (roster : List Player) (reactionRounds : Nat) (wire : runtime.application.WirePolicy)
    (profile : BehavioralProfile setup.program) (who : Player)
    (replacement : runtime.application.PlayerPolicy) :
    ∃ mixture : FinDist (BehavioralPolicy who setup.program),
      ((setup.pendingGame runtime roster reactionRounds wire).play
        (Profile.update
          (fun actor => setup.compilePendingStrategy runtime actor (profile actor))
          who replacement)).map (setup.pendingOutcome runtime) =
      mixture.bind (fun alternative =>
        (setup.run (Profile.update (sig := SourceProgram.gameSignature setup.program)
          profile who alternative)).map some) := by
  apply setup.pendingGame_deviation_law_of_graph runtime roster reactionRounds wire profile who
    replacement
  have graphLaw := runtime.servicedGame_deviation_law setup.graph
    (setup.compileGraphProfile profile)
    (setup.initialLaw.map fun initial => encodeState initial.1)
    (by simpa only [graphCtx_names] using setup.namesNodup)
    setup.graph_bindingDiscipline roster reactionRounds wire who replacement
  obtain ⟨mixture, law⟩ := graphLaw
  refine ⟨mixture, ?_⟩
  have decoded := congrArg (FinDist.map (Option.map setup.decodeGraph)) law
  rw [FinDist.map_bind] at decoded
  change
    (((runtime.servicedGame setup.graph
      (setup.initialLaw.map fun initial => encodeState initial.1)
      roster reactionRounds wire).play
      (Profile.update (runtime.compileProfile setup.graph (setup.compileGraphProfile profile))
        who replacement)).map
      (fun execution => execution.native.application.outcome?.map setup.decodeGraph)) = _
  simpa only [graphGameForm, FinDist.map_comp, FinDist.bind_map,
    Function.comp_def, Option.map_some] using decoded

/-- Exact strategic simulation of source play by the serviced pending-message
runtime.  The common observation keeps missing native outcomes explicit. -/
def pendingSimulation (setup : Setup (Player := Player) (L := L))
    (runtime : GraphRuntime Player L (graphCtx setup.program.terminalCtx))
    (roster : List Player) (reactionRounds : Nat) (wire : runtime.application.WirePolicy) :
    GameForm.MixtureSimulationOn setup.gameForm
      (setup.pendingGame runtime roster reactionRounds wire) some
      (setup.pendingOutcome runtime) (fun _ _ => True) where
  compileStrategy := setup.compilePendingStrategy runtime
  honest_law profile := setup.pendingGame_honest_law runtime roster reactionRounds wire profile
  compiled_considered _ _ := trivial
  deviation_mixture profile who replacement _ :=
    setup.pendingGame_deviation_law runtime roster reactionRounds wire profile who replacement

/-- Same-error approximate Nash is preserved and reflected at the compiled
pending-message profile for every terminal-state utility. -/
theorem pendingGame_approximate_nash_iff
    (setup : Setup (Player := Player) (L := L))
    (runtime : GraphRuntime Player L (graphCtx setup.program.terminalCtx))
    (roster : List Player) (reactionRounds : Nat) (wire : runtime.application.WirePolicy)
    (utility : State L setup.program.terminalCtx → Player → ℝ)
    (missing : Player → ℝ) (ε : ℝ)
    (profile : BehavioralProfile setup.program) :
    IsεNash (setup.pendingGame runtime roster reactionRounds wire)
        (fun outcome who => (setup.pendingOutcome runtime outcome).elim
          (missing who) (fun state => utility state who)) ε
        (fun who => setup.compilePendingStrategy runtime who (profile who)) ↔
      IsεNash setup.gameForm utility ε profile := by
  let optionUtility : Option (State L setup.program.terminalCtx) → Player → ℝ := fun outcome who =>
    outcome.elim (missing who) (fun state => utility state who)
  change
    IsεNash (setup.pendingGame runtime roster reactionRounds wire)
        (fun outcome who => optionUtility (setup.pendingOutcome runtime outcome) who) ε
        ((setup.pendingSimulation runtime roster reactionRounds wire).compileProfile profile) ↔
      IsεNash setup.gameForm (fun state who => optionUtility (some state) who) ε profile
  simpa only [optionUtility, Option.elim_some, pendingSimulation,
    GameForm.MixtureSimulationOn.compileProfile] using
    (setup.pendingSimulation runtime roster reactionRounds wire).isεNash_compileProfile_iff
      optionUtility ε profile (fun _ _ => trivial)

/-- info: 'Vegas.SourceProgram.Setup.pendingGame_honest_law' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.pendingGame_honest_law

/-- info: 'Vegas.SourceProgram.Setup.pendingGame_approximate_nash_of_compiled' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.pendingGame_approximate_nash_of_compiled

/-- info: 'Vegas.SourceProgram.Setup.pendingGame_deviation_law_of_graph' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.pendingGame_deviation_law_of_graph

/-- info: 'Vegas.SourceProgram.Setup.pendingGame_deviation_law' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.pendingGame_deviation_law

/-- info: 'Vegas.SourceProgram.Setup.pendingGame_approximate_nash_iff' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.pendingGame_approximate_nash_iff

end Vegas.SourceProgram.Setup
