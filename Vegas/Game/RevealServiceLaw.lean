/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.RevealServiceExecution
import Vegas.Game.RevealServicePayoffs
import Vegas.Game.SourceContinuation
import GameTheoryExtensions.Math.Probability.Support

/-! # Initialized law of the actual revelation compiler

The finite alphabet is fixed from the setup law. Arbitrarily correlated private
draws and all source withholding decisions are retained. The result uses the
existing native service evaluator and its actual normalized response compiler.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory.Math.Probability Interaction EventGraphRuntime
open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]

/-- The concrete split-response compiler has the exact complete typed source
law, for every alias weight including the canonical zero-weight compiler. -/
theorem compiled_plan_source_law
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (bounds : MessageBounds (graph setup)) (watcher : Player)
    (reveals : setup.program.RevealOnly)
    (observer : ∀ event, (graph setup).actor? event ≠ some watcher)
    (openable : ∀ initial ∈ setup.initialLaw.support, initial.BindingsOpenable)
    (profile : BehavioralProfile setup.program)
    (weight : ℝ) (nonnegative : 0 ≤ weight) (atMostOne : weight ≤ 1) :
    ((initialLaw setup).bind fun state =>
      (runtime setup).runInteractionPlan leaks
        (policy setup leaks (bounds.withInitialValues (initialLaw setup)) watcher profile
          weight nonnegative atMostOne)
        ((runtime setup).reportNetwork leaks watcher) (plan setup watcher)
        (ReactiveApplication.Execution.initial (application setup leaks) state)).map
      (fun final => decodeState? (terminalRefs setup.program)
        final.application.config.store) = (setup.run profile).map some := by
  let extended := bounds.withInitialValues (initialLaw setup)
  let players := policy setup leaks extended watcher profile weight nonnegative atMostOne
  have watcherPolicy : players watcher = (application setup leaks).reportFirstUnpublished := by
    simp only [players, policy, ↓reduceIte]
  have ordinary : ∀ who, who ≠ watcher → ∀ past view response,
      response ∈ (players who past view).support →
        response ∈ ordinaryActions setup leaks extended who past view := by
    intro who different past view response supported
    change response ∈ (policy setup leaks extended watcher profile weight nonnegative atMostOne
      who past view).support at supported
    rw [policy, ite_eq_right different] at supported
    exact ordinaryPolicy_covered setup leaks extended profile weight nonnegative atMostOne
      who past view response supported
  have projects : ∀ who, who ≠ watcher → ∀ past view opening,
      opening? setup leaks who past view = some opening →
      opening ∈ (extended.menu (runtime setup) leaks).actions who past view →
      (players who past view).map (sourceChoice setup leaks) =
        sourceChoiceLaw setup leaks profile who view := by
    intro who different past view opening selected covered
    change (policy setup leaks extended watcher profile weight nonnegative atMostOne
      who past view).map _ = _
    rw [policy, ite_eq_right different]
    exact ordinaryPolicy_projects setup leaks extended profile weight nonnegative atMostOne
      who past view opening selected covered
  rw [initialLaw, PMF.bind_map, PMF.map_bind, Setup.run, PMF.map_bind]
  apply bind_congr_on_support _
  intro initial supported
  have current := run_source_suffix_option_law setup leaks bounds watcher observer profile players
    watcherPolicy ordinary projects initial supported setup.program reveals profile
    (setup.initialConfig initial) (ContextRefs.initial setup.context (outputLayout setup.program))
    (outputEmbedding setup.program) (initialRefsBefore setup.program) 0
    (CompiledPolicySuffix.whole setup.program profile)
    (ReactiveApplication.Execution.initial (application setup leaks)
      (EventGraphRuntime.State.initial (graph := graph setup) (setup.eventInputs initial)))
    (checkpoint_initial setup leaks reveals initial (openable initial supported))
  exact current

/-- The actual C-game behavioral compiler preserves the complete typed source
readout law. It quantifies over every source policy and every alias weight,
without an equilibrium or independent-types premise. -/
theorem compiled_behavioral_source_law
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (bounds : MessageBounds (graph setup)) (watcher : Player)
    (reveals : setup.program.RevealOnly)
    (observer : ∀ event, (graph setup).actor? event ≠ some watcher)
    (openable : ∀ initial ∈ setup.initialLaw.support, initial.BindingsOpenable)
    (profile : BehavioralProfile setup.program)
    (weight : ℝ) (nonnegative : 0 ≤ weight) (atMostOne : weight ≤ 1) :
    ((information setup leaks (bounds.withInitialValues (initialLaw setup)) watcher).runBehavioral
      (compiledProfile setup leaks (bounds.withInitialValues (initialLaw setup)) watcher profile
        weight nonnegative atMostOne) (2 * horizon setup watcher + 1)).map
        (fun final => sourceReadout setup leaks final.state) = (setup.run profile).map some := by
  rw [← compiled_plan_source_law setup leaks bounds watcher reveals observer openable
    profile weight nonnegative atMostOne]
  rw [show (fun final : (protocol setup leaks
      (bounds.withInitialValues (initialLaw setup)) watcher).History =>
      sourceReadout setup leaks final.state) = sourceReadout setup leaks ∘ History.state from rfl,
    ← PMF.map_comp, menu_execution_law setup leaks _ watcher, decoded_compiledProfile]
  simp only [PMF.map_bind, PMF.map_comp]
  rw [initialLaw, PMF.bind_map, PMF.bind_map]
  apply bind_congr_on_support _
  intro initial _supported
  apply map_congr_on_support _
  intro final supported
  have settled := plan_terminal setup leaks watcher reveals
    (policy setup leaks (bounds.withInitialValues (initialLaw setup)) watcher profile
      weight nonnegative atMostOne) ((runtime setup).reportNetwork leaks watcher)
    (setup.eventInputs initial) _ final
    (EventGraphRuntime.State.initial_invariant (graph := graph setup) (setup.eventInputs initial))
    supported
  change (if final.application.config.cut.Terminal then
    decodeState? (terminalRefs setup.program) final.application.config.store else none) = _
  exact ite_eq_left settled

/-- The original source behavioral profile is preserved through the actual
history evaluators on both sides, not only through a syntactic policy law. -/
theorem compiled_profile_readout_law
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (bounds : MessageBounds (graph setup)) (watcher : Player)
    (reveals : setup.program.RevealOnly)
    (observer : ∀ event, (graph setup).actor? event ≠ some watcher)
    (openable : ∀ initial ∈ setup.initialLaw.support, initial.BindingsOpenable)
    (admission : CommitmentInterface setup.program)
    (profile : GameTheory.Profile (setup.informationModel admission).behavioralSignature)
    (weight : ℝ) (nonnegative : 0 ≤ weight) (small : weight ≤ 1) :
    ((information setup leaks (bounds.withInitialValues (initialLaw setup)) watcher).runBehavioral
      (compiledProfile setup leaks (bounds.withInitialValues (initialLaw setup)) watcher
        (setup.decodeBehavioralProfile admission profile) weight nonnegative small)
      (2 * horizon setup watcher + 1)).map (fun final => sourceReadout setup leaks final.state) =
      ((setup.informationModel admission).runBehavioral profile
        (instructionCount setup.program + 1)).map
          (fun final => setup.protocolReadout final.state) := by
  rw [compiled_behavioral_source_law setup leaks bounds watcher reveals observer openable]
  symm
  exact setup.runBehavioralFrom_readout admission profile (instructionCount setup.program + 1)
    (setup.executionProtocol admission).initHistory (Nat.le_refl _)

/-- Initial private data, all public results, and the complete utility vector
are retained jointly because they are read from the same typed terminal state. -/
theorem compiled_profile_joint_utility_law
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (bounds : MessageBounds (graph setup)) (watcher : Player)
    (reveals : setup.program.RevealOnly)
    (observer : ∀ event, (graph setup).actor? event ≠ some watcher)
    (openable : ∀ initial ∈ setup.initialLaw.support, initial.BindingsOpenable)
    (admission : CommitmentInterface setup.program)
    (profile : GameTheory.Profile (setup.informationModel admission).behavioralSignature)
    (weight : ℝ) (nonnegative : 0 ≤ weight) (small : weight ≤ 1)
    (utility : State L setup.program.terminalCtx → Player → ℝ) :
    ((information setup leaks (bounds.withInitialValues (initialLaw setup)) watcher).runBehavioral
      (compiledProfile setup leaks (bounds.withInitialValues (initialLaw setup)) watcher
        (setup.decodeBehavioralProfile admission profile) weight nonnegative small)
      (2 * horizon setup watcher + 1)).map
        (fun final => (sourceReadout setup leaks final.state,
          baseUtility setup leaks utility final.state)) =
      ((setup.informationModel admission).runBehavioral profile
        (instructionCount setup.program + 1)).map
          (fun final => (setup.protocolReadout final.state,
            fun who => (setup.protocolReadout final.state).elim 0
              (fun state => utility state who))) := by
  have law := compiled_profile_readout_law setup leaks bounds watcher reveals observer openable
    admission profile weight nonnegative small
  have mapped := congrArg (fun distribution => distribution.map
    (fun state => (state, fun who => state.elim 0 (fun current => utility current who)))) law
  unfold baseUtility
  simpa only [PMF.map_comp, Function.comp_def] using mapped

end Vegas
