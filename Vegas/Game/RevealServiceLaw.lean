/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.RevealServiceExecution

/-! # Initialized law of the actual revelation compiler

The finite alphabet is fixed from the setup law. Arbitrarily correlated private
draws and all source withholding decisions are retained. The result uses the
existing native service evaluator and its actual normalized response compiler.
-/

noncomputable section

namespace Vegas.SourceProgram.RevealService

open GameTheory.Math.Probability Interaction EventGraphRuntime EventLowering

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
  rw [initialLaw, FinDist.bind_map, FinDist.map_bind, Setup.run, FinDist.map_bind]
  apply FinDist.bind_congr
  intro initial supported
  have current := run_source_suffix_option_law setup leaks bounds watcher observer profile players
    watcherPolicy ordinary projects initial supported setup.program reveals profile
    (setup.initialConfig initial) (ContextRefs.initial setup.context (outputLayout setup.program))
    (outputEmbedding setup.program) (initialRefsBefore setup.program) 0
    (CompiledPolicySuffix.whole setup.program profile)
    (ReactiveApplication.Execution.initial (application setup leaks)
      (EventGraphRuntime.State.initial (graph := graph setup) (setup.eventInputs initial)))
    (checkpoint_initial setup leaks initial (openable initial supported))
  exact current

end Vegas.SourceProgram.RevealService
