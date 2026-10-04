/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.PrivateResolutionForkBobCompiler
import Vegas.Examples.PrivateResolutionForkCompletionBounds
import Vegas.Examples.PrivateResolutionForkTrueResource
import Vegas.EventGraph.SampleProvenance

/-! # Bob's actual typed source observation

Semantic graph reachability fixes both chance outputs at TRUE. At Bob's
ready turn, the completed cut excludes all earlier own graph actions.
An actual successful Alice output and persistent initialized inputs then
identify the literal compiler observation without a source-policy premise.
-/

noncomputable section

namespace Vegas.PrivateResolutionFork

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Math.Probability
open GameTheory.Protocol

private def firstSampleLaw : PublicDist nativeGraph.layout BaseTy.bool :=
  compilePublicDist (ContextRefs.initial setup.context (outputLayout setup.program))
    (.weighted (.pure true))

private def secondSampleLaw : PublicDist nativeGraph.layout BaseTy.bool :=
  compilePublicDist
    (((ContextRefs.initial setup.context (outputLayout setup.program)).cons
      (outputRef setup.program sample0)) :
        ContextRefs nativeGraph.layout ((2, .publicData .bool) :: initialCtx))
          (.weighted (.pure true))

private theorem firstSampleLaw_eval (store : Store nativeGraph.layout) :
    firstSampleLaw.eval? store = some (PMF.pure true) := by
  change some (RationalLaw.pure true).denote = some (PMF.pure true)
  rw [RationalLaw.denote_pure]

private theorem secondSampleLaw_eval (store : Store nativeGraph.layout) :
    secondSampleLaw.eval? store = some (PMF.pure true) := by
  change some (RationalLaw.pure true).denote = some (PMF.pure true)
  rw [RationalLaw.denote_pure]

theorem sample_outputs_true {inputs : nativeGraph.Inputs} {config : nativeGraph.Config}
    (reachable : config.Reachable inputs)
    (ordered : config.cut.IsPrefix 3) :
    (outputRef setup.program sample0).get? config.store = some true ∧
      (outputRef setup.program sample1).get? config.store = some true := by
  have first := reachable.constant_sample_output sample0 BaseTy.bool firstSampleLaw rfl rfl
    (PMF.pure true) firstSampleLaw_eval ((ordered.2 sample0).mpr (by decide))
  have second := reachable.constant_sample_output sample1 BaseTy.bool secondSampleLaw rfl rfl
    (PMF.pure true) secondSampleLaw_eval ((ordered.2 sample1).mpr (by decide))
  obtain ⟨firstValue, firstChosen, firstStored⟩ := first
  obtain ⟨secondValue, secondChosen, secondStored⟩ := second
  cases (PMF.mem_support_pure_iff _ _).mp firstChosen
  cases (PMF.mem_support_pure_iff _ _).mp secondChosen
  exact ⟨firstStored, secondStored⟩

theorem bob_own_completions_empty (config : nativeGraph.Config)
    (ordered : config.cut.IsPrefix 3) :
    nativeGraph.ownCompletions bob config.history = [] := by
  apply List.filter_eq_nil_iff.mpr
  intro completion present
  have completed := (config.history_exact completion.event).mp
    (List.mem_map_of_mem (f := Completion.event) present)
  have earlier := (ordered.2 completion.event).mp completed
  obtain ⟨event, action⟩ := completion
  change Fin 4 at event
  have absent : nativeGraph.actor? event ≠ some bob := by
    fin_cases event
    · change none ≠ some bob
      decide
    · change none ≠ some bob
      decide
    · change some alice ≠ some bob
      decide
    · change 3 < 3 at earlier
      omega
  simp [absent]

theorem bob_prefix_at_active_turn (control : app.Control)
    (trace : (app.protocol (initialLaw setup) horizon scheduler).Trace (some control))
    (active : control.actor = some bob) :
    control.execution.application.config.cut.IsPrefix 3 := by
  obtain ⟨rank, _, _, ordered⟩ := (completionBounds_history trace).ordered
  have ready := bob_raw_ready control trace active
  have atRank := (ready_iff_rank setup _ rank ordered bobResolution).mp ready
  change 3 = rank at atRank
  subst rank
  exact ordered

theorem bob_compiler_observation_of_history (control : app.Control)
    (trace : (app.protocol (initialLaw setup) horizon scheduler).Trace (some control))
    (active : control.actor = some bob)
    (published : (outputRef setup.program aliceResolution).get?
      control.execution.application.config.store = some (.success unitValue)) :
    ∃ high : Bool,
      decodeObservation? bob bobRefs
        ((graph setup).playerStore bob control.execution.application.config.store) =
          some (sourceObserve bob (sourceAliceDone high true).state) ∧
      decodeCompletions setup.program
        ((setup.eventGraph.fromModeObservation .sequential bob
          ((graph setup).playerObserve bob control.execution.application.config)).ownActions) =
            [] := by
  have initialized : initialLaw setup =
      (setup.initialLaw.map setup.eventInputs).map
        (EventGraphRuntime.State.initial (graph := graph setup)) := by
    rw [PMF.map_comp]
    rfl
  have raw := trace
  rw [initialized] at raw
  obtain ⟨inputs, selected, reachable⟩ := (runtime setup).reactive_history_graph_reachable leaks
    (setup.initialLaw.map setup.eventInputs) horizon scheduler raw
  obtain ⟨initial, chosen, rfl⟩ := PMF.support_map .. ▸ selected
  change initial ∈ (mix (1 / 4) (by norm_num) (by norm_num)
    (PMF.pure (sourceInitial true)) (PMF.pure (sourceInitial false))).support at chosen
  have initializedType : ∃ high, initial = sourceInitial high := by
    rcases support_mix_subset _ _ _ _ _ chosen with high | low
    · exact ⟨true, (PMF.mem_support_pure_iff _ _).mp high⟩
    · exact ⟨false, (PMF.mem_support_pure_iff _ _).mp low⟩
  obtain ⟨high, rfl⟩ := initializedType
  have ordered := bob_prefix_at_active_turn control trace active
  obtain ⟨first, second⟩ := sample_outputs_true reachable ordered
  have initialAgree : (ContextRefs.initial setup.context (outputLayout setup.program)).Agrees
      (sourceInitial high) control.execution.application.config.store := by
    apply ContextRefs.initial_agrees
    intro input
    change some (control.execution.application.config.inputs input) =
      some (encodeInputs (sourceInitial high) input)
    rw [reachable.inputs_eq]
    rfl
  have agrees : bobRefs.Agrees (sourceAliceDone high true).state
      control.execution.application.config.store := by
    intro name cell selected
    cases selected with
    | here => exact published
    | there selected => cases selected with
      | here => exact second
      | there selected => cases selected with
        | here => exact first
        | there selected => exact initialAgree selected
  refine ⟨high, decodeObservation?_playerStore_eq_some (graph := graph setup) bobRefs bob
    (sourceAliceDone high true).state _ agrees, ?_⟩
  have empty := bob_own_completions_empty control.execution.application.config ordered
  change decodeCompletions setup.program
    ((nativeGraph.ownCompletions bob control.execution.application.config.history).map
      (setup.eventGraph.fromModeCompletion .sequential)) = []
  rw [empty]
  rfl

end Vegas.PrivateResolutionFork
