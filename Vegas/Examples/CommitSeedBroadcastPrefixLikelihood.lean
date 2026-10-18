/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedBroadcastAllGoodTarget
import Interaction.ReactiveMenuLikelihood
import Interaction.ReactiveResponseEvaluation
import GameTheoryExtensions.Analysis.Protocol.ContinuationOwnPlay
import GameTheoryExtensions.Analysis.Protocol.OwnPlayReach

/-! # Exact native chance coefficients and retained-response likelihoods -/

noncomputable section

namespace Vegas.Examples.CommitSeedBroadcast

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

private theorem no_public_sample (event : graph.EventId) (payload : simpleExpr.Ty) :
    graph.outputLayout event ≠ .publicData payload := by
  fin_cases event <;> intro impossible <;> cases impossible

/-- The concrete Boolean source has no sampled event; even an arbitrary raw
environment command has one literal native successor. -/
theorem native_environment_pure (state : app.State) (command : app.EnvironmentCommand) :
    ∃ next, app.environment state command = PMF.pure next := by
  change ∃ next, PhaseRuntimeState.environment runtime state command = PMF.pure next
  unfold PhaseRuntimeState.environment
  split
  · cases command with
    | advanceClock => exact ⟨_, PMF.pure_map ..⟩
    | expire event => exact ⟨_, PMF.pure_map ..⟩
    | executeSample event =>
        have sampled : environmentStep runtime state.current.native (.executeSample event) =
            PMF.pure state.current.native := by
          by_cases ready : state.current.native.config.cut.Ready event
          · apply environmentStep_executeSample_of_nonsample runtime _ event ready
            intro payload law outputEq codeEq _same
            exact (no_public_sample event payload outputEq).elim
          · exact environmentStep_executeSample_of_not_ready runtime _ event ready
        rw [sampled]
        exact ⟨_, PMF.pure_map ..⟩
  · exact ⟨state, rfl⟩

theorem native_environmentStep_pure (execution : app.Execution) (command : app.Command) :
    ∃ next, execution.environmentStep app command = PMF.pure next := by
  cases command with
  | activate owner => exact ⟨completeActivation execution owner, completeActivation_law ..⟩
  | wait => exact ⟨_, PMF.pure_map ..⟩
  | «include» identifier => exact ⟨_, PMF.pure_map ..⟩
  | application command =>
      obtain ⟨next, law⟩ := native_environment_pure execution.application command
      simp only [ReactiveApplication.Execution.environmentStep, law, PMF.pure_map]
      exact ⟨_, rfl⟩

theorem family_transition_pure (seed : Seeds) (state : app.ProtocolState)
    (joint : Player → Option app.Action) :
    ∃ next, app.transition initial horizon (family seed) state joint = PMF.pure next := by
  cases state with
  | none => exact ⟨_, PMF.pure_map ..⟩
  | some control =>
      rcases control with ⟨remaining, actor, execution⟩
      cases actor with
      | some owner => exact ⟨_, rfl⟩
      | none =>
          cases remaining with
          | zero => exact ⟨_, rfl⟩
          | succ remaining =>
              obtain ⟨next, law⟩ := native_environmentStep_pure execution
                (choose seed execution.environmentRecall (execution.observeEnvironment app))
              simp only [ReactiveApplication.transition, family, PMF.pure_bind, law,
                PMF.pure_map]
              exact ⟨_, rfl⟩

theorem family_transition_atom (seed : Seeds) (before after : app.ProtocolState)
    (joint : Player → Option app.Action)
    (reached : after ∈ (app.transition initial horizon (family seed) before joint).support) :
    ((app.transition initial horizon (family seed) before joint) after).toReal = 1 := by
  obtain ⟨next, law⟩ := family_transition_pure seed before joint
  rw [law, PMF.mem_support_pure_iff] at reached
  subst after
  rw [law, PMF.pure_apply_self, ENNReal.toReal_one]

/-- The initial state, private observation sample and every physical command
have unit realized chance coefficient under the original fixed seed. -/
theorem family_trace_transitionMass (seed : Seeds) {state : app.ProtocolState}
    (trace : (app.protocol initial horizon (family seed)).Trace state) :
    trace.transitionMass = 1 := by
  refine Trace.rec (motive := fun _ past => past.transitionMass = 1) ?_ ?_ trace
  · rfl
  · intro before after prior joint legal reached ih
    rw [Trace.transitionMass_extend, ih]
    exact one_mul _ |>.trans (family_transition_atom seed before after joint reached)

theorem family_history_ownPlay_factor (seed : Seeds)
    (profile : ∀ owner, (app.information initial horizon (family seed)).BehavioralPolicy owner)
    {state : app.ProtocolState}
    (trace : (app.protocol initial horizon (family seed)).Trace state) :
    ((app.information initial horizon (family seed)).historyReachWeight profile
      ⟨state, trace⟩).toReal =
      ∏ owner, (app.information initial horizon (family seed)).ownPlayReachProbability
        (profile owner) ((app.information initial horizon (family seed)).ownPlay owner trace) := by
  let model := app.information initial horizon (family seed)
  obtain ⟨records, recordsEq, _provenance, chance, _nonnegative, chanceEq, factor⟩ :=
    model.exists_continuation_ownPlay_factor (.start :
      (app.protocol initial horizon (family seed)).Trace none) trace (TracePrefix.start trace)
  have chanceOne : chance = 1 := by
    simpa only [Trace.transitionMass_start, mul_one, family_trace_transitionMass] using chanceEq
  have recordsSame (owner : Player) : records owner = model.ownPlay owner trace := by
    simpa only [InfoSignals.ownPlay, List.append_nil] using (recordsEq owner).symm
  have evaluated := factor profile
  rw [chanceOne, one_mul] at evaluated
  simp_rw [recordsSame] at evaluated
  simpa only [InformationModel.historyReachWeight, InformationModel.runBehavioral,
    Trace.length, Nat.sub_zero, initHistory] using evaluated

/-- This is the existing canonical own-action product, evaluated on the
complete original native recall rather than on a refreshed local history. -/
def nativeResponseLikelihood (players : Player → app.Policy)
    (execution : app.Execution) : ℝ :=
  ∏ owner, (app.information initial horizon scheduler).ownPlayReachProbability
    (who := owner) (app.encodePolicy (players owner)) (app.recallOwnPlay (execution.recall owner))

theorem family_history_response_factor (seed : Seeds) (players : Player → app.Policy)
    (control : app.Control)
    (trace : (app.protocol initial horizon (family seed)).Trace (some control)) :
    ((app.information initial horizon (family seed)).historyReachWeight
      (fun owner => app.encodePolicy (players owner)) ⟨some control, trace⟩).toReal =
      nativeResponseLikelihood players control.execution := by
  rw [family_history_ownPlay_factor]
  unfold nativeResponseLikelihood
  apply Finset.prod_congr rfl
  intro owner _member
  have words : (app.information initial horizon (family seed)).ownPlay owner trace =
      app.recallOwnPlay (control.execution.recall owner) :=
    app.trace_ownPlay initial horizon (family seed) owner trace
  rw [words]
  have common (records : List (app.Info × app.Action)) :
      (app.information initial horizon (family seed)).ownPlayReachProbability
        (who := owner) (app.encodePolicy (players owner)) records =
      (app.information initial horizon scheduler).ownPlayReachProbability
        (who := owner) (app.encodePolicy (players owner)) records := by
    induction records with
    | nil => rfl
    | cons entry prior ih =>
        simp only [InformationModel.ownPlayReachProbability, ih]
        rfl
  exact common _

/-- Embedding the actual finite raw menu preserves its complete history atom.
There is no command-normalization factor hidden in the response product. -/
theorem family_menu_history_response_factor (seed : Seeds)
    (profile : ∀ owner,
      (rawMenu.information initial horizon (family seed)).BehavioralPolicy owner)
    (control : app.Control)
    (trace : (rawMenu.protocol initial horizon (family seed)).Trace (some control)) :
    ((rawMenu.information initial horizon (family seed)).historyReachWeight profile
      ⟨some control, trace⟩).toReal =
      nativeResponseLikelihood
        (rawMenu.decodeProfile initial horizon (family seed) profile) control.execution := by
  let model := rawMenu.information initial horizon (family seed)
  let history : (rawMenu.protocol initial horizon (family seed)).History := ⟨some control, trace⟩
  have law := rawMenu.run_embed initial horizon (family seed) profile trace.length
    (rawMenu.protocol initial horizon (family seed)).initHistory
  have atom := congrArg (fun distribution : PMF
      (app.protocol initial horizon (family seed)).History =>
        distribution (rawMenu.toRawHistory initial horizon (family seed) history)) law
  rw [pmf_map_apply_of_injective _ (rawMenu.toRawHistory_injective initial horizon
    (family seed))] at atom
  have initialHistory : rawMenu.toRawHistory initial horizon (family seed)
      (rawMenu.protocol initial horizon (family seed)).initHistory =
        (app.protocol initial horizon (family seed)).initHistory := by rfl
  rw [initialHistory] at atom
  have embedded : (fun owner => app.encodePolicy
      (rawMenu.decodeProfile initial horizon (family seed) profile owner)) =
      fun owner => rawMenu.embedPolicy initial horizon (family seed) owner (profile owner) := by
    funext owner
    exact app.encode_decodePolicy _
  have exactNative := family_history_response_factor seed
    (rawMenu.decodeProfile initial horizon (family seed) profile) control
      (rawMenu.toRawTrace initial horizon (family seed) trace)
  rw [embedded] at exactNative
  have exactMenu : (model.historyReachWeight profile history).toReal =
      ((app.information initial horizon (family seed)).historyReachWeight
        (fun owner => rawMenu.embedPolicy initial horizon (family seed) owner (profile owner))
          (rawMenu.toRawHistory initial horizon (family seed) history)).toReal := by
    simpa only [model, history, InformationModel.historyReachWeight,
      InformationModel.runBehavioral, initHistory,
      ReactiveApplication.ResponseMenu.toRawTrace_length,
      ReactiveApplication.ResponseMenu.toRawHistory,
      ReactiveApplication.ResponseMenu.toRawTrace] using congrArg ENNReal.toReal atom
  exact exactMenu.trans exactNative

end Vegas.Examples.CommitSeedBroadcast
