/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveHiddenResponse
import Vegas.Pending.EventSampleObservation
import GameTheoryExtensions.Math.Probability.Support

/-! # Common passive samples and maintenance during a private binding repair

The same passive sample preserves the entire vector of opponents' inputs.
Clock, grant and expiry steps are deterministic, so their observation laws can
also be coupled jointly. No pending message is removed or hidden by these lemmas.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))

private theorem environment_observed_eq
    (left right : (runtime.reactiveApplication leaks).Execution)
    (network : left.network = right.network) (receipts : left.receipts = right.receipts)
    (publicEq : left.application.publicView = right.application.publicView) :
    left.observeEnvironment (runtime.reactiveApplication leaks) =
      right.observeEnvironment (runtime.reactiveApplication leaks) := by
  change ReactiveApplication.EnvironmentView.mk (app := runtime.reactiveApplication leaks)
    _ _ _ = _
  rw [network, receipts]
  exact congrArg (fun view => (⟨right.network.publicView, view, right.receipts⟩ :
    (runtime.reactiveApplication leaks).EnvironmentView)) publicEq

/-- Activation uses one common passive sample on the equal pending pool.
The sampled player may be the hidden owner; no observer restriction is needed. -/
theorem reactive_activate_hidden_congr
    (left right : (runtime.reactiveApplication leaks).Execution) (hidden actor : Player)
    (network : left.network = right.network) (receipts : left.receipts = right.receipts)
    (publicEq : left.application.publicView = right.application.publicView)
    (serviceRecall : left.environmentRecall = right.environmentRecall)
    (views : ∀ who, who ≠ hidden →
      left.application.playerView who = right.application.playerView who)
    (recall : ∀ who, who ≠ hidden → left.recall who = right.recall who) :
    let readout := fun next : (runtime.reactiveApplication leaks).Execution =>
      (next.network, next.receipts, next.environmentRecall, fun who =>
        if who = hidden then none else some (next.recall who, next.application.playerView who))
    (left.environmentStep (runtime.reactiveApplication leaks) (.activate actor)).map readout =
      (right.environmentStep (runtime.reactiveApplication leaks) (.activate actor)).map
        readout := by
  dsimp only
  have environment := environment_observed_eq runtime leaks left right network receipts publicEq
  simp only [ReactiveApplication.Execution.environmentStep, PMF.map_comp]
  rw [show left.network.pending = right.network.pending from
    congrArg MessageNetwork.pending network]
  apply map_congr_on_support _
  intro selected _
  dsimp only [Function.comp_apply]
  apply Prod.ext
  · rw [network]
  apply Prod.ext receipts
  apply Prod.ext
  · rw [environment, serviceRecall]
  funext who
  dsimp only
  split
  · rfl
  · rename_i ordinary
    exact congrArg some (Prod.ext (recall who ordinary) (views who ordinary))

private theorem maintenance_result_view
    (left right first second : State graph) (who : Player) (command : EnvironmentCommand graph)
    (maintenance : ∀ event, command ≠ .executeSample event)
    (views : left.playerView who = right.playerView who)
    (firstSupported : first ∈ (environmentStep runtime left command).support)
    (secondSupported : second ∈ (environmentStep runtime right command).support) :
    first.playerView who = second.playerView who := by
  have same := maintenance_playerView_congr runtime left right who command maintenance views
  have member : first.playerView who ∈
      ((environmentStep runtime right command).map (fun next => next.playerView who)).support := by
    rw [← same, PMF.support_map]
    exact ⟨first, firstSupported, rfl⟩
  cases command with
  | executeSample event => exact (maintenance event rfl).elim
  | grant event | advanceClock | expire event =>
      simp only [environmentStep, PMF.mem_support_pure_iff _ _] at secondSupported
      subst second
      simpa only [environmentStep, PMF.pure_map, PMF.mem_support_pure_iff _ _] using member

private theorem application_environment (state : State graph) (command : EnvironmentCommand graph) :
    (runtime.reactiveApplication leaks).environment state command =
      environmentStep runtime state command := rfl

/-- Deterministic service maintenance preserves joint opponent inputs and the
same scheduler recall. The hypothesis excludes public chance, handled by its
common-draw law, and does not make a claim about arbitrary packet inclusion. -/
theorem reactive_maintenance_hidden_congr
    (left right : (runtime.reactiveApplication leaks).Execution) (hidden : Player)
    (network : left.network = right.network) (receipts : left.receipts = right.receipts)
    (publicEq : left.application.publicView = right.application.publicView)
    (serviceRecall : left.environmentRecall = right.environmentRecall)
    (views : ∀ who, who ≠ hidden →
      left.application.playerView who = right.application.playerView who)
    (recall : ∀ who, who ≠ hidden → left.recall who = right.recall who)
    (command : EnvironmentCommand graph)
    (maintenance : ∀ event, command ≠ .executeSample event) :
    let readout := fun next : (runtime.reactiveApplication leaks).Execution =>
      (next.network, next.receipts, next.environmentRecall, fun who =>
        if who = hidden then none else some (next.recall who, next.application.playerView who))
    (left.environmentStep (runtime.reactiveApplication leaks) (.application command)).map readout =
      (right.environmentStep (runtime.reactiveApplication leaks) (.application command)).map
        readout := by
  have environment := environment_observed_eq runtime leaks left right network receipts publicEq
  have results := maintenance_result_view runtime
  dsimp only
  cases command with
  | executeSample event => exact (maintenance event rfl).elim
  | grant event | advanceClock | expire event =>
      simp only [ReactiveApplication.Execution.environmentStep, application_environment,
        environmentStep, PMF.pure_map]
      congr 1
      apply Prod.ext network
      apply Prod.ext receipts
      apply Prod.ext
      · rw [environment, serviceRecall]
      funext who
      dsimp only
      split
      · rfl
      · rename_i ordinary
        apply congrArg some
        apply Prod.ext (recall who ordinary)
        exact results left.application right.application _ _ who _ maintenance
          (views who ordinary) ((PMF.mem_support_pure_iff _ _).mpr rfl)
            ((PMF.mem_support_pure_iff _ _).mpr rfl)

/-- Actual native execution uses the same public draw on both sides; network,
receipts, service recall and every opponent's input remain jointly coupled. -/
theorem reactive_sample_hidden_congr
    (left right : (runtime.reactiveApplication leaks).Execution) (hidden : Player)
    (network : left.network = right.network) (receipts : left.receipts = right.receipts)
    (publicEq : left.application.publicView = right.application.publicView)
    (serviceRecall : left.environmentRecall = right.environmentRecall)
    (views : ∀ who, who ≠ hidden →
      left.application.playerView who = right.application.playerView who)
    (recall : ∀ who, who ≠ hidden → left.recall who = right.recall who)
    (event : graph.EventId) (leftReady : left.application.config.cut.Ready event)
    (rightReady : right.application.config.cut.Ready event)
    (payload : L.Ty) (law : EventGraph.PublicDist graph.layout payload)
    (outputEq : graph.outputLayout event = .publicData payload)
    (codeEq : cast (congrArg (EventGraph.EventCode graph.layout) outputEq)
      (graph.nodes event) = .sample payload law)
    (viewEq : nodeView graph event = .sample payload law outputEq codeEq) :
    let readout := fun next : (runtime.reactiveApplication leaks).Execution =>
      (next.network, next.receipts, next.environmentRecall, fun who =>
        if who = hidden then none else some (next.recall who, next.application.playerView who))
    (left.environmentStep (runtime.reactiveApplication leaks)
      (.application (.executeSample event))).map readout =
        (right.environmentStep (runtime.reactiveApplication leaks)
          (.application (.executeSample event))).map readout := by
  have environment := environment_observed_eq runtime leaks left right network receipts publicEq
  have sampled := environmentStep_sample_hidden_congr runtime left.application right.application
    hidden event publicEq views leftReady rightReady payload law outputEq codeEq viewEq
  dsimp only
  simp only [ReactiveApplication.Execution.environmentStep, application_environment,
    PMF.map_comp]
  rw [← PMF.bind_pure_comp, Function.comp_def, ← PMF.bind_pure_comp, Function.comp_def]
  apply bind_eq_of_map_eq _ _ _ _ sampled
  intro first _ second _ same
  apply congrArg PMF.pure
  dsimp only [Function.comp_apply]
  apply Prod.ext network
  apply Prod.ext receipts
  apply Prod.ext
  · rw [environment, serviceRecall]
  funext who
  dsimp only
  by_cases ordinary : who = hidden
  · simp only [ordinary, ↓reduceIte]
  · simp only [ordinary, ↓reduceIte]
    apply congrArg some
    apply Prod.ext (recall who ordinary)
    have observed := congrFun same who
    simpa only [ordinary, ↓reduceIte, Option.some.injEq] using observed

end Vegas.EventGraphRuntime
