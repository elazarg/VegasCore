/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.EventHonestEpoch

/-! # Honest outcome laws of the asynchronous pending-message service -/

noncomputable section

namespace Vegas.EventGraphRuntime

open GameTheory.Math.Probability Interaction Vegas.EventGraph

variable {Player : Type} [DecidableEq Player]
variable {L : IExpr} [R : IExpr.ResultTypes L]
variable {graph : Vegas.EventGraph Player L}

/-- Concrete adaptive epochs preserve both their boundary conditions and the
future semantic law. Histories and pending delivery remain in the actual run. -/
theorem runService_honest (runtime : EventGraphRuntime graph) (inputs : graph.Inputs)
    (ordered : graph.BarrierOrdered) (feasible : runtime.ServiceFeasible)
    (profile : graph.BehavioralProfile) (roster : List Player) (reactionRounds : Nat)
    (wire : runtime.application.WirePolicy) (order : runtime.ServiceOrderPolicy)
    (count : Nat) (execution : runtime.application.PolicyExecution)
    (boundary : HonestBoundary runtime inputs execution)
    (age : execution.native.application.ActivationAgeOne) :
    (runtime.runService roster reactionRounds (runtime.compileProfile profile) wire order
        count execution).bind (fun next => next.native.application.continuationLaw profile) =
      execution.native.application.continuationLaw profile ∧
    ∀ next ∈ (runtime.runService roster reactionRounds (runtime.compileProfile profile)
        wire order count execution).support,
      HonestBoundary runtime inputs next ∧ next.native.application.ActivationAgeOne := by
  induction count generalizing execution with
  | zero =>
      simp only [runService, FinDist.pure_bind, FinDist.mem_support_pure]
      exact ⟨trivial, fun next same => same ▸ ⟨boundary, age⟩⟩
  | succ count ih =>
      have epoch := runtime.serviceEpoch_honest inputs ordered feasible profile roster
        reactionRounds wire order execution boundary age
      constructor
      · rw [runService, FinDist.bind_bind]
        calc
          _ = (runtime.serviceEpoch roster reactionRounds (runtime.compileProfile profile)
                wire order execution).bind
                  (fun middle => middle.native.application.continuationLaw profile) := by
              apply FinDist.bind_congr
              intro middle member
              exact (ih middle (epoch.2 middle member).1 (epoch.2 middle member).2).1
          _ = _ := epoch.1
      · intro next member
        simp only [runService, FinDist.support_bind, Set.mem_iUnion] at member
        obtain ⟨middle, middleMem, tailMem⟩ := member
        exact (ih middle (epoch.2 middle middleMem).1 (epoch.2 middle middleMem).2).2 next tailMem

/-- At the concrete service horizon, continuation conservation becomes equality
of complete terminal semantic laws. No chronological trace equality is asserted. -/
theorem runService_honest_semantic_law (runtime : EventGraphRuntime graph)
    (ordered : graph.BarrierOrdered) (feasible : runtime.ServiceFeasible)
    (inputs : graph.Inputs) (profile : graph.BehavioralProfile)
    (roster : List Player) (reactionRounds : Nat)
    (wire : runtime.application.WirePolicy) (order : runtime.ServiceOrderPolicy) :
    (runtime.runService roster reactionRounds (runtime.compileProfile profile) wire order
      runtime.serviceEpochs
      (MessageApplication.PolicyExecution.initial runtime.application
        (MessageApplication.State.initial runtime.application (State.initial inputs)))).map
        (fun next => graph.semanticKey next.native.application.config) =
      (graph.runPolicies graph.canonicalScheduler (graph.normalizeProfile profile) inputs).map
        graph.semanticKey := by
  let initial := MessageApplication.PolicyExecution.initial runtime.application
    (MessageApplication.State.initial runtime.application (State.initial inputs))
  have boundary := runtime.initial_honestBoundary inputs
  have conserved := (runtime.runService_honest inputs ordered feasible profile roster reactionRounds
    wire order runtime.serviceEpochs initial boundary (State.initial_activationAgeOne inputs)).1
  calc
    _ = (runtime.runService roster reactionRounds (runtime.compileProfile profile) wire order
          runtime.serviceEpochs initial).bind
            (fun next => next.native.application.continuationLaw profile) := by
      rw [FinDist.map_eq_bind]
      apply FinDist.bind_congr
      intro next member
      have terminal := runtime.runService_terminal inputs roster reactionRounds
        (runtime.compileProfile profile) wire order initial next boundary.invariant member
      exact (State.continuationLaw_terminal next.native.application profile terminal).symm
    _ = initial.native.application.continuationLaw profile := conserved
    _ = graph.canonicalContinuation profile (Config.initial inputs) :=
      boundary.continuationLaw_eq runtime inputs profile initial
    _ = _ := graph.canonicalContinuation_initial profile inputs

/-- One prescribed profile serves every draw of private setup. The complete
typed terminal-store law agrees with canonical normalized graph execution. -/
theorem servicedEventGame_honest_store_law (runtime : EventGraphRuntime graph)
    (ordered : graph.BarrierOrdered) (feasible : runtime.ServiceFeasible)
    (inputs : FinDist graph.Inputs) (profile : graph.BehavioralProfile)
    (roster : List Player) (reactionRounds : Nat)
    (wire : runtime.application.WirePolicy) (order : runtime.ServiceOrderPolicy) :
    ((runtime.servicedEventGame inputs roster reactionRounds wire order).play
      (runtime.compileProfile profile)).map (fun next => next.native.application.config.store) =
      inputs.bind fun input =>
        (graph.runPolicies graph.canonicalScheduler (graph.normalizeProfile profile) input).map
          (fun config => config.store) := by
  change (inputs.bind _).map _ = _
  rw [FinDist.map_bind]
  apply FinDist.bind_congr
  intro input _
  have semanticLaw := runtime.runService_honest_semantic_law ordered feasible input profile
    roster reactionRounds wire order
  have projected := congrArg (fun measure : FinDist graph.SemanticKey =>
    measure.map fun key => key.2.1) semanticLaw
  simp only [FinDist.map_comp, Function.comp_def, semanticKey, storeRecall] at projected
  convert projected using 1
  rfl

end Vegas.EventGraphRuntime
