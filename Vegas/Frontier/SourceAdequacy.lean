import Vegas.Frontier.RoundView

/-!
# Source payoff adequacy

The event graph is source-free.  This module proves the source-facing
connection kept by the compiler certificate: at a terminal reachable graph
state, the compiled payoff projection agrees with the source payoff list
evaluated in the terminal source environment reconstructed from the graph
store.
-/

namespace Vegas

namespace ToEventGraph

open EventGraph

variable {P : Type} [DecidableEq P] {L : IExpr}

namespace BuildResult

/-- Every terminal source binding has a typed value in a reachable terminal
graph store. Hidden committed values are included: terminality means every
event node, including commits, has written its canonical field. -/
theorem sourceStoreAvailable
    (result : BuildResult P L)
    (state : ReachableConfig result.graph)
    (hterminal : Terminal result.graph state.1) :
    ∀ {name bindTy} (h : VHasVar result.terminalCtx name bindTy),
      ∃ value, Store.getAs state.1.store
        (result.terminalState.fieldOf h) bindTy.base = some value := by
  intro name bindTy h
  have hcoherent :
      StoreCoherent result.graph state.1 :=
    reachable_storeCoherent result.graphWF state.2
  rcases result.terminalState.fieldOf_spec h with
    ⟨spec, hfield, hty, _howner⟩
  have hfieldResult :
      result.graph.field? (result.terminalState.fieldOf h) = some spec := by
    simpa [BuildResult.graph, result.terminalInitialFields,
      result.terminalNodes] using hfield
  have havailable :
      result.graph.fieldAvailableBefore result.graph.nodeCount
        (result.terminalState.fieldOf h) = true := by
    simpa [BuildResult.graph, Graph.nodeCount,
      result.terminalInitialFields, result.terminalNodes] using
      result.terminalState.fieldOf_available h
  have hsourceReady :
      (match spec.source with
       | .initial _ => True
       | .event node => state.1.nodeDone node) := by
    unfold Graph.fieldAvailableBefore at havailable
    rw [hfieldResult] at havailable
    cases hsource : spec.source with
    | initial value =>
        trivial
    | event node =>
        have hlt : node < result.graph.nodeCount := by
          simpa [hsource] using havailable
        change node ∈ state.1.doneIds
        exact
          Finset.mem_image.mpr
            ⟨⟨node, hlt⟩, hterminal ⟨node, hlt⟩, rfl⟩
  rcases hcoherent
      (result.terminalState.fieldOf h) spec hfieldResult hsourceReady with
    ⟨value, hvalue⟩
  rw [← hty]
  exact ⟨value, hvalue⟩

/-- At reachable terminal graph states, the compiled payoff projection agrees
with the declared source payoff list in the reconstructed terminal source
environment. -/
theorem evalPayoffs?_eq_sourceAtTerminal
    (result : BuildResult P L)
    (state : ReachableConfig result.graph)
    (hterminal : Terminal result.graph state.1) :
    evalPayoffs? result.payoffs state.1.store =
      some
        (evalPayoffs result.sourcePayoffs
          (sourceEnvOfStore result.terminalState state.1.store
            (result.sourceStoreAvailable state hterminal))) := by
  rw [result.payoffs_eq]
  exact
    evalPayoffs?_compilePayoffs_eq_sourceEnvOfStore
      result.terminalState result.sourcePayoffs state.1.store
      (result.sourceStoreAvailable state hterminal)

end BuildResult

private theorem pmf_map_congr_of_eq_on_support
    {α β : Type*} {dist : PMF α} {f g : α → β}
    (h : ∀ a, a ∈ dist.support → f a = g a) :
    PMF.map f dist = PMF.map g dist := by
  apply PMF.ext
  intro b
  rw [PMF.map_apply, PMF.map_apply]
  apply tsum_congr
  intro a
  by_cases ha : a ∈ dist.support
  · rw [h a ha]
  · have hzero : dist a = 0 :=
      (PMF.apply_eq_zero_iff dist a).2 ha
    simp [hzero]

/-- Terminal source environment reconstructed from a reachable terminal
compiled graph state. -/
noncomputable def sourceEnvAtTerminal
    (g : GraphProgram P L)
    (state : ReachableConfig (compile g).graph)
    (hterminal : Terminal (compile g).graph state.1) :
    VEnv L (buildResult g).terminalCtx :=
  sourceEnvOfStore (buildResult g).terminalState state.1.store
    (by
      intro name bindTy h
      simpa [compile, buildResult, BuildResult.graph] using
        (buildResult g).sourceStoreAvailable state hterminal h)

/-- Source payoff outcome at a reachable terminal compiled graph state. -/
noncomputable def sourceOutcomeAtTerminal
    (g : GraphProgram P L)
    (state : ReachableConfig (compile g).graph)
    (hterminal : Terminal (compile g).graph state.1) : Outcome P :=
  evalPayoffs (buildResult g).sourcePayoffs
    (sourceEnvAtTerminal g state hterminal)

/-- Source payoff projection for a completed frontier history.  The `none`
branch is kept explicit for arbitrary histories; completed run distributions
put no mass on it. -/
noncomputable def sourceOutcomeOptionAtHistory
    (g : GraphProgram P L)
    {view : (PrimitiveMachine (compile g)).RoundView}
    (history : view.BoundedHistory (completionBound (compile g))) :
    Option (Outcome P) := by
  classical
  exact
    if hterminal :
        Terminal (compile g).graph history.lastState.state.1 then
      some (sourceOutcomeAtTerminal g history.lastState.state hterminal)
    else
      none

/-- Source payoff projection for an event-batch trace of the primitive
compiled machine.  This is the trace-level analogue of
`sourceOutcomeOptionAtHistory`: nonterminal bounded traces have no source
outcome yet. -/
noncomputable def sourceOutcomeOptionAtTrace
    (g : GraphProgram P L)
    (trace : (PrimitiveMachine (compile g)).EventBatchTrace) :
    Option (Outcome P) := by
  classical
  exact
    if hterminal :
        Terminal (compile g).graph trace.2.1 then
      some (sourceOutcomeAtTerminal g trace.2 hterminal)
    else
      none

/-- Source adequacy for the public `compile` entry point.  The source
environment is reconstructed using the compiler certificate `buildResult`;
the compiled semantic object itself remains source-free. -/
theorem compile_evalPayoffs?_eq_sourceAtTerminal
    (g : GraphProgram P L)
    (state : ReachableConfig (compile g).graph)
    (hterminal : Terminal (compile g).graph state.1) :
    evalPayoffs? (compile g).payoffs state.1.store =
      some (sourceOutcomeAtTerminal g state hterminal) := by
  simpa [compile, buildResult, BuildResult.graph,
    sourceOutcomeAtTerminal, sourceEnvAtTerminal] using
    (buildResult g).evalPayoffs?_eq_sourceAtTerminal state hterminal

/-- Source adequacy at the primitive machine outcome surface. -/
theorem compile_primitiveMachine_outcome_eq_sourceAtTerminal
    (g : GraphProgram P L)
    (state : (PrimitiveMachine (compile g)).State)
    (hterminal : (PrimitiveMachine (compile g)).terminal state) :
    (PrimitiveMachine (compile g)).outcome state =
      some (sourceOutcomeAtTerminal g state
        (by simpa [PrimitiveMachine, primitiveMachineSpec] using hterminal)) := by
  have hterminalGraph :
      Terminal (compile g).graph state.1 := by
    simpa [PrimitiveMachine, primitiveMachineSpec] using hterminal
  have hprojection :=
    EventGraph.ToMachine.primitiveMachine_outcome_terminal
      (primitiveMachineSpec (compile g)) hterminal
  rw [hprojection]
  exact compile_evalPayoffs?_eq_sourceAtTerminal g state hterminalGraph

/-- Primitive-machine trace outcomes agree with the source payoff projection
on terminal traces and are both absent on nonterminal traces. -/
theorem compile_primitiveMachine_outcome_eq_sourceTrace
    (g : GraphProgram P L)
    (trace : (PrimitiveMachine (compile g)).EventBatchTrace) :
    (PrimitiveMachine (compile g)).outcome trace.2 =
      sourceOutcomeOptionAtTrace g trace := by
  classical
  unfold sourceOutcomeOptionAtTrace
  by_cases hterminal : Terminal (compile g).graph trace.2.1
  · rw [dif_pos hterminal]
    exact
      compile_primitiveMachine_outcome_eq_sourceAtTerminal
        g trace.2
        (by simpa [PrimitiveMachine, primitiveMachineSpec] using hterminal)
  · rw [dif_neg hterminal]
    change
      (EventGraph.ToMachine.primitiveMachine
        (primitiveMachineSpec (compile g))).outcome trace.2 = none
    unfold EventGraph.ToMachine.primitiveMachine
    simp [hterminal]

section Completed

variable [Fintype P]
variable {program : WFProgram P L}
variable {presentation :
  EventGraph.CheckpointPresentation (compile program.core).graph}

/-- Every supported concrete outcome of a completed pure frontier game is the
declared source payoff outcome at the terminal graph state of some supported
frontier history. -/
theorem CompletedFrontierPureKernelGame.outcomeKernel_support_sourceOutcome
    (completed :
      CompletedFrontierPureKernelGame (compile program.core) presentation)
    (σ : completed.game.Profile)
    {outcome : (PrimitiveMachine (compile program.core)).Outcome}
    (hsupport : outcome ∈ (completed.game.outcomeKernel σ).support) :
    ∃ history : (completed.view).BoundedHistory
        (completionBound (compile program.core)),
      ∃ hterminal :
        Terminal (compile program.core).graph history.lastState.state.1,
        history ∈
          ((completed.view).runDist
            (completionBound (compile program.core))
            (completionBound (compile program.core))
            ((completed.view).legalPureToBehavioral
              (completionBound (compile program.core)) σ)).support ∧
        outcome =
          sourceOutcomeAtTerminal program.core
            history.lastState.state hterminal ∧
        (PrimitiveMachine (compile program.core)).AvailableRunBatchesFrom
          ((Machine.BoundedState.init
            (PrimitiveMachine (compile program.core))
            (completionBound (compile program.core))).state)
          ((completed.view).boundedHistoryEventBatches
            (completionBound (compile program.core)) history)
          history.lastState.state := by
  rcases completed.outcomeKernel_support_history σ hsupport with
    ⟨history, hhistory, hterminal, hprimitive, hrun⟩
  have hsource :
      (PrimitiveMachine (compile program.core)).outcome
          history.lastState.state =
        some
          (sourceOutcomeAtTerminal program.core
            history.lastState.state hterminal) := by
    exact
      compile_primitiveMachine_outcome_eq_sourceAtTerminal
        program.core history.lastState.state
        (by simpa [PrimitiveMachine, primitiveMachineSpec] using hterminal)
  have houtcome :
      outcome =
        sourceOutcomeAtTerminal program.core
          history.lastState.state hterminal :=
    Option.some.inj (hprimitive.symm.trans hsource)
  exact ⟨history, hterminal, hhistory, houtcome, hrun⟩

/-- The option-valued completed pure frontier kernel is exactly the run
distribution pushed forward through the source payoff projection. -/
theorem CompletedFrontierPureKernelGame.optionOutcomeKernel_eq_sourceMap
    (completed :
      CompletedFrontierPureKernelGame (compile program.core) presentation)
    (σ : completed.game.Profile) :
    completed.optionOutcomeKernel σ =
      PMF.map
        (sourceOutcomeOptionAtHistory program.core)
        ((completed.view).runDist
          (completionBound (compile program.core))
          (completionBound (compile program.core))
          ((completed.view).legalPureToBehavioral
            (completionBound (compile program.core)) σ)) := by
  classical
  letI :
      ∀ player,
        Fintype
          (Option
            ((frontierRoundView
              (compile program.core) presentation completed.semantics).Act
              player)) := by
    intro player
    letI :
        ∀ node : Fin (compile program.core).graph.nodeCount,
          Fintype (L.Val ((compile program.core).graph.nodeRow node).ty) :=
      completed.nodeFintype
    dsimp [CompletedFrontierPureKernelGame.view, frontierRoundView,
      EventGraph.frontierRoundView]
    infer_instance
  change
    (completed.view).boundedOutcomeFromPure
        (completionBound (compile program.core)) σ
        (completionBound (compile program.core)) =
      PMF.map
        (sourceOutcomeOptionAtHistory program.core)
        ((completed.view).runDist
          (completionBound (compile program.core))
          (completionBound (compile program.core))
          ((completed.view).legalPureToBehavioral
            (completionBound (compile program.core)) σ))
  rw [Machine.RoundView.boundedOutcomeFromPure,
    Machine.RoundView.boundedEventBatchTraceFromPure,
    Machine.RoundView.boundedEventBatchTraceFromBehavioral]
  rw [PMF.map_comp]
  apply pmf_map_congr_of_eq_on_support
  intro history hhistory
  have hterminal :
      Terminal (compile program.core).graph history.lastState.state.1 :=
    FrontierRoundSemantics.runDist_support_terminal_of_completionBound
      completed.semantics
      ((completed.view).legalPureToBehavioral
        (completionBound (compile program.core)) σ)
      hhistory
  have houtcome :
      (PrimitiveMachine (compile program.core)).outcome
          history.lastState.state =
        some
          (sourceOutcomeAtTerminal program.core
            history.lastState.state hterminal) :=
    compile_primitiveMachine_outcome_eq_sourceAtTerminal
      program.core history.lastState.state
      (by simpa [PrimitiveMachine, primitiveMachineSpec] using hterminal)
  change
    (PrimitiveMachine (compile program.core)).outcome
        history.lastState.state =
      sourceOutcomeOptionAtHistory program.core history
  rw [houtcome, sourceOutcomeOptionAtHistory, dif_pos hterminal]

/-- Every supported concrete outcome of a completed behavioral frontier game
is the declared source payoff outcome at the terminal graph state of some
supported frontier history. -/
theorem
    CompletedFrontierBehavioralKernelGame.outcomeKernel_support_sourceOutcome
    (completed :
      CompletedFrontierBehavioralKernelGame
        (compile program.core) presentation)
    (σ : completed.game.Profile)
    {outcome : (PrimitiveMachine (compile program.core)).Outcome}
    (hsupport : outcome ∈ (completed.game.outcomeKernel σ).support) :
    ∃ history : (completed.view).BoundedHistory
        (completionBound (compile program.core)),
      ∃ hterminal :
        Terminal (compile program.core).graph history.lastState.state.1,
        history ∈
          ((completed.view).runDist
            (completionBound (compile program.core))
            (completionBound (compile program.core)) σ).support ∧
        outcome =
          sourceOutcomeAtTerminal program.core
            history.lastState.state hterminal ∧
        (PrimitiveMachine (compile program.core)).AvailableRunBatchesFrom
          ((Machine.BoundedState.init
            (PrimitiveMachine (compile program.core))
            (completionBound (compile program.core))).state)
          ((completed.view).boundedHistoryEventBatches
            (completionBound (compile program.core)) history)
          history.lastState.state := by
  rcases completed.outcomeKernel_support_history σ hsupport with
    ⟨history, hhistory, hterminal, hprimitive, hrun⟩
  have hsource :
      (PrimitiveMachine (compile program.core)).outcome
          history.lastState.state =
        some
          (sourceOutcomeAtTerminal program.core
            history.lastState.state hterminal) := by
    exact
      compile_primitiveMachine_outcome_eq_sourceAtTerminal
        program.core history.lastState.state
        (by simpa [PrimitiveMachine, primitiveMachineSpec] using hterminal)
  have houtcome :
      outcome =
        sourceOutcomeAtTerminal program.core
          history.lastState.state hterminal :=
    Option.some.inj (hprimitive.symm.trans hsource)
  exact ⟨history, hterminal, hhistory, houtcome, hrun⟩

/-- The option-valued completed behavioral frontier kernel is exactly the run
distribution pushed forward through the source payoff projection. -/
theorem
    CompletedFrontierBehavioralKernelGame.optionOutcomeKernel_eq_sourceMap
    (completed :
      CompletedFrontierBehavioralKernelGame
        (compile program.core) presentation)
    (σ : completed.game.Profile) :
    completed.optionOutcomeKernel σ =
      PMF.map
        (sourceOutcomeOptionAtHistory program.core)
        ((completed.view).runDist
          (completionBound (compile program.core))
          (completionBound (compile program.core)) σ) := by
  classical
  letI :
      ∀ player,
        Fintype
          (Option
            ((frontierRoundView
              (compile program.core) presentation completed.semantics).Act
              player)) := by
    intro player
    letI :
        ∀ node : Fin (compile program.core).graph.nodeCount,
          Fintype (L.Val ((compile program.core).graph.nodeRow node).ty) :=
      completed.nodeFintype
    dsimp [CompletedFrontierBehavioralKernelGame.view, frontierRoundView,
      EventGraph.frontierRoundView]
    infer_instance
  change
    (completed.view).boundedOutcomeFromBehavioral
        (completionBound (compile program.core)) σ
        (completionBound (compile program.core)) =
      PMF.map
        (sourceOutcomeOptionAtHistory program.core)
        ((completed.view).runDist
          (completionBound (compile program.core))
          (completionBound (compile program.core)) σ)
  rw [Machine.RoundView.boundedOutcomeFromBehavioral,
    Machine.RoundView.boundedEventBatchTraceFromBehavioral]
  rw [PMF.map_comp]
  apply pmf_map_congr_of_eq_on_support
  intro history hhistory
  have hterminal :
      Terminal (compile program.core).graph history.lastState.state.1 :=
    FrontierRoundSemantics.runDist_support_terminal_of_completionBound
      completed.semantics σ hhistory
  have houtcome :
      (PrimitiveMachine (compile program.core)).outcome
          history.lastState.state =
        some
          (sourceOutcomeAtTerminal program.core
            history.lastState.state hterminal) :=
    compile_primitiveMachine_outcome_eq_sourceAtTerminal
      program.core history.lastState.state
      (by simpa [PrimitiveMachine, primitiveMachineSpec] using hterminal)
  change
    (PrimitiveMachine (compile program.core)).outcome
        history.lastState.state =
      sourceOutcomeOptionAtHistory program.core history
  rw [houtcome, sourceOutcomeOptionAtHistory, dif_pos hterminal]

end Completed

end ToEventGraph

end Vegas
