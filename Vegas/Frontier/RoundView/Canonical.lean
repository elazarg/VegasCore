/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Frontier.RoundView.InternalClosure

/-!
# Canonical frontier round semantics and kernel-game definitions

The frontier round-step certificate, the primitive-downset and frontier
checkpoint presentations, the canonical frontier round semantics, and the
pure/behavioral frontier kernel-game definitions and program constructors.
-/

namespace Vegas

namespace ToEventGraph

open GameTheory

variable {P : Type} [DecidableEq P] [Fintype P] {L : IExpr}

/-- Certificate attached to one supported frontier-round transition. -/
abbrev FrontierRoundStepCertificate
    (compiled : CompiledProgram P L)
    (presentation : EventGraph.CheckpointPresentation compiled.graph)
    {state : (PrimitiveMachine compiled).State}
    (action :
      {a : JointAction (FrontierAct compiled) //
        JointActionLegal (FrontierAct compiled)
          (frontierActive compiled)
          (PrimitiveMachine compiled).terminal
          (frontierAvailableActions compiled) state a})
    (dst : (PrimitiveMachine compiled).State)
    (batch : List (PrimitiveMachine compiled).Event) : Prop :=
  EventGraph.FrontierRoundStepCertificate
    (primitiveMachineSpec compiled) presentation action dst batch

/-- Strategic semantics for one frontier round under a checkpoint
presentation. -/
abbrev FrontierRoundSemantics (compiled : CompiledProgram P L)
    (presentation : EventGraph.CheckpointPresentation compiled.graph) : Type :=
  EventGraph.FrontierRoundSemantics
    (primitiveMachineSpec compiled) presentation

/-- Native machine round view induced by canonical graph frontiers and an
explicit frontier-round operational semantics. -/
noncomputable def frontierRoundView
    (compiled : CompiledProgram P L)
    (presentation : EventGraph.CheckpointPresentation compiled.graph)
    (semantics : FrontierRoundSemantics compiled presentation) :
    (PrimitiveMachine compiled).RoundView :=
  EventGraph.frontierRoundView
    (primitiveMachineSpec compiled) presentation semantics

/-- Primitive downset checkpoint presentation induced by compiled graph
well-formedness and graph guard liveness. -/
noncomputable def primitiveDownsetPresentation
    (compiled : CompiledProgram P L)
    (guards : EventGraph.GuardLive compiled.graph) :
    EventGraph.CheckpointPresentation compiled.graph :=
  EventGraph.primitiveDownsetCheckpointPresentation compiled.graph
    (EventGraph.primitiveDownsetProgress_of_availableEventProgress
      (EventGraph.availableEventProgress_of_guardLive
        compiled.graphWF guards))

private noncomputable def selectedCommitDestination
    (compiled : CompiledProgram P L)
    {state : (PrimitiveMachine compiled).State}
    (action :
      {a : JointAction (FrontierAct compiled) //
        JointActionLegal (FrontierAct compiled)
          (frontierActive compiled)
          (PrimitiveMachine compiled).terminal
          (frontierAvailableActions compiled) state a})
    (hactive : (frontierActive compiled state).Nonempty) :
    (PrimitiveMachine compiled).State :=
  Classical.choose
    (selectedCommitEvents_primitiveDownset_allowed_of_active
      compiled action.2 hactive)

private theorem selectedCommitDestination_spec
    (compiled : CompiledProgram P L)
    {state : (PrimitiveMachine compiled).State}
    (action :
      {a : JointAction (FrontierAct compiled) //
        JointActionLegal (FrontierAct compiled)
          (frontierActive compiled)
          (PrimitiveMachine compiled).terminal
          (frontierAvailableActions compiled) state a})
    (hactive : (frontierActive compiled state).Nonempty) :
    (PrimitiveMachine compiled).AvailableRunFrom state
        (selectedCommitEvents compiled action.1)
        (selectedCommitDestination compiled action hactive) ∧
      (EventGraph.primitiveDownsetCheckpointPolicy compiled.graph).allowed
        state (selectedCommitDestination compiled action hactive) :=
  Classical.choose_spec
    (selectedCommitEvents_primitiveDownset_allowed_of_active
      compiled action.2 hactive)

private noncomputable def selectedCommitClosureTransition
    (compiled : CompiledProgram P L)
    {state : (PrimitiveMachine compiled).State}
    (action :
      {a : JointAction (FrontierAct compiled) //
        JointActionLegal (FrontierAct compiled)
          (frontierActive compiled)
          (PrimitiveMachine compiled).terminal
          (frontierAvailableActions compiled) state a})
    (hactive : (frontierActive compiled state).Nonempty) :
    PMF (PrimitiveMachine compiled).State :=
  internalClosureTransition compiled compiled.graph.nodeCount
    (selectedCommitDestination compiled action hactive)

private theorem selectedCommitClosure_support_cert
    (compiled : CompiledProgram P L)
    {state dst : (PrimitiveMachine compiled).State}
    (action :
      {a : JointAction (FrontierAct compiled) //
        JointActionLegal (FrontierAct compiled)
          (frontierActive compiled)
          (PrimitiveMachine compiled).terminal
          (frontierAvailableActions compiled) state a})
    (hactive : (frontierActive compiled state).Nonempty)
    (hsupport :
      dst ∈ (selectedCommitClosureTransition compiled action hactive).support) :
    InternalClosureRunCert compiled
      (selectedCommitDestination compiled action hactive) dst :=
  internalClosureTransition_support_cert
    compiled compiled.graph.nodeCount hsupport

private theorem selectedCommitClosure_support_closed
    (compiled : CompiledProgram P L)
    {state dst : (PrimitiveMachine compiled).State}
    (action :
      {a : JointAction (FrontierAct compiled) //
        JointActionLegal (FrontierAct compiled)
          (frontierActive compiled)
          (PrimitiveMachine compiled).terminal
          (frontierAvailableActions compiled) state a})
    (hactive : (frontierActive compiled state).Nonempty)
    (hsupport :
      dst ∈ (selectedCommitClosureTransition compiled action hactive).support) :
    EventGraph.readyInternalNodes compiled.graph dst.1 = ∅ :=
  internalClosureTransition_support_closed compiled hsupport

private theorem active_eq_empty_of_not_nonempty
    (compiled : CompiledProgram P L)
    {state : (PrimitiveMachine compiled).State}
    (hactive : ¬ (frontierActive compiled state).Nonempty) :
    frontierActive compiled state = ∅ := by
  ext who
  constructor
  · intro hwho
    exact False.elim (hactive ⟨who, hwho⟩)
  · intro hwho
    cases hwho

private theorem activePlayers_eq_empty_of_frontier_empty_no_internal
    (compiled : CompiledProgram P L)
    {state : (PrimitiveMachine compiled).State}
    (hreadyInternal :
      ¬ (EventGraph.readyInternalNodes compiled.graph state.1).Nonempty)
    (hfrontier : frontierActive compiled state = ∅) :
    EventGraph.activePlayers compiled.graph state.1 = ∅ := by
  simpa [frontierActive, EventGraph.frontierActive, hreadyInternal]
    using hfrontier

private theorem no_ready_internal_no_active_impossible
    (compiled : CompiledProgram P L)
    (guards : EventGraph.GuardLive compiled.graph)
    {state : (PrimitiveMachine compiled).State}
    (hterminal : ¬ (PrimitiveMachine compiled).terminal state)
    (hreadyInternal :
      ¬ (EventGraph.readyInternalNodes compiled.graph state.1).Nonempty)
    (hfrontier : frontierActive compiled state = ∅) :
    False := by
  have hactivePlayersEmpty :
      EventGraph.activePlayers compiled.graph state.1 = ∅ :=
    activePlayers_eq_empty_of_frontier_empty_no_internal
      compiled hreadyInternal hfrontier
  rcases EventGraph.exists_internal_available_of_no_active
      compiled.graphWF guards hterminal hactivePlayersEmpty with
    ⟨event, havailable⟩
  have hreadyInternalNode :
      EventGraph.ReadyInternalNode compiled.graph state.1 event.node :=
    havailable.readyInternalNode
  have hmem :
      event.node ∈
        EventGraph.readyInternalNodes compiled.graph state.1 := by
    unfold EventGraph.readyInternalNodes
    simp [hreadyInternalNode]
  exact hreadyInternal ⟨event.node, hmem⟩

/-- Frontier-checkpoint transitions generated by the canonical strategic
frontier policy.

An allowed checkpoint either closes currently-ready internal work, or, when no
internal work is ready, executes one legal strategic commit frontier and then
closes newly-ready internal work. -/
inductive FrontierCheckpointAllowed
    (compiled : CompiledProgram P L) :
    (PrimitiveMachine compiled).State →
      (PrimitiveMachine compiled).State → Prop where
  | internal {src dst : (PrimitiveMachine compiled).State}
      (hinternal :
        (EventGraph.readyInternalNodes compiled.graph src.1).Nonempty)
      (hsupport :
        dst ∈ (internalClosureAfterReady compiled src).support) :
      FrontierCheckpointAllowed compiled src dst
  | strategic {src dst : (PrimitiveMachine compiled).State}
      (hnoInternal :
        ¬ (EventGraph.readyInternalNodes compiled.graph src.1).Nonempty)
      (hactive : (frontierActive compiled src).Nonempty)
      (action :
        {a : JointAction (FrontierAct compiled) //
          JointActionLegal (FrontierAct compiled)
            (frontierActive compiled)
            (PrimitiveMachine compiled).terminal
            (frontierAvailableActions compiled) src a})
      (hsupport :
        dst ∈ (selectedCommitClosureTransition
          compiled action hactive).support) :
      FrontierCheckpointAllowed compiled src dst

private theorem frontierCheckpointAllowed_run
    (compiled : CompiledProgram P L)
    {src dst : (PrimitiveMachine compiled).State}
    (hallowed : FrontierCheckpointAllowed compiled src dst) :
    ∃ batch : List (PrimitiveMachine compiled).Event,
      (PrimitiveMachine compiled).AvailableRunFrom src batch dst ∧
        batch ≠ [] := by
  cases hallowed with
  | internal hinternal hsupport =>
      rcases internalClosureAfterReady_support_cert
          compiled hinternal hsupport with
        ⟨batch, _hinternalOnly, hrun, hne⟩
      exact ⟨batch, hrun, hne⟩
  | strategic hnoInternal hactive action hsupport =>
      have hprefix := selectedCommitDestination_spec compiled action hactive
      have htailCert :=
        selectedCommitClosure_support_cert
          compiled action hactive hsupport
      have htailSpec :=
        internalClosureRunEventBatch_spec compiled htailCert
      let batch :=
        selectedCommitEvents compiled action.1 ++
          internalClosureRunEventBatch compiled
            (selectedCommitDestination compiled action hactive) dst
      have hrun :
          (PrimitiveMachine compiled).AvailableRunFrom src batch dst := by
        dsimp [batch]
        exact hprefix.1.append htailSpec.2
      have hne : batch ≠ [] := by
        intro hnil
        have hselectedNil :
            selectedCommitEvents compiled action.1 = [] :=
          (List.eq_nil_of_append_eq_nil hnil).1
        exact
          selectedCommitEvents_ne_nil_of_active
            compiled action.2 hactive hselectedNil
      exact ⟨batch, hrun, hne⟩

private theorem frontierCheckpointAllowed_realizable
    (compiled : CompiledProgram P L)
    {src dst : (PrimitiveMachine compiled).State}
    (hallowed : FrontierCheckpointAllowed compiled src dst) :
    EventGraph.CheckpointStep compiled.graph src dst := by
  rcases frontierCheckpointAllowed_run compiled hallowed with
    ⟨batch, hrun, _hne⟩
  exact
    EventGraph.ToMachine.checkpointStep_of_availableRunFrom
      (primitiveMachineSpec compiled) hrun

private theorem frontierCheckpointAllowed_advances
    (compiled : CompiledProgram P L)
    {src dst : (PrimitiveMachine compiled).State}
    (hallowed : FrontierCheckpointAllowed compiled src dst) :
    src.1.done ⊂ dst.1.done := by
  rcases frontierCheckpointAllowed_run compiled hallowed with
    ⟨batch, hrun, hne⟩
  exact
    EventGraph.ToMachine.primitiveMachine_availableRunFrom_done_ssubset_of_ne_nil
      (primitiveMachineSpec compiled) hrun hne

/-- Checkpoint presentation matching the canonical frontier round policy. -/
noncomputable def frontierPresentation
    (compiled : CompiledProgram P L)
    (guards : EventGraph.GuardLive compiled.graph) :
    EventGraph.CheckpointPresentation compiled.graph where
  policy :=
    { allowed := FrontierCheckpointAllowed compiled
      realizable := frontierCheckpointAllowed_realizable compiled
      advances := frontierCheckpointAllowed_advances compiled }
  nonterminal_exists_allowed := by
    intro state hterminal
    classical
    by_cases hinternal :
        (EventGraph.readyInternalNodes compiled.graph state.1).Nonempty
    · rcases (internalClosureAfterReady compiled state).support_nonempty with
        ⟨dst, hdst⟩
      exact ⟨dst, FrontierCheckpointAllowed.internal hinternal hdst⟩
    · by_cases hactive : (frontierActive compiled state).Nonempty
      · rcases EventGraph.exists_legal_frontier_action_of_reachable
          compiled.graphWF guards hterminal with
          ⟨rawAction, hlegalRaw⟩
        let action :
            {a : JointAction (FrontierAct compiled) //
              JointActionLegal (FrontierAct compiled)
                (frontierActive compiled)
                (PrimitiveMachine compiled).terminal
                (frontierAvailableActions compiled) state a} :=
          ⟨rawAction, by
            constructor
            · exact hlegalRaw.1
            · intro who
              have hwho := hlegalRaw.2 who
              cases haction : rawAction who with
              | none =>
                  simpa [haction, frontierActive,
                    EventGraph.frontierActive, hinternal,
                    frontierAvailableActions, PrimitiveMachine,
                    EventGraph.ToMachine.primitiveMachine] using hwho
              | some localAction =>
                  simpa [haction, frontierActive,
                    EventGraph.frontierActive, hinternal,
                    frontierAvailableActions, EventGraph.frontierAvailableActions,
                    PrimitiveMachine,
                    EventGraph.ToMachine.primitiveMachine] using hwho⟩
        rcases
            (selectedCommitClosureTransition compiled action hactive).support_nonempty with
          ⟨dst, hdst⟩
        exact
          ⟨dst,
            FrontierCheckpointAllowed.strategic
              hinternal hactive action hdst⟩
      · have hactiveEmpty := active_eq_empty_of_not_nonempty
          compiled hactive
        exact False.elim
          (no_ready_internal_no_active_impossible
            compiled guards hterminal hinternal hactiveEmpty)

private noncomputable def canonicalFrontierTransition
    (compiled : CompiledProgram P L)
    (guards : EventGraph.GuardLive compiled.graph)
    (state : (PrimitiveMachine compiled).State)
    (action :
      {a : JointAction (FrontierAct compiled) //
        JointActionLegal (FrontierAct compiled)
          (frontierActive compiled)
          (PrimitiveMachine compiled).terminal
        (frontierAvailableActions compiled) state a}) :
    PMF (PrimitiveMachine compiled).State := by
  classical
  if _hinternal :
      (EventGraph.readyInternalNodes compiled.graph state.1).Nonempty then
    exact internalClosureAfterReady compiled state
  else if hactive : (frontierActive compiled state).Nonempty then
    exact selectedCommitClosureTransition compiled action hactive
  else
    let hactiveEmpty := active_eq_empty_of_not_nonempty
      compiled hactive
    exact False.elim
      (no_ready_internal_no_active_impossible
        compiled guards action.2.1 _hinternal hactiveEmpty)

private noncomputable def canonicalFrontierEventBatch
    (compiled : CompiledProgram P L)
    (guards : EventGraph.GuardLive compiled.graph)
    (state : (PrimitiveMachine compiled).State)
    (action :
      {a : JointAction (FrontierAct compiled) //
        JointActionLegal (FrontierAct compiled)
          (frontierActive compiled)
          (PrimitiveMachine compiled).terminal
          (frontierAvailableActions compiled) state a})
    (_dst : (PrimitiveMachine compiled).State) :
    List (PrimitiveMachine compiled).Event := by
  classical
  if _hinternal :
      (EventGraph.readyInternalNodes compiled.graph state.1).Nonempty then
    exact internalClosureEventBatch compiled state _dst
  else if hactive : (frontierActive compiled state).Nonempty then
    exact
      selectedCommitEvents compiled action.1 ++
        internalClosureRunEventBatch compiled
          (selectedCommitDestination compiled action hactive) _dst
  else
    let hactiveEmpty := active_eq_empty_of_not_nonempty
      compiled hactive
    exact False.elim
      (no_ready_internal_no_active_impossible
        compiled guards action.2.1 _hinternal hactiveEmpty)

/-- Canonical frontier semantics.

When internal graph nodes are ready, the round closes internal work before
presenting any strategic frontier. Otherwise, when players are active, the
round executes the selected commit frontier and then closes newly-ready
internal work before the checkpoint observation. A nonterminal checkpoint with
neither ready internal work nor active commits is impossible under graph
well-formedness and live guards. -/
noncomputable def canonicalFrontierRoundSemantics
    (compiled : CompiledProgram P L)
    (guards : EventGraph.GuardLive compiled.graph) :
    FrontierRoundSemantics compiled
      (frontierPresentation compiled guards) where
  guards := guards
  transition := canonicalFrontierTransition compiled guards
  eventBatch := canonicalFrontierEventBatch compiled guards
  certifies := by
    classical
    intro state action dst hsupport
    by_cases hinternal :
        (EventGraph.readyInternalNodes compiled.graph state.1).Nonempty
    · have hsupportMem :
          dst ∈
            (internalClosureAfterReady compiled state).support :=
        (PMF.mem_support_iff _ _).2 (by
          simpa [canonicalFrontierTransition, hinternal]
            using hsupport)
      have hcert :
          InternalClosureBatchCert compiled state dst :=
        internalClosureAfterReady_support_cert
          compiled hinternal hsupportMem
      have hbatchSpec :=
        internalClosureEventBatch_spec compiled hcert
      have hrealizes :
          FrontierBatchRealizesAction compiled action.1
            (internalClosureEventBatch compiled state dst) := by
        constructor
        · intro event hmem
          rcases hbatchSpec.1 event hmem with
            ⟨internalEvent, hevent⟩
          rw [hevent]
          trivial
        · intro who frontierAction node value haction _hvalue
          have hlocal := action.2.2 who
          rw [haction] at hlocal
          have hwho : who ∈ frontierActive compiled state := hlocal.1
          have hfrontierEmpty :
              frontierActive compiled state = ∅ := by
            simp [frontierActive, EventGraph.frontierActive, hinternal]
          rw [hfrontierEmpty] at hwho
          cases hwho
      exact
        { realizesAction := by
            simpa [canonicalFrontierEventBatch, hinternal] using
              hrealizes
          availableRun := by
            simpa [canonicalFrontierEventBatch, hinternal] using
              hbatchSpec.2.1
          allowed :=
            FrontierCheckpointAllowed.internal hinternal hsupportMem }
    · by_cases hactive : (frontierActive compiled state).Nonempty
      · have hsupportMem :
            dst ∈
              (selectedCommitClosureTransition
                compiled action hactive).support :=
          (PMF.mem_support_iff _ _).2 (by
            simpa [canonicalFrontierTransition, hinternal, hactive]
              using hsupport)
        have hclosureCert :
            InternalClosureRunCert compiled
              (selectedCommitDestination compiled action hactive) dst :=
          selectedCommitClosure_support_cert
            compiled action hactive hsupportMem
        have hclosureSpec :=
          internalClosureRunEventBatch_spec compiled hclosureCert
        have hspec :=
          selectedCommitDestination_spec compiled action hactive
        have hrealizes :
            EventGraph.FrontierBatchRealizesAction
              (primitiveMachineSpec compiled) action.1
              (canonicalFrontierEventBatch compiled guards
                state action
                dst) := by
          have hselectedRealizes :
              FrontierBatchRealizesAction compiled action.1
                (selectedCommitEvents compiled action.1) :=
            selectedCommitEvents_realizesAction
              compiled action.1 action.2
          simpa [canonicalFrontierEventBatch, hinternal, hactive] using
            frontierBatchRealizesAction_append_internalOnly
              compiled hselectedRealizes hclosureSpec.1
        have hrun :
            (EventGraph.PrimitiveMachineOf
              (primitiveMachineSpec compiled)).AvailableRunFrom state
              (canonicalFrontierEventBatch compiled guards
                state action
                dst)
              dst := by
          simpa [canonicalFrontierEventBatch, hinternal, hactive] using
            hspec.1.append hclosureSpec.2
        have hne :
            canonicalFrontierEventBatch compiled guards
              state action dst ≠ [] := by
          have hselectedNe :
              selectedCommitEvents compiled action.1 ≠ [] :=
            selectedCommitEvents_ne_nil_of_active
              compiled action.2 hactive
          intro hnil
          have hselectedNil :
              selectedCommitEvents compiled action.1 = [] :=
            (List.eq_nil_of_append_eq_nil
              (by
                simpa [canonicalFrontierEventBatch, hinternal,
                  hactive] using hnil)).1
          exact hselectedNe hselectedNil
        exact
          { realizesAction := hrealizes
            availableRun := hrun
            allowed :=
              FrontierCheckpointAllowed.strategic
                hinternal hactive action hsupportMem }
      · let hactiveEmpty := active_eq_empty_of_not_nonempty
          compiled hactive
        exact False.elim
          (no_ready_internal_no_active_impossible
            compiled guards action.2.1 hinternal hactiveEmpty)

/-- Every supported default frontier transition lands at an internal-closed
checkpoint. -/
theorem canonicalFrontierRoundSemantics_transition_support_closed
    (compiled : CompiledProgram P L)
    (guards : EventGraph.GuardLive compiled.graph)
    {state dst : (PrimitiveMachine compiled).State}
    (action :
      {a : JointAction (FrontierAct compiled) //
        JointActionLegal (FrontierAct compiled)
          (frontierActive compiled)
          (PrimitiveMachine compiled).terminal
          (frontierAvailableActions compiled) state a})
    (hsupport :
      (canonicalFrontierRoundSemantics compiled guards).transition
        state action dst ≠ 0) :
    EventGraph.readyInternalNodes compiled.graph dst.1 = ∅ := by
  classical
  change canonicalFrontierTransition compiled guards
    state action dst ≠ 0 at hsupport
  by_cases hinternal :
      (EventGraph.readyInternalNodes compiled.graph state.1).Nonempty
  · have hsupportMem :
        dst ∈ (internalClosureAfterReady compiled state).support :=
      (PMF.mem_support_iff _ _).2 (by
        simpa [canonicalFrontierTransition, hinternal] using hsupport)
    exact internalClosureAfterReady_support_closed compiled hsupportMem
  · by_cases hactive : (frontierActive compiled state).Nonempty
    · have hsupportMem :
          dst ∈
            (selectedCommitClosureTransition
              compiled action hactive).support :=
        (PMF.mem_support_iff _ _).2 (by
          simpa [canonicalFrontierTransition, hinternal, hactive]
            using hsupport)
      exact selectedCommitClosure_support_closed
        compiled action hactive hsupportMem
    · let hactiveEmpty := active_eq_empty_of_not_nonempty
        compiled hactive
      exact False.elim
        (no_ready_internal_no_active_impossible
          compiled guards action.2.1 hinternal hactiveEmpty)

/-- The natural round bound for a strict-downset frontier presentation.

Every supported nonterminal frontier round strictly increases the completed
node downset, so `nodeCount` rounds are enough for the default completed-game
presentation. -/
def completionBound (compiled : CompiledProgram P L) : Nat :=
  compiled.graph.nodeCount

end ToEventGraph

end Vegas
