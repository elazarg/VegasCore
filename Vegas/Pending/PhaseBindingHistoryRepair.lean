/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseBindingEnvironmentDispatcher
import Vegas.Pending.PhaseBindingCounterfactualStep

/-! # Actual clear phased histories admit directed binding repairs -/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseBindingRepair

open Interaction EventGraph GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  {runtime : EventGraphRuntime graph}
  {leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph)}

/-- A supported clear history has an actual legal directed image under the
same scheduler and initial law. The saved and current semantic frontiers,
original submitted meanings, complete foreign inputs and physical scheduler
transcript are retained by the frame. The actual counterfactual reach of the
repaired owner is exactly preserved. This does not
assert an own-action likelihood bound or a posterior identity. -/
theorem repair_clear_history (bounds : MessageBounds graph) (covered : bounds.CoversOutputValues)
    (plan : RuntimePhasePlan graph) (ordered : graph.RevealRelaxedOrdered)
    (inputs : PMF graph.Inputs) (horizon : Nat)
    (scheduler : (phaseApplication runtime leaks).Scheduler) (owner : Player)
    (policies : ∀ who, ((PhaseCount.onePacketMenu runtime leaks bounds).information
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).BehavioralPolicy who)
    {state : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).State}
    (trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace state)
    (control : (phaseApplication runtime leaks).Control) (current : state = some control)
    (clear : control.execution.application.current.excluded = ∅) :
    ∃ (memory : BindingMemory runtime (nativeLeaks (graph := graph)))
      (image : (phaseApplication runtime leaks).Execution)
      (imageTrace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
        (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace
          (some ⟨control.remaining, control.actor, image⟩)),
      Frame runtime leaks memory owner control.execution image ∧
      memory.RecordsSubmittedBindings runtime (nativeLeaks (graph := graph)) owner
        (execution runtime leaks control.execution) (execution runtime leaks image) ∧
      memory.shadow.OwnBindings owner ∧
      ((PhaseCount.onePacketMenu runtime leaks bounds).information
        (inputs.map (PhaseRuntimeState.initial plan)) horizon
          scheduler).counterfactualReachProbability policies owner trace =
        ((PhaseCount.onePacketMenu runtime leaks bounds).information
          (inputs.map (PhaseRuntimeState.initial plan)) horizon
            scheduler).counterfactualReachProbability policies owner imageTrace := by
  let app := phaseApplication runtime leaks
  let menu := PhaseCount.onePacketMenu runtime leaks bounds
  let initial := inputs.map (PhaseRuntimeState.initial plan)
  let information := menu.information initial horizon scheduler
  induction trace generalizing control with
  | start => cases current
  | @extend before after prior joint legal realized ih =>
      subst current
      let afterTrace := prior.extend joint legal realized
      cases before with
      | none =>
          change some control ∈ (initial.map fun state =>
            some (⟨horizon, none, ReactiveApplication.Execution.initial app state⟩ :
              app.Control)).support at realized
          obtain ⟨draw, _supported, same⟩ := PMF.support_map .. ▸ realized
          cases Option.some.inj same
          let physical := ReactiveApplication.Execution.initial app draw
          let memory := BindingMemory.atRecall runtime (nativeLeaks (graph := graph))
            ((execution runtime leaks physical).recall owner)
          refine ⟨memory, physical, afterTrace,
            frame_at_clear_history runtime leaks bounds plan inputs horizon scheduler
              afterTrace clear owner, ?_, ?_, rfl⟩
          · intro message member
            cases member
          · exact BindingShadow.ownBindings_empty owner
      | some before =>
          have rawRealized : some control ∈
              (app.transition initial horizon scheduler (some before) joint).support := realized
          have monotone := (phaseApplication_exclusion_monotone runtime leaks).transition
            initial horizon scheduler before control joint rawRealized
          have beforeClear : before.execution.application.current.excluded = ∅ :=
            Finset.subset_empty.mp (clear ▸ monotone)
          obtain ⟨memory, image, imageTrace, paired, recorded, onlyBindings, priorMass⟩ :=
            ih before rfl beforeClear
          rcases before with ⟨remaining, actor, original⟩
          cases actor with
          | some actor =>
              have available := legal.2 actor
              cases responseEq : joint actor with
              | none =>
                  rw [responseEq] at available
                  exact False.elim (available rfl)
              | some response =>
                  rw [responseEq] at available
                  let sourceJoint : Player → Option app.Action :=
                    fun who => if who = actor then some response else none
                  have jointEq : joint = sourceJoint := by
                    funext who
                    by_cases same : who = actor
                    · subst who
                      simpa only [sourceJoint, ↓reduceIte] using responseEq
                    · have inactive : joint who = none := LegalOption.eq_none_of_inactive _
                        ((menu.protocol initial horizon scheduler).legalOption_of_legal legal who)
                        (by simp [ReactiveApplication.ResponseMenu.protocol,
                          ReactiveApplication.actor, Ne.symm same])
                      simpa only [sourceJoint, same, ↓reduceIte] using inactive
                  subst joint
                  change some control ∈ (PMF.pure (some
                    (⟨remaining, none, original.respond app actor
                      ((sourceJoint actor).getD ⟨none⟩)⟩ : app.Control))).support at realized
                  simp only [sourceJoint, ↓reduceIte, Option.getD_some,
                    PMF.mem_support_pure_iff] at realized
                  cases Option.some.inj realized
                  obtain ⟨target, remembered, member, nextFrame, nextRecorded, nextOnly,
                      responseImageEq⟩ :=
                    paired.response_records recorded onlyBindings bounds covered plan ordered
                      inputs horizon scheduler remaining actor prior imageTrace response available.2
                  let targetJoint : Player → Option app.Action :=
                    fun who => if who = actor then some target else none
                  have targetLegal : (menu.protocol initial horizon scheduler).Legal
                      (some ⟨remaining, some actor, image⟩) targetJoint := by
                    constructor
                    · simp [menu, ReactiveApplication.ResponseMenu.protocol,
                        ReactiveApplication.terminal]
                    · intro who
                      by_cases same : who = actor
                      · subst who
                        simpa [menu, PhaseCount.onePacketMenu, targetJoint,
                          ReactiveApplication.ResponseMenu.protocol,
                          ReactiveApplication.actor, ReactiveApplication.ResponseMenu.available]
                          using member
                      · simp [menu, targetJoint, ReactiveApplication.ResponseMenu.protocol,
                          ReactiveApplication.actor, same, Ne.symm same]
                  have targetRealized : some ⟨remaining, none, image.respond app actor target⟩ ∈
                      ((menu.protocol initial horizon scheduler).step _
                        ⟨targetJoint, targetLegal⟩).support := by
                    change _ ∈ (PMF.pure _).support
                    simp only [targetJoint, ↓reduceIte, Option.getD_some,
                      PMF.mem_support_pure_iff]
                    rfl
                  have sameActions : ∀ who, who ≠ owner → sourceJoint who = targetJoint who := by
                    intro who different
                    by_cases same : who = actor
                    · subst who
                      have targetSame : target = response := by
                        simpa only [Frame.responseImage, different, ↓reduceIte]
                          using responseImageEq
                      simp only [sourceJoint, targetJoint, ↓reduceIte, targetSame]
                    · simp only [sourceJoint, targetJoint, same, ↓reduceIte]
                  have compared := paired.response_counterfactualStepProb runtime leaks menu
                    initial horizon scheduler remaining actor prior imageTrace sourceJoint
                      targetJoint legal targetLegal sameActions policies
                  exact ⟨remembered, image.respond app actor target,
                    imageTrace.extend targetJoint targetLegal targetRealized,
                    nextFrame, nextRecorded, nextOnly, by
                      rw [InformationModel.counterfactualReachProbability,
                        InformationModel.counterfactualReachProbability, priorMass]
                      congr 1
                      simpa only [sourceJoint, Option.getD_some, targetJoint, ↓reduceIte]
                        using compared⟩
          | none =>
              cases remaining with
              | zero => exact False.elim (legal.1 ⟨rfl, rfl⟩)
              | succ remaining =>
                  have sourceRealized := realized
                  change some control ∈ ((scheduler original.environmentRecall
                    (original.observeEnvironment app)).bind _).support at realized
                  obtain ⟨command, selected, supported⟩ :=
                    Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ realized)
                  obtain ⟨next, moved, same⟩ := PMF.support_map .. ▸ supported
                  cases Option.some.inj same
                  obtain ⟨target, targetSupported, nextFrame, nextRecorded, _nextTrace⟩ :=
                    paired.environment_records recorded onlyBindings bounds plan inputs horizon
                      scheduler remaining prior imageTrace command selected next moved clear
                  let targetJoint : Player → Option app.Action := fun _ => none
                  have targetLegal : (menu.protocol initial horizon scheduler).Legal
                      (some ⟨remaining + 1, none, image⟩) targetJoint := by
                    constructor
                    · simp [menu, ReactiveApplication.ResponseMenu.protocol,
                        ReactiveApplication.terminal]
                    · intro who
                      simp [menu, targetJoint, ReactiveApplication.ResponseMenu.protocol,
                        ReactiveApplication.actor]
                  have targetRealized : some ⟨remaining, command.actor? app, target⟩ ∈
                      ((menu.protocol initial horizon scheduler).step _
                        ⟨targetJoint, targetLegal⟩).support := by
                    change _ ∈ ((scheduler image.environmentRecall
                      (image.observeEnvironment app)).bind _).support
                    rw [PMF.support_bind]
                    apply Set.mem_iUnion₂.mpr
                    refine ⟨command, ?_, ?_⟩
                    · rw [← paired.scheduler_law scheduler]
                      exact selected
                    · rw [PMF.support_map]
                      exact ⟨target, targetSupported, rfl⟩
                  have compared := paired.counterfactual_environment_extend runtime leaks menu
                    initial horizon scheduler nextFrame remaining command prior imageTrace joint
                      targetJoint legal targetLegal moved targetSupported sourceRealized
                      targetRealized policies priorMass
                  exact ⟨memory, target, imageTrace.extend targetJoint targetLegal targetRealized,
                    nextFrame, nextRecorded, onlyBindings, compared⟩

end Vegas.EventGraphRuntime.PhaseBindingRepair
