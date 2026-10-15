/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseRepairCallbackWitness
import Vegas.Game.PhaseRepairMarkedRecords
import Vegas.Pending.PhaseBindingCounterfactualStep

/-! # Actual repaired histories retain every selected raw binding position -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
  (runtime : EventGraphRuntime (serviceGraph setup mode))
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))
  (bounds : MessageBounds (serviceGraph setup mode))
  (plan : RuntimePhasePlan (serviceGraph setup mode))
  (horizon : Nat) (scheduler : (phaseApplication runtime leaks).Scheduler)

local notation "app" => phaseApplication runtime leaks
local notation "initial" => setup.initialLaw.map
  (fun draw => PhaseRuntimeState.initial plan (encodeInputs draw))
local notation "E" => ReactiveApplication.ResponseMenu.protocol
  (PhaseCount.onePacketMenu runtime leaks bounds) initial horizon scheduler
local notation "N" => ReactiveApplication.ResponseMenu.information
  (PhaseCount.onePacketMenu runtime leaks bounds) initial horizon scheduler

/-- Every actual clear binding history has a genuine same-scheduler repaired
history. Each own response has its derived chronological category, and the
actual counterfactual reach equality retains all other players and all chance
and scheduler factors. Every selected raw binding position has separate ordinary
before/after words and a concrete same-slot marked pair. No mixture origin is
inferred from a typed failure, and no target history or kernel ratio is given. -/
theorem phase_repair_marked_binding_history (covered : bounds.CoversOutputValues)
    (owner : Player) (policies : ∀ who, (N).BehavioralPolicy who)
    (final : (app).Control) (finalTrace : (E).Trace (some final))
    (bindingEvent : (serviceGraph setup mode).EventId) (bindingOwner : Player)
    (bindingPayload : L.Ty)
    (bindingOutput : (serviceGraph setup mode).outputLayout bindingEvent =
      .binding bindingOwner bindingPayload)
    (finalClear : final.execution.application.current.excluded = ∅)
    (finalRequest : final.execution.application.SeedRequest bindingOwner
      ⟨final.execution.application.attempt, bindingEvent⟩) :
    ∃ (memory : BindingMemory runtime (PhaseBindingRepair.nativeLeaks
        (graph := serviceGraph setup mode))) (image : (app).Execution)
      (imageTrace : (E).Trace (some ⟨final.remaining, final.actor, image⟩)) (sends waits : Nat),
      PhaseBindingRepair.Frame runtime leaks memory owner final.execution image ∧
      memory.RecordsSubmittedBindings runtime (PhaseBindingRepair.nativeLeaks
        (graph := serviceGraph setup mode)) owner
          (PhaseBindingRepair.execution runtime leaks final.execution)
          (PhaseBindingRepair.execution runtime leaks image) ∧
      memory.shadow.OwnBindings owner ∧
      (N).counterfactualReachProbability policies owner finalTrace =
        (N).counterfactualReachProbability policies owner imageTrace ∧
      PhaseRepairOwnPlay setup mode runtime leaks bounds plan horizon scheduler owner
        ((app).recallOwnPlay (final.execution.recall owner))
        ((app).recallOwnPlay (image.recall owner)) sends waits ∧
      PhaseRepairMarkedBindings setup mode runtime leaks bounds plan horizon scheduler owner
        ((app).recallOwnPlay (final.execution.recall owner))
        ((app).recallOwnPlay (image.recall owner)) := by
  let menu := PhaseCount.onePacketMenu runtime leaks bounds
  let inputs := setup.initialLaw.map (fun draw => encodeInputs draw)
  have initialEq : inputs.map (PhaseRuntimeState.initial plan) = initial := by
    exact PMF.map_comp _ _ _
  have ordered := serviceGraph_revealRelaxedOrdered setup mode
  have construct : ∀ {state : (E).State} (trace : (E).Trace state),
      TracePrefix trace finalTrace → ∀ control : (app).Control, state = some control →
      control.execution.application.current.excluded = ∅ →
      ∃ (memory : BindingMemory runtime (PhaseBindingRepair.nativeLeaks
          (graph := serviceGraph setup mode))) (image : (app).Execution)
        (imageTrace : (E).Trace (some ⟨control.remaining, control.actor, image⟩))
        (sends waits : Nat),
        PhaseBindingRepair.Frame runtime leaks memory owner control.execution image ∧
        memory.RecordsSubmittedBindings runtime (PhaseBindingRepair.nativeLeaks
          (graph := serviceGraph setup mode)) owner
            (PhaseBindingRepair.execution runtime leaks control.execution)
            (PhaseBindingRepair.execution runtime leaks image) ∧
        memory.shadow.OwnBindings owner ∧
        (N).counterfactualReachProbability policies owner trace =
          (N).counterfactualReachProbability policies owner imageTrace ∧
        PhaseRepairOwnPlay setup mode runtime leaks bounds plan horizon scheduler owner
          ((app).recallOwnPlay (control.execution.recall owner))
          ((app).recallOwnPlay (image.recall owner)) sends waits ∧
        PhaseRepairMarkedBindings setup mode runtime leaks bounds plan horizon scheduler owner
          ((app).recallOwnPlay (control.execution.recall owner))
          ((app).recallOwnPlay (image.recall owner)) := by
    intro state trace
    induction trace with
    | start => intro _ control impossible; cases impossible
    | @extend before after prior joint legal realized ih =>
        intro isPrefix control current clear
        subst current
        have priorPrefix : TracePrefix prior finalTrace :=
          (TracePrefix.extend (.refl) joint legal realized).trans isPrefix
        let afterTrace := prior.extend joint legal realized
        cases before with
        | none =>
            change some control ∈ ((initial).map fun state =>
              some (⟨horizon, none, ReactiveApplication.Execution.initial app state⟩ :
                (app).Control)).support at realized
            obtain ⟨draw, _supported, same⟩ := PMF.support_map .. ▸ realized
            cases Option.some.inj same
            let physical := ReactiveApplication.Execution.initial app draw
            let memory := BindingMemory.atRecall runtime (PhaseBindingRepair.nativeLeaks
              (graph := serviceGraph setup mode))
              ((PhaseBindingRepair.execution runtime leaks physical).recall owner)
            refine ⟨memory, physical, afterTrace, 0, 0,
              PhaseBindingRepair.frame_at_clear_history runtime leaks bounds plan inputs horizon
                scheduler (by rw [initialEq]; exact afterTrace) clear owner, ?_, ?_, rfl, .nil,
                PhaseRepairMarkedBindings.nil setup mode runtime leaks bounds plan horizon
                  scheduler owner⟩
            · intro message member
              cases member
            · exact BindingShadow.ownBindings_empty owner
        | some before =>
            have rawRealized : some control ∈
                ((app).transition initial horizon scheduler (some before) joint).support := realized
            have monotone := (phaseApplication_exclusion_monotone runtime leaks).transition
              initial horizon scheduler before control joint rawRealized
            have beforeClear : before.execution.application.current.excluded = ∅ :=
              Finset.subset_empty.mp (clear ▸ monotone)
            obtain ⟨memory, image, imageTrace, sends, waits, paired, recorded, onlyBindings,
                priorMass, priorRelation, priorMarked⟩ := ih priorPrefix before rfl beforeClear
            have countedPrior : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
                (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace
                  (some before) := by rw [initialEq]; exact prior
            have countedImage : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
                (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace
                  (some ⟨before.remaining, before.actor, image⟩) := by
              rw [initialEq]
              exact imageTrace
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
                    let sourceJoint : Player → Option (app).Action :=
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
                        ((sourceJoint actor).getD ⟨none⟩)⟩ : (app).Control))).support at realized
                    simp only [sourceJoint, ↓reduceIte, Option.getD_some,
                      PMF.mem_support_pure_iff] at realized
                    cases Option.some.inj realized
                    obtain ⟨target, remembered, member, nextFrame, nextRecorded, nextOnly,
                        responseImageEq⟩ :=
                      paired.response_records recorded onlyBindings bounds covered plan ordered
                        inputs horizon scheduler remaining actor countedPrior countedImage response
                        available.2
                    let targetJoint : Player → Option (app).Action :=
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
                    have sameActions : ∀ who, who ≠ owner → sourceJoint who = targetJoint who := by
                      intro who different
                      by_cases same : who = actor
                      · subst who
                        have targetSame : target = response := by
                          simpa only [PhaseBindingRepair.Frame.responseImage, different, ↓reduceIte]
                            using responseImageEq
                        simp only [sourceJoint, targetJoint, ↓reduceIte, targetSame]
                      · simp only [sourceJoint, targetJoint, same, ↓reduceIte]
                    have compared := paired.response_counterfactualStepProb runtime leaks menu
                      initial horizon scheduler remaining actor prior imageTrace sourceJoint
                        targetJoint legal targetLegal sameActions policies
                    have relationNext : ∃ nextSends nextWaits,
                        PhaseRepairOwnPlay setup mode runtime leaks bounds plan horizon scheduler
                          owner ((app).recallOwnPlay ((original.respond app actor response).recall
                            owner)) ((app).recallOwnPlay ((image.respond app actor target).recall
                              owner)) nextSends nextWaits ∧
                          PhaseRepairMarkedBindings setup mode runtime leaks bounds plan horizon
                            scheduler owner
                            ((app).recallOwnPlay ((original.respond app actor response).recall
                              owner))
                            ((app).recallOwnPlay ((image.respond app actor target).recall
                              owner)) := by
                      by_cases own : actor = owner
                      · subst actor
                        obtain ⟨stepSends, stepWaits, callback⟩ := phase_repair_callback_pair setup
                          mode runtime leaks bounds plan horizon scheduler covered owner remaining
                            original image memory paired prior imageTrace final finalTrace
                            priorPrefix bindingEvent bindingOwner bindingPayload bindingOutput
                              finalClear finalRequest response available.2
                        rw [← responseImageEq] at callback
                        refine ⟨stepSends + sends, stepWaits + waits, ?_, ?_⟩
                        · rw [(app).respond_ownPlay, (app).respond_ownPlay]
                          simpa only [List.singleton_append] using callback.append setup mode
                            runtime leaks bounds plan horizon scheduler priorRelation
                        · rw [(app).respond_ownPlay, (app).respond_ownPlay]
                          apply PhaseRepairMarkedBindings.cons setup mode runtime leaks bounds plan
                            horizon scheduler owner _ _ _ _ stepSends stepWaits sends waits callback
                              priorRelation priorMarked
                          intro raw
                          obtain ⟨event, serial, preparation, evidence, sourceEq⟩ := raw
                          change response = _ at sourceEq
                          subst response
                          rw [responseImageEq]
                          exact phase_repair_raw_response_pair setup mode runtime leaks bounds plan
                            horizon scheduler covered owner remaining original image memory paired
                              prior imageTrace event serial preparation evidence available.2
                      · refine ⟨sends, waits, ?_, ?_⟩
                        · simpa only [ReactiveApplication.Execution.respond, Ne.symm own,
                            ↓reduceIte] using priorRelation
                        · simpa only [ReactiveApplication.Execution.respond, Ne.symm own,
                            ↓reduceIte] using priorMarked
                    obtain ⟨nextSends, nextWaits, nextRelation, nextMarked⟩ := relationNext
                    refine ⟨remembered, image.respond app actor target,
                      imageTrace.extend targetJoint targetLegal targetRealized,
                      nextSends, nextWaits, nextFrame, nextRecorded, nextOnly, ?_, nextRelation,
                        nextMarked⟩
                    rw [InformationModel.counterfactualReachProbability,
                      InformationModel.counterfactualReachProbability, priorMass]
                    congr 1
                    simpa only [sourceJoint, Option.getD_some, targetJoint, ↓reduceIte]
                      using compared
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
                        scheduler remaining countedPrior countedImage command selected next moved
                          clear
                    let targetJoint : Player → Option (app).Action := fun _ => none
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
                    refine ⟨memory, target,
                      imageTrace.extend targetJoint targetLegal targetRealized, sends, waits,
                      nextFrame, nextRecorded, onlyBindings, compared, ?_, ?_⟩
                    · rw [(app).environmentStep_recall original next command moved,
                        (app).environmentStep_recall image target command targetSupported]
                      exact priorRelation
                    · rw [(app).environmentStep_recall original next command moved,
                        (app).environmentStep_recall image target command targetSupported]
                      exact priorMarked
  exact construct finalTrace .refl final rfl finalClear

end Vegas
