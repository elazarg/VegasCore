/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseProposalLostPreparationMass
import Vegas.Game.PhaseProposalLostBindingForcedWait
import Interaction.ReactiveOwnPlay

/-! # Genuine counted suffixes after an unaccepted private preparation

The suffix is transported by induction on its actual trace startTrace. Source
rejection and sender silence are factual obligations of the original lost
episode, including its closing primitive. The image is constructed using the
original scheduler and original intrinsic Nature kernels.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction EventGraph GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks

/-- The complete actual suffix, with the designated sender's inert private
alias projected away only in the comparison. Every target history is genuine;
the original source-side obligations mention no target execution or law. -/
theorem phase_lost_binding_suffix_replay
    (bounds : MessageBounds graph) (initial : PMF (app).State)
    (horizon : Nat) (scheduler : (app).Scheduler)
    (owner : Player) (slot : CandidateSlot graph) (first second : Raw L)
    (start finish : (app).Control)
    (startTrace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol initial horizon
      scheduler).Trace (some start))
    (trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol initial horizon
      scheduler).Trace (some finish))
    (retained : TracePrefix startTrace trace)
    (image : (app).Execution)
    (imagePrefix : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol initial horizon
      scheduler).Trace (some ⟨start.remaining, start.actor, image⟩))
    (paired : image.eraseRecall app owner =
      ((HiddenSwap.preparationOnly (owner, slot) first second).phaseExecution
        start.execution).eraseRecall app owner)
    (silent : ∀ remaining execution
      (prior : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol initial horizon
        scheduler).Trace (some ⟨remaining, some owner, execution⟩)),
      TracePrefix startTrace prior → TracePrefix prior trace →
      PhaseCount.onePacketActions runtime leaks bounds owner (execution.recall owner)
        (execution.observe app owner) = {⟨none⟩})
    (targetSilent : ∀ remaining execution
      (prior : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol initial horizon
        scheduler).Trace (some ⟨remaining, some owner, execution⟩)),
      TracePrefix startTrace prior → TracePrefix prior trace →
      ∀ image (_imageTrace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
        initial horizon scheduler).Trace (some ⟨remaining, some owner, image⟩)),
      image.eraseRecall app owner =
        ((HiddenSwap.preparationOnly (owner, slot) first second).phaseExecution
          execution).eraseRecall app owner →
      PhaseCount.onePacketActions runtime leaks bounds owner (image.recall owner)
        (image.observe app owner) = {⟨none⟩})
    (unused : ∀ control
      (prior : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol initial horizon
        scheduler).Trace (some control)),
      TracePrefix startTrace prior → TracePrefix prior trace →
      control.execution.application.current.native.HandleUnused (owner, slot))
    (rejected : ∀ remaining execution
      (prior : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol initial horizon
        scheduler).Trace (some ⟨remaining + 1, none, execution⟩)),
      TracePrefix startTrace prior → ∀ command next,
      command ∈ (scheduler execution.environmentRecall
        (execution.observeEnvironment app)).support →
      next ∈ (execution.environmentStep app command).support →
      ∀ (nextTrace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol initial horizon
        scheduler).Trace (some ⟨remaining, command.actor? app, next⟩)),
      TracePrefix prior nextTrace → TracePrefix nextTrace trace →
      ∀ id message event, command = .include id →
        execution.network.lookup id = some message →
        message.payload.packet.call = .commitment event (owner, slot) →
          execution.application.handle runtime message = none) :
    ∃ (target : (app).Execution)
      (imageTrace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol initial horizon
        scheduler).Trace (some ⟨finish.remaining, finish.actor, target⟩)),
      TracePrefix imagePrefix imageTrace ∧
      target.eraseRecall app owner =
        ((HiddenSwap.preparationOnly (owner, slot) first second).phaseExecution
          finish.execution).eraseRecall app owner ∧
        imageTrace.transitionMass * startTrace.transitionMass =
          trace.transitionMass * imagePrefix.transitionMass ∧
      (∀ policy : ((PhaseCount.onePacketMenu runtime leaks bounds).information initial horizon
          scheduler).BehavioralPolicy owner,
        ((PhaseCount.onePacketMenu runtime leaks bounds).information initial horizon
          scheduler).ownPlayReachProbability policy
              (((PhaseCount.onePacketMenu runtime leaks bounds).information initial horizon
                scheduler).ownPlay owner imageTrace) =
          ((PhaseCount.onePacketMenu runtime leaks bounds).information initial horizon
            scheduler).ownPlayReachProbability policy
              (((PhaseCount.onePacketMenu runtime leaks bounds).information initial horizon
                scheduler).ownPlay owner imagePrefix)) ∧
      ∀ policy : ((PhaseCount.onePacketMenu runtime leaks bounds).information initial horizon
          scheduler).BehavioralPolicy owner,
        ((PhaseCount.onePacketMenu runtime leaks bounds).information initial horizon
          scheduler).ownPlayReachProbability policy
            (((PhaseCount.onePacketMenu runtime leaks bounds).information initial horizon
              scheduler).ownPlay owner trace) =
          ((PhaseCount.onePacketMenu runtime leaks bounds).information initial horizon
            scheduler).ownPlayReachProbability policy
              (((PhaseCount.onePacketMenu runtime leaks bounds).information initial horizon
                scheduler).ownPlay owner startTrace) := by
  classical
  let menu := PhaseCount.onePacketMenu runtime leaks bounds
  let swap := HiddenSwap.preparationOnly (owner, slot) first second
  have lift : ∀ {state} {middleTrace : (menu.protocol initial horizon scheduler).Trace state},
      TracePrefix startTrace middleTrace → TracePrefix middleTrace trace →
      ∃ (middle : (app).Control), state = some middle ∧ ∃ (target : (app).Execution)
        (imageTrace : (menu.protocol initial horizon scheduler).Trace
          (some ⟨middle.remaining, middle.actor, target⟩)),
        TracePrefix imagePrefix imageTrace ∧
        target.eraseRecall app owner =
          (swap.phaseExecution middle.execution).eraseRecall app owner ∧
          imageTrace.transitionMass * startTrace.transitionMass =
            middleTrace.transitionMass * imagePrefix.transitionMass ∧
        (∀ policy : (menu.information initial horizon scheduler).BehavioralPolicy owner,
          (menu.information initial horizon scheduler).ownPlayReachProbability policy
              ((menu.information initial horizon scheduler).ownPlay owner imageTrace) =
            (menu.information initial horizon scheduler).ownPlayReachProbability policy
              ((menu.information initial horizon scheduler).ownPlay owner imagePrefix)) ∧
        ∀ policy : (menu.information initial horizon scheduler).BehavioralPolicy owner,
          (menu.information initial horizon scheduler).ownPlayReachProbability policy
              ((menu.information initial horizon scheduler).ownPlay owner middleTrace) =
            (menu.information initial horizon scheduler).ownPlayReachProbability policy
              ((menu.information initial horizon scheduler).ownPlay owner startTrace) := by
    intro state middleTrace fromStart
    induction fromStart with
    | refl => exact fun _ => ⟨start, rfl, image, imagePrefix, .refl, paired, by ring, (fun _ =>
      rfl), fun _ => rfl⟩
    | @extend source target earlier kept joint legal realized ih =>
        intro toFinish
        have priorKept : TracePrefix earlier trace :=
          (TracePrefix.extend TracePrefix.refl joint legal realized).trans toFinish
        obtain ⟨middle, rfl, image, imageTrace, imageKept, relation, mass, tailFactor, sourceTail⟩
          := ih
          priorKept
        rcases middle with ⟨remaining, actor, original⟩
        cases actor with
        | some actor =>
            have available := legal.2 actor
            cases chosen : joint actor with
            | none =>
                rw [chosen] at available
                exact False.elim (available rfl)
            | some response =>
                rw [chosen] at available
                have moved : target = some
                    (⟨remaining, none, original.respond app actor response⟩ : (app).Control) := by
                  change target ∈ (PMF.pure _).support at realized
                  simpa only [PMF.mem_support_pure_iff, chosen, Option.getD_some] using realized
                subst target
                by_cases designated : actor = owner
                · subst actor
                  have wait : response = ⟨none⟩ := by
                    apply Finset.mem_singleton.mp
                    rw [← silent remaining original earlier kept priorKept]
                    exact available.2
                  subst response
                  obtain ⟨targetTrace, targetKept, targetMass, targetWord⟩ :=
                    HiddenSwap.phase_respond_trace_prefix bounds
                    initial horizon scheduler remaining
                    image owner ⟨none⟩ imageTrace
                    (PhaseCount.silence_onePacket runtime leaks bounds owner _ _)
                  refine ⟨_, rfl, _, targetTrace, imageKept.trans targetKept,
                    HiddenSwap.preparationOnly_wait_erased owner slot first second original image
                      relation, ?_, ?_, ?_⟩
                  · rw [targetMass, Trace.transitionMass_extend]
                    change _ = (earlier.transitionMass * ((PMF.pure _ : PMF (app).ProtocolState)
                      (some ⟨remaining, none, original.respond app owner ⟨none⟩⟩)).toReal) * _
                    simpa only [chosen, Option.getD_some, PMF.pure_apply_self,
                      ENNReal.toReal_one, mul_one] using mass
                  · intro policy
                    rw [targetWord owner, ite_eq_left rfl,
                      InformationModel.ownPlayReachProbability]
                    have atom := phase_singleton_wait_atom runtime leaks bounds horizon initial
                      scheduler owner (image.recall owner) (image.observe app owner)
                        (targetSilent remaining original earlier kept priorKept image imageTrace
                          relation) policy
                    rw [atom, one_mul]
                    exact tailFactor policy
                  · intro policy
                    rw [HiddenSwap.phase_trace_ownPlay bounds initial horizon scheduler _ _ owner,
                      (app).respond_ownPlay, InformationModel.ownPlayReachProbability]
                    have atom := phase_singleton_wait_atom runtime leaks bounds horizon initial
                      scheduler owner (original.recall owner) (original.observe app owner)
                        (silent remaining original earlier kept priorKept) policy
                    rw [atom, one_mul,
                      ← HiddenSwap.phase_trace_ownPlay bounds initial horizon scheduler _
                        earlier owner]
                    exact sourceTail policy
                · obtain ⟨offered, nextRelation⟩ :=
                    HiddenSwap.preparationOnly_foreign_respond_erased owner actor designated slot
                      first second bounds initial horizon scheduler remaining original image earlier
                        relation response available.2
                  obtain ⟨targetTrace, targetKept, targetMass, targetWord⟩ :=
                    HiddenSwap.phase_respond_trace_prefix bounds
                    initial horizon scheduler remaining
                    image actor response imageTrace offered
                  refine ⟨_, rfl, _, targetTrace, imageKept.trans targetKept, nextRelation, ?_,
                    ?_, ?_⟩
                  · rw [targetMass, Trace.transitionMass_extend]
                    change _ = (earlier.transitionMass * ((PMF.pure _ : PMF (app).ProtocolState)
                      (some ⟨remaining, none, original.respond app actor response⟩)).toReal) * _
                    simpa only [chosen, Option.getD_some, PMF.pure_apply_self,
                      ENNReal.toReal_one, mul_one] using mass
                  · intro policy
                    rw [targetWord owner, ite_eq_right (Ne.symm designated)]
                    exact tailFactor policy
                  · intro policy
                    rw [HiddenSwap.phase_trace_ownPlay bounds initial horizon scheduler _ _ owner,
                      (app).respond_recall_other original actor owner (Ne.symm designated) response,
                      ← HiddenSwap.phase_trace_ownPlay bounds initial horizon scheduler _
                        earlier owner]
                    exact sourceTail policy
        | none =>
            cases remaining with
            | zero => exact False.elim (legal.1 ⟨rfl, rfl⟩)
            | succ remaining =>
                change target ∈ ((scheduler original.environmentRecall
                  (original.observeEnvironment app)).bind _).support at realized
                obtain ⟨command, selected, drawn⟩ :=
                  Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ realized)
                obtain ⟨next, moved, same⟩ := PMF.support_map .. ▸ drawn
                subst target
                obtain ⟨target, targetMoved, nextRelation⟩ :=
                  HiddenSwap.preparationOnly_environment_erased owner slot first second original
                    image relation command next moved (unused _ earlier kept priorKept)
                      (rejected remaining original earlier kept command next selected moved
                        (earlier.extend joint legal realized)
                        (TracePrefix.extend TracePrefix.refl joint legal realized) toFinish)
                have service : image.environmentRecall = original.environmentRecall := by
                  have recorded := congrArg (fun execution : (app).Execution =>
                    execution.environmentRecall) relation
                  exact recorded
                have observation : image.observeEnvironment app = original.observeEnvironment app :=
                  (congrArg (fun execution : (app).Execution =>
                    execution.observeEnvironment app) relation).trans
                      (swap.observeEnvironment_phaseExecution original)
                have selectedImage : command ∈ (scheduler image.environmentRecall
                    (image.observeEnvironment app)).support := by
                  rw [service, observation]
                  exact selected
                obtain ⟨targetTrace, targetKept, targetMass, targetWord⟩ :=
                  HiddenSwap.phase_environment_trace_prefix bounds
                  initial horizon scheduler remaining
                  image target command imageTrace selectedImage targetMoved
                have intrinsic := HiddenSwap.preparationOnly_environment_atom owner slot first
                  second original image relation command next target moved targetMoved nextRelation
                    (unused _ earlier kept priorKept)
                    (rejected remaining original earlier kept command next selected moved
                      (earlier.extend joint legal realized)
                      (TracePrefix.extend TracePrefix.refl joint legal realized) toFinish)
                refine ⟨_, rfl, target, targetTrace, imageKept.trans targetKept, nextRelation, ?_,
                  ?_, ?_⟩
                · rw [targetMass, service, observation, intrinsic, Trace.transitionMass_extend]
                  change (_ * _ : ℝ) * startTrace.transitionMass =
                    (earlier.transitionMass * ((app).transition initial horizon scheduler
                      (some ⟨remaining + 1, none, original⟩) joint
                        (some ⟨remaining, command.actor? app, next⟩)).toReal) *
                          imagePrefix.transitionMass
                  rw [(app).transition_environment_apply initial horizon scheduler remaining
                    original next command moved]
                  simpa only [mul_assoc, mul_left_comm, mul_comm] using
                    congrArg (fun value : ℝ => value *
                      ((scheduler original.environmentRecall (original.observeEnvironment app)
                        command) *
                        (original.environmentStep app command) next).toReal) mass
                · intro policy
                  rw [targetWord owner]
                  exact tailFactor policy
                · intro policy
                  rw [HiddenSwap.phase_trace_ownPlay bounds initial horizon scheduler _ _ owner,
                    (app).environmentStep_recall original next command moved,
                    ← HiddenSwap.phase_trace_ownPlay bounds initial horizon scheduler _
                      earlier owner]
                  exact sourceTail policy
  obtain ⟨last, same, target, targetTrace, imageKept, relation, mass, tailFactor, sourceTail⟩ :=
    lift retained
    TracePrefix.refl
  cases Option.some.inj same
  exact ⟨target, targetTrace, imageKept, relation, mass, tailFactor, sourceTail⟩

end Vegas.EventGraphRuntime
