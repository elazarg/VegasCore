/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseProposalLostBindingInformation
import Vegas.Game.PhaseProposalRepairChance
import Vegas.Game.PhaseProposalLostBindingForcedWait
import Vegas.Pending.PhaseProposalPreparationPrefix

/-! # Initialized mass of an actual lost ordinary-value replacement

The earlier initialized trace is literal. A genuinely counted changed SEND
is constructed at the same fresh physical slot, and the actual suffix replay
retains every intrinsic Nature atom through rejection, expiry and restore.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction EventGraph GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))
  (bounds : MessageBounds graph) (plan : RuntimePhasePlan graph)
  (inputs : PMF graph.Inputs) (horizon : Nat)

local notation "app" => phaseApplication runtime leaks
local notation "menu" => PhaseCount.onePacketMenu runtime leaks bounds
local notation "initial" => inputs.map (PhaseRuntimeState.initial plan)

/-- Change an actual submitted typed value that was never admitted in its
finished original attempt. The actual initial draw and original pre-SEND
trace remain literal; no image prefix or image mass is assumed. -/
theorem phase_lost_binding_initialized_mass
    (scheduler : (app).Scheduler) (ordered : graph.RevealRelaxedOrdered)
    (fuel : Nat) (owner : Player) (execution : (app).Execution)
    (prior : ((menu).protocol initial horizon scheduler).Trace
      (some ⟨fuel, some owner, execution⟩))
    (omitted : graph.EventId) (payload : L.Ty)
    (binding : graph.outputLayout omitted = .binding owner payload)
    (request : execution.application.SeedRequest owner ⟨execution.application.attempt, omitted⟩)
    (serial : Nat) (first second : L.Val payload) (evidence : EvidenceRequest graph)
    (offered : (⟨some ⟨⟨.commitment omitted (owner, .prepared serial),
      some ⟨payload, first⟩⟩, evidence⟩⟩ : (app).Action) ∈
        PhaseCount.onePacketActions runtime leaks bounds owner (execution.recall owner)
          (execution.observe app owner))
    (values : ∀ value : L.Val payload, (⟨payload, value⟩ : Raw L) ∈ bounds.values)
    (sentJoint : Player → Option (app).Action)
    (sentLegal : ((menu).protocol initial horizon scheduler).Legal
      (some ⟨fuel, some owner, execution⟩) sentJoint)
    (sentRealized : some (⟨fuel, none, execution.respond app owner
      ⟨some ⟨⟨.commitment omitted (owner, .prepared serial), some ⟨payload, first⟩⟩,
        evidence⟩⟩⟩ : (app).Control) ∈
      (((menu).protocol initial horizon scheduler).step
        (some ⟨fuel, some owner, execution⟩) ⟨sentJoint, sentLegal⟩).support)
    (remaining : Nat) (before after : (app).Execution)
    (beforeTrace : ((menu).protocol initial horizon scheduler).Trace
      (some ⟨remaining + 1, none, before⟩))
    (toClose : TracePrefix (prior.extend sentJoint sentLegal sentRealized) beforeTrace)
    (same : execution.application.attempt = before.application.attempt)
    (command : (app).Command)
    (selected : command ∈ (scheduler before.environmentRecall
      (before.observeEnvironment app)).support)
    (moved : after ∈ (before.environmentStep app command).support)
    (closingJoint : Player → Option (app).Action)
    (closingLegal : ((menu).protocol initial horizon scheduler).Legal
      (some ⟨remaining + 1, none, before⟩) closingJoint)
    (closingRealized : some (⟨remaining, command.actor? app, after⟩ : (app).Control) ∈
      (((menu).protocol initial horizon scheduler).step
        (some ⟨remaining + 1, none, before⟩) ⟨closingJoint, closingLegal⟩).support)
    (finish : (app).Control)
    (trace : ((menu).protocol initial horizon scheduler).Trace (some finish))
    (fromClose : TracePrefix (beforeTrace.extend closingJoint closingLegal closingRealized) trace)
    (current : RecoveryState graph) (effect : PhaseClosingEffect runtime leaks before after current)
    (phase : RuntimePhase graph) (installed : before.application.phases.head? = some phase)
    (kind : phase.kind = .commitment)
    (finished : phase.Finished (phase.drain current))
    (coverage : (phase.drain current).FailureCoverage)
    (excludedEq : (phase.drain current).excluded = after.application.current.excluded)
    (inside : omitted ∈ phase.events)
    (unaccepted : (phase.drain current).native.accepted (.inr omitted) = none) :
    ∃ (image : (app).Execution)
      (imageTrace : ((menu).protocol initial horizon scheduler).Trace
        (some ⟨finish.remaining, finish.actor, image⟩)),
      TracePrefix prior imageTrace ∧ imageTrace.transitionMass = trace.transitionMass ∧
      image.eraseRecall app owner =
        ((HiddenSwap.preparationOnly (owner, .prepared serial) ⟨payload, first⟩
          ⟨payload, second⟩).phaseExecution finish.execution).eraseRecall app owner ∧
      image.application.current.native.config.inputs =
        finish.execution.application.current.native.config.inputs ∧
      (∀ who, who ≠ owner →
        (image.recall who, image.observe app who) =
          (finish.execution.recall who, finish.execution.observe app who) ∧
        ((menu).information initial horizon scheduler).ownPlay who imageTrace =
          ((menu).information initial horizon scheduler).ownPlay who trace) ∧
      (∀ policy : ((menu).information initial horizon scheduler).BehavioralPolicy owner,
        ((menu).information initial horizon scheduler).ownPlayReachProbability policy
            (((menu).information initial horizon scheduler).ownPlay owner imageTrace) =
          ((menu).information initial horizon scheduler).ownPlayReachProbability policy
            ((some (execution.recall owner, execution.observe app owner),
              phaseBindingResponse runtime leaks owner omitted payload (.success second) serial) ::
                ((menu).information initial horizon scheduler).ownPlay owner prior) ∧
        ((menu).information initial horizon scheduler).ownPlayReachProbability policy
            (((menu).information initial horizon scheduler).ownPlay owner trace) =
          ((menu).information initial horizon scheduler).ownPlayReachProbability policy
            ((some (execution.recall owner, execution.observe app owner),
              (⟨some ⟨⟨.commitment omitted (owner, .prepared serial),
                some ⟨payload, first⟩⟩, evidence⟩⟩ : (app).Action)) ::
                  ((menu).information initial horizon scheduler).ownPlay owner prior)) ∧
      ∀ profile : ∀ who, ((menu).information initial horizon scheduler).BehavioralPolicy who,
        (((menu).information initial horizon scheduler).historyReachWeight profile
            ⟨some ⟨finish.remaining, finish.actor, image⟩, imageTrace⟩).toReal *
          (((profile owner (some (execution.recall owner, execution.observe app owner))).map
            Subtype.val) (some (⟨some ⟨⟨.commitment omitted (owner, .prepared serial),
              some ⟨payload, first⟩⟩, evidence⟩⟩ : (app).Action))).toReal =
          (((menu).information initial horizon scheduler).historyReachWeight profile
            ⟨some finish, trace⟩).toReal *
          (((profile owner (some (execution.recall owner, execution.observe app owner))).map
            Subtype.val) (some (phaseBindingResponse runtime leaks owner omitted payload
              (.success second) serial))).toReal := by
  classical
  let material : WitnessedSubmission graph :=
    ⟨⟨.commitment omitted (owner, .prepared serial), some ⟨payload, first⟩⟩, evidence⟩
  let source : (app).Action := ⟨some material⟩
  let original := execution.respond app owner source
  let start : (app).Control := ⟨fuel, none, original⟩
  let startTrace := prior.extend sentJoint sentLegal sentRealized
  let packet := (execution.application.submit owner material).emit owner
    (execution.network.known owner) material
  let entry : (app).PlayerEntry :=
    ⟨execution.observe app owner, source, some (execution.network.submit owner packet).1⟩
  have recorded : entry ∈ original.recall owner := by
    simp only [original, source, ReactiveApplication.Execution.respond, ↓reduceIte]
    exact List.mem_append_right _ (List.mem_singleton_self _)
  obtain ⟨imagePrefix, initialKept, initialMass, paired, saved, initialWord⟩ :=
    HiddenSwap.preparationOnly_changed_response_prefix bounds plan ordered inputs horizon scheduler
      fuel owner execution prior omitted payload binding request serial first second evidence
        offered values
  have originalMass : startTrace.transitionMass = prior.transitionMass := by
    rw [Trace.transitionMass_extend]
    have pureSupport : some (⟨fuel, none, original⟩ : (app).Control) ∈
        (PMF.pure (some (⟨fuel, none, execution.respond app owner
          ((sentJoint owner).getD ⟨none⟩)⟩ : (app).Control))).support := sentRealized
    have equal := (PMF.mem_support_pure_iff _ _).mp pureSupport
    change prior.transitionMass * ((PMF.pure
      (some (⟨fuel, none, execution.respond app owner ((sentJoint owner).getD ⟨none⟩)⟩ :
        (app).Control))) (some ⟨fuel, none, original⟩)).toReal = prior.transitionMass
    rw [equal, PMF.pure_apply_self, ENNReal.toReal_one, mul_one]
  obtain ⟨_sourceKept, image, imageTrace, imageKept, finalPaired, crossMass, tailFactor,
    sourceTail⟩ :=
    phase_lost_binding_replay runtime leaks bounds plan inputs horizon scheduler ordered start
      startTrace remaining before after beforeTrace toClose same command selected moved
        closingJoint closingLegal closingRealized
        (beforeTrace.extend closingJoint closingLegal closingRealized) rfl finish trace fromClose
        current effect phase installed kind finished coverage excludedEq owner omitted payload
        binding inside unaccepted entry recorded material rfl serial rfl rfl saved
        ⟨payload, first⟩ ⟨payload, second⟩ _ imagePrefix paired
  have mass : imageTrace.transitionMass = trace.transitionMass := by
    rw [originalMass, initialMass] at crossMass
    exact mul_right_cancel₀ (ne_of_gt prior.transitionMass_pos) crossMass
  have information := HiddenSwap.preparationOnly_full_information bounds initial horizon scheduler
    owner (.prepared serial) ⟨payload, first⟩ ⟨payload, second⟩ finish trace image imageTrace
      finalPaired
  refine ⟨image, imageTrace, initialKept.trans imageKept, mass, finalPaired, information.1,
    information.2, ?_, ?_⟩
  · intro policy
    constructor
    · rw [tailFactor policy, initialWord]
    · rw [sourceTail policy,
        HiddenSwap.phase_trace_ownPlay bounds initial horizon scheduler _ startTrace owner,
        (app).respond_ownPlay,
        ← HiddenSwap.phase_trace_ownPlay bounds initial horizon scheduler _ prior owner]
  · intro profile
    have originalFactor := PhaseProposal.historyReach_eq_transitionMass_mul_ownPlay
      runtime leaks bounds initial horizon scheduler profile ⟨some finish, trace⟩
    have imageFactor := PhaseProposal.historyReach_eq_transitionMass_mul_ownPlay
      runtime leaks bounds initial horizon scheduler profile
        ⟨some ⟨finish.remaining, finish.actor, image⟩, imageTrace⟩
    have common :
        (∏ who ∈ Finset.univ.erase owner,
          ((menu).information initial horizon scheduler).ownPlayReachProbability (profile who)
            (((menu).information initial horizon scheduler).ownPlay who imageTrace)) =
        ∏ who ∈ Finset.univ.erase owner,
          ((menu).information initial horizon scheduler).ownPlayReachProbability (profile who)
            (((menu).information initial horizon scheduler).ownPlay who trace) := by
      apply Finset.prod_congr rfl
      intro who included
      rw [(information.2 who (Finset.mem_erase.mp included).1).2]
    rw [imageFactor, originalFactor, mass]
    rw [← Finset.mul_prod_erase Finset.univ
      (fun who => ((menu).information initial horizon scheduler).ownPlayReachProbability
        (profile who) (((menu).information initial horizon scheduler).ownPlay who imageTrace))
          (Finset.mem_univ owner),
      ← Finset.mul_prod_erase Finset.univ
      (fun who => ((menu).information initial horizon scheduler).ownPlayReachProbability
        (profile who) (((menu).information initial horizon scheduler).ownPlay who trace))
          (Finset.mem_univ owner), common]
    rw [tailFactor (profile owner), initialWord,
      sourceTail (profile owner),
      HiddenSwap.phase_trace_ownPlay bounds initial horizon scheduler _ startTrace owner,
      (app).respond_ownPlay,
      ← HiddenSwap.phase_trace_ownPlay bounds initial horizon scheduler _ prior owner]
    simp only [InformationModel.ownPlayReachProbability]
    ring



end Vegas.EventGraphRuntime
