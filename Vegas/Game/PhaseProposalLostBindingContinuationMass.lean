/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseProposalLostBindingBeforeClosure
import Vegas.Game.PhaseProposalLostBindingForcedWait
import Vegas.Pending.PhaseBindingIdleMenu
import Interaction.ReactiveInvariantPrefix

/-! # Actual conditional history atoms on a lost binding slice

Only the designated sender's continuation policy is changed. Every appended
callback on the literal lost history has a singleton WAIT menu: before the
actual closing omission by owner order, afterward by permanent exclusion.
The existing continuation own-word factorization then identifies the actual
conditional history atom for every pair of policies of that sender.
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
local notation "model" => ReactiveApplication.ResponseMenu.information
  (PhaseCount.onePacketMenu runtime leaks bounds) initial horizon

private theorem callback_silent_continuation_atom
    (scheduler : (app).Scheduler) (owner : Player) (start finish : (app).Control)
    (startTrace : ((menu).protocol initial horizon scheduler).Trace (some start))
    (trace : ((menu).protocol initial horizon scheduler).Trace (some finish))
    (retained : TracePrefix startTrace trace)
    (silent : ∀ remaining execution
      (prior : ((menu).protocol initial horizon scheduler).Trace
        (some ⟨remaining, some owner, execution⟩)),
      TracePrefix startTrace prior → TracePrefix prior trace →
      PhaseCount.onePacketActions runtime leaks bounds owner (execution.recall owner)
        (execution.observe app owner) = {⟨none⟩})
    (first second : ∀ who, (model scheduler).BehavioralPolicy who)
    (foreign : ∀ who, who ≠ owner → first who = second who) :
    (model scheduler).runBehavioralFrom first (trace.length - startTrace.length)
        ⟨some start, startTrace⟩ ⟨some finish, trace⟩ =
      (model scheduler).runBehavioralFrom second (trace.length - startTrace.length)
        ⟨some start, startTrace⟩ ⟨some finish, trace⟩ := by
  classical
  obtain ⟨records, _words, origin, chance, _nonnegative, _mass, factored⟩ :=
    (model scheduler).exists_continuation_ownPlay_factor startTrace trace retained
  have ownOne (policy : (model scheduler).BehavioralPolicy owner) :
      (model scheduler).ownPlayReachProbability policy (records owner) = 1 := by
    have each (record : (model scheduler).InfoState owner × (app).Action)
        (included : record ∈ records owner) :
        (((policy record.1).map Subtype.val) (some record.2)).toReal = 1 := by
      obtain ⟨before, joint, legal, next, realized, fromStart, kept, observed, chosen⟩ :=
        origin owner record included
      have active := legal.2 owner
      rw [chosen] at active
      rcases before with ⟨beforeState, beforeTrace⟩
      cases beforeState with
      | none =>
          have impossible : (none : Option Player) = some owner := active.1
          cases impossible
      | some control =>
          have acting : control.actor = some owner := active.1
          rcases control with ⟨remaining, actor, execution⟩
          dsimp only at acting
          subst actor
          have beforeKept : TracePrefix beforeTrace trace :=
            (TracePrefix.extend TracePrefix.refl joint legal realized).trans kept
          have singleton := silent remaining execution beforeTrace fromStart beforeKept
          have response : record.2 = ⟨none⟩ := by
            have offered : record.2 ∈ PhaseCount.onePacketActions runtime leaks bounds owner
                (execution.recall owner) (execution.observe app owner) := active.2
            rw [singleton] at offered
            exact Finset.mem_singleton.mp offered
          have information : record.1 = some (execution.recall owner,
              execution.observe app owner) := by
            change ((menu).signals initial horizon scheduler).infoOf owner beforeTrace = record.1
              at observed
            rw [ReactiveApplication.ResponseMenu.info] at observed
            simpa only [ReactiveApplication.observe, ↓reduceIte] using observed.symm
          rw [information, response]
          exact phase_singleton_wait_atom runtime leaks bounds horizon initial scheduler owner
            (execution.recall owner) (execution.observe app owner) singleton policy
    have wordOne (word : List ((model scheduler).InfoState owner × (app).Action))
        (all : ∀ record ∈ word,
          (((policy record.1).map Subtype.val) (some record.2)).toReal = 1) :
        (model scheduler).ownPlayReachProbability policy word = 1 := by
      revert all
      induction word with
      | nil => intro _; rfl
      | cons record rest ih =>
          intro all
          change (((policy record.1).map Subtype.val) (some record.2)).toReal *
            (model scheduler).ownPlayReachProbability policy rest = 1
          rw [all record (List.mem_cons_self ..), one_mul]
          exact ih (fun selected included => all selected (List.mem_cons_of_mem _ included))
    exact wordOne _ each
  have product : (∏ who, (model scheduler).ownPlayReachProbability (first who) (records who)) =
      ∏ who, (model scheduler).ownPlayReachProbability (second who) (records who) := by
    apply Finset.prod_congr rfl
    intro who _included
    by_cases same : who = owner
    · subst who
      rw [ownOne, ownOne]
    · rw [foreign who same]
  apply (ENNReal.toReal_eq_toReal_iff' (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)).mp
  rw [factored, factored, product]

/-- On an actual whole lost-preparation history, the designated sender's
conditional atom is independent of its entire continuation policy. The
original initialized prefix and every other player's policy stay literal.
No reference-law equality is asserted on accepting branches. -/
theorem phase_lost_binding_continuation_atom
    (scheduler : (app).Scheduler) (ordered : graph.RevealRelaxedOrdered)
    (owner : Player) (start closing finish : (app).Control)
    (startTrace : ((menu).protocol initial horizon scheduler).Trace (some start))
    (closingTrace : ((menu).protocol initial horizon scheduler).Trace (some closing))
    (trace : ((menu).protocol initial horizon scheduler).Trace (some finish))
    (toClose : TracePrefix startTrace closingTrace)
    (same : start.execution.application.attempt = closing.execution.application.attempt)
    (after : (app).Control)
    (afterTrace : ((menu).protocol initial horizon scheduler).Trace (some after))
    (closingJoint : Player → Option (app).Action)
    (closingLegal : ((menu).protocol initial horizon scheduler).Legal
      (some closing) closingJoint)
    (closingRealized : some after ∈ (((menu).protocol initial horizon scheduler).step
      (some closing) ⟨closingJoint, closingLegal⟩).support)
    (closingStep : afterTrace = closingTrace.extend closingJoint closingLegal closingRealized)
    (fromClose : TracePrefix afterTrace trace)
    (current : RecoveryState graph)
    (effect : PhaseClosingEffect runtime leaks closing.execution after.execution current)
    (phase : RuntimePhase graph)
    (installed : closing.execution.application.phases.head? = some phase)
    (kind : phase.kind = .commitment) (omitted : graph.EventId) (payload : L.Ty)
    (binding : graph.outputLayout omitted = .binding owner payload)
    (inside : omitted ∈ phase.events) (finished : phase.Finished (phase.drain current))
    (coverage : (phase.drain current).FailureCoverage)
    (excludedEq : (phase.drain current).excluded = after.execution.application.current.excluded)
    (unaccepted : (phase.drain current).native.accepted (.inr omitted) = none)
    (entry : (app).PlayerEntry) (recorded : entry ∈ start.execution.recall owner)
    (material : WitnessedSubmission graph) (transmitted : entry.action.transmission = some material)
    (candidate : Handle graph) (named : material.call.packet = .commitment omitted candidate)
    (sameEntry : entry.beforeView.application.2.attempt = start.execution.application.attempt)
    (first second : ∀ who, (model scheduler).BehavioralPolicy who)
    (foreign : ∀ who, who ≠ owner → first who = second who) :
    (model scheduler).runBehavioralFrom first (trace.length - startTrace.length)
        ⟨some start, startTrace⟩ ⟨some finish, trace⟩ =
      (model scheduler).runBehavioralFrom second (trace.length - startTrace.length)
        ⟨some start, startTrace⟩ ⟨some finish, trace⟩ := by
  classical
  have afterKept : TracePrefix closingTrace afterTrace := by
    rw [closingStep]
    exact TracePrefix.extend (TracePrefix.refl : TracePrefix closingTrace closingTrace)
      closingJoint closingLegal closingRealized
  have closingKept := afterKept.trans fromClose
  have allKept := toClose.trans closingKept
  have excluded : owner ∈ after.execution.application.current.excluded := by
    rw [← excludedEq]
    exact RecoveryState.excluded_of_finished_unaccepted_binding (phase.drain current) phase
      finished coverage omitted inside owner payload binding unaccepted
  apply callback_silent_continuation_atom runtime leaks bounds plan inputs horizon scheduler owner
    start finish startTrace trace allKept _ first second foreign
  intro remaining execution prior fromStart kept
  by_cases before : prior.length ≤ closingTrace.length
  · have reaches := kept.reachesWithin.ancestor_comparable closingKept.reachesWithin before
    have beforeClose : TracePrefix prior closingTrace := reaches.tracePrefix
    have currentSame := phase_attempt_eq_between runtime leaks bounds plan inputs horizon scheduler
      start ⟨remaining, some owner, execution⟩ closing startTrace prior closingTrace fromStart
        beforeClose same
    have remembered := ((app).reaches_recall_prefix initial horizon scheduler
      ((menu).reaches_raw initial horizon scheduler fromStart.reachesWithin) start
        ⟨remaining, some owner, execution⟩ rfl rfl owner).subset recorded
    exact phase_lost_binding_callback_silent runtime leaks bounds plan inputs horizon scheduler
      ordered remaining owner execution prior closing closingTrace beforeClose currentSame
        after.execution current effect phase installed kind omitted payload binding inside
          unaccepted
          entry remembered material transmitted candidate named
            ((sameEntry.trans same).trans currentSame.symm)
  · have deeper : afterTrace.length ≤ prior.length := by
      rw [closingStep, Trace.length]
      omega
    have reaches := fromClose.reachesWithin.ancestor_comparable kept.reachesWithin deeper
    have fromAfter : TracePrefix afterTrace prior := reaches.tracePrefix
    let excludedInvariant : (app).Invariant (fun state => owner ∈ state.current.excluded) :=
      { submit := fun state who response present =>
          (phaseApplication_exclusion_monotone runtime leaks).submit state who response present
        handle := fun state message next present handled =>
          (phaseApplication_exclusion_monotone runtime leaks).handle state message next handled
            present
        environment := fun state command next present supported =>
          (phaseApplication_exclusion_monotone runtime leaks).environment state command next
            supported present }
    have stillExcluded := excludedInvariant.tracePrefix menu initial horizon scheduler after
      ⟨remaining, some owner, execution⟩ afterTrace prior fromAfter excluded
    apply PhaseCount.onePacketActions_eq_singleton_of_no_request runtime leaks bounds plan inputs
      horizon scheduler remaining owner execution prior
    intro coordinate request
    exact request.2.2.2.2 stillExcluded

end Vegas.EventGraphRuntime
