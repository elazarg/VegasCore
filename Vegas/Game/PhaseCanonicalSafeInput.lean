/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseCanonicalBindingProtection
import Vegas.Game.PhaseCanonicalOpeningProtection
import Vegas.Pending.PhaseSentMenu
import Vegas.Pending.PhaseBindingIdleMenu

/-! # Protected requests or singleton menus on actual canonical callbacks -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
  (runtime : EventGraphRuntime (serviceGraph setup mode))
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))
  (bounds : MessageBounds (serviceGraph setup mode)) (wellFormed : setup.WellFormed)
  (source : ∀ owner, setup.intendedModel.BehavioralPolicy owner)
  (assessment : setup.commitRecoveryModel.BehavioralAssessment)
  (copies : (setup.commitRecoveryRestriction wellFormed).ExtendsProfile source assessment.strategy)
  (continuing : ∀ owner (site : setup.commitRecoveryModel.InformationSite owner),
    ∀ choice ∈ (assessment.strategy owner site.1).support,
      setup.CommitRecoveryContinues owner site.1 choice.1)
  (plan : RuntimePhasePlan (serviceGraph setup mode))
  (maximal : plan.phases.IsChain fun before after =>
    before.kind ≠ after.kind ∨ before.kind = .sample)
  (horizon : Nat) (scheduler : (phaseApplication runtime leaks).Scheduler)
  (capacity : horizon ≤ bounds.candidateCount)
  (delay bound : (serviceGraph setup mode).EventId → Nat)

local notation "P" => phaseApplication runtime leaks
local notation "start" =>
  PMF.map (PhaseRuntimeState.initial plan) (setup.initialLaw.map encodeInputs)

include copies continuing maximal capacity

/-- Every actual clear canonical callback either has a protected unsent
binding or opening request, or has exactly the silent response available.
The latter includes sent requests and callbacks without any ready request. -/
theorem phaseSourcePolicy_protected_or_singleton
    (opportunity : PhaseService.Opportunity runtime leaks start horizon scheduler delay)
    (timely : runtime.AsyncTimely delay bound)
    (remaining : Nat) (owner : Player) (execution : (P).Execution)
    (trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol start horizon
      scheduler).Trace (some ⟨remaining, some owner, execution⟩))
    (clear : execution.application.current.excluded = ∅)
    (consistent : ∀ player, (phaseSourcePolicy setup mode runtime leaks bounds wellFormed assessment
      player).Consistent (execution.recall player))
    (values : ∀ event actor payload,
      ((serviceGraph setup mode).outputLayout event = .binding actor payload ∨
        (serviceGraph setup mode).outputLayout event = .publication payload) →
      ∀ value : L.Val payload, (⟨payload, value⟩ : Raw L) ∈ bounds.values) :
    (∃ event : (serviceGraph setup mode).EventId,
      execution.application.SeedRequest owner ⟨execution.application.attempt, event⟩ ∧
      (∀ message ∈ (P).outputs (execution.recall owner),
        PhaseCount.event? message.payload ≠ some ⟨execution.application.attempt, event⟩) ∧
      ((∃ payload, (serviceGraph setup mode).outputLayout event = .binding owner payload) ∨
        ((serviceGraph setup mode).outputLayout event).IsPublication) ∧
      execution.application.current.native.publicView.InclusionFitsDeadline runtime bound event) ∨
    PhaseCount.onePacketActions runtime leaks bounds owner (execution.recall owner)
      (execution.observe (P) owner) = {⟨none⟩} := by
  classical
  let inputs := setup.initialLaw.map encodeInputs
  let menu := PhaseCount.onePacketMenu runtime leaks bounds
  by_cases offered : ∃ coordinate, execution.application.SeedRequest owner coordinate
  · obtain ⟨⟨attempt, event⟩, request⟩ := offered
    have sameAttempt : attempt = execution.application.attempt := request.1
    subst attempt
    by_cases sent : ∃ message ∈ (P).outputs (execution.recall owner),
        PhaseSeedScheduler.ownPacket ⟨execution.application.attempt, event⟩ owner message = true
    · exact Or.inr (PhaseCount.onePacketActions_eq_singleton_of_sent runtime leaks bounds plan
        (serviceGraph_revealRelaxedOrdered setup mode) inputs horizon scheduler remaining owner
          execution trace ⟨execution.application.attempt, event⟩ request sent)
    have raw := menu.toRawTrace start horizon scheduler trace
    have inputRecall := (P).history_inputRecall start horizon scheduler raw
    have unsent : ∀ message ∈ (P).outputs (execution.recall owner),
        PhaseCount.event? message.payload ≠ some ⟨execution.application.attempt, event⟩ := by
      intro message member named
      apply sent
      have authored : message.sender = owner := by
        rw [← inputRecall owner] at member
        exact of_decide_eq_true (List.mem_filter.mp member).2
      obtain ⟨actual, called, addressed⟩ := Option.map_eq_some_iff.mp named
      have attemptEq := congrArg CommitAttemptEvent.attempt addressed
      have eventEq := congrArg CommitAttemptEvent.event addressed
      refine ⟨message, member, ?_⟩
      simp only [PhaseSeedScheduler.ownPacket, decide_eq_true_eq]
      change actual = event at eventEq
      rw [eventEq] at called
      exact ⟨authored, attemptEq, called⟩
    have owned := request.2.2.2.1
    cases node : nodeView (serviceGraph setup mode) event with
    | bind actor payload outputEq codeEq =>
        have acting : (serviceGraph setup mode).actor? event = some actor :=
          (EventCode.actor_cast outputEq _).symm.trans (congrArg EventCode.actor codeEq)
        have same : actor = owner := Option.some.inj (acting.symm.trans owned)
        subst actor
        have initialEq : start = setup.initialLaw.map
            (fun draw => PhaseRuntimeState.initial plan (encodeInputs draw)) :=
          PMF.map_comp encodeInputs setup.initialLaw (PhaseRuntimeState.initial plan)
        have simpleTrace := initialEq ▸ trace
        have simpleOpportunity := initialEq ▸ opportunity
        have fitting := phaseSourcePolicy_unsent_binding_protected setup mode runtime leaks
          bounds wellFormed assessment continuing plan maximal horizon scheduler capacity
            delay bound simpleOpportunity timely ⟨remaining, some owner, execution⟩
              simpleTrace clear owner (consistent owner) event payload outputEq request unsent
                (values event owner payload (Or.inl outputEq))
        exact Or.inl ⟨event, request, unsent, Or.inl ⟨payload, outputEq⟩, fitting⟩
    | resolve actor payload binding checks outputEq codeEq =>
        have publication : ((serviceGraph setup mode).outputLayout event).IsPublication := by
          rw [outputEq]
          trivial
        have fitting := phaseSourcePolicy_unsent_opening_protected setup mode runtime leaks bounds
          wellFormed source assessment copies plan maximal horizon scheduler delay bound opportunity
            timely ⟨remaining, some owner, execution⟩ trace clear owner consistent event publication
              request unsent (fun payload found => values event owner payload (Or.inr found))
        exact Or.inl ⟨event, request, unsent, Or.inr publication, fitting⟩
    | sample payload law outputEq codeEq =>
        have noActor : (serviceGraph setup mode).actor? event = none :=
          (EventCode.actor_cast outputEq _).symm.trans (congrArg EventCode.actor codeEq)
        rw [noActor] at owned
        cases owned
  · exact Or.inr (PhaseCount.onePacketActions_eq_singleton_of_no_request runtime leaks bounds plan
      inputs horizon scheduler remaining owner execution trace clear (fun coordinate requested =>
        offered ⟨coordinate, requested⟩))

end Vegas
