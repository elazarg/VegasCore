/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseProposalOrdinarySupport

/-! # Every usable actual counted response occurs in the ordinary comparison -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
  (runtime : EventGraphRuntime (serviceGraph setup mode))
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))
  (bounds : MessageBounds (serviceGraph setup mode))
  (plan : RuntimePhasePlan (serviceGraph setup mode))

local notation "app" => phaseApplication runtime leaks

/-- No submitted binding preparation fails to decode at its declared type.
This condition says nothing about any source guard or later service outcome. -/
def phaseProposalResponsePrepared (response : (app).Action) : Prop :=
  ∀ (material : WitnessedSubmission (serviceGraph setup mode)) event candidate,
    response.transmission = some material → material.call.packet = .commitment event candidate →
      PhaseProposal.bindingPreparation material ≠ none

/-- Actual shape/query facts provide ordinary support for every prepared
response, including all raw aliases and forced WAIT at exhausted/debt inputs. -/
theorem phaseProposalOrdinaryResponses_supported_of_counted
    (complete : leaks = MessageNetwork.completePendingObservation)
    (covered : bounds.CoversOutputValues)
    (maximal : plan.phases.IsChain fun first last =>
      first.kind ≠ last.kind ∨ first.kind = .sample)
    (values : ∀ who (key : setup.ProposalRecoveryComponent who),
      PMF (setup.CommitRecoveryValueChoice who key.1))
    (fullValues : ∀ who key, FullSupport (values who key))
    (rates : PhaseProposalRates) (waitPositive : 0 < rates.waiting.val)
    (waitBelow : rates.waiting.val < 1) (slots : 0 < rates.slots.val)
    (aliases : 0 < rates.aliases.val)
    (horizon : Nat) (scheduler : (app).Scheduler) (remaining : Nat) (owner : Player)
    (execution : (app).Execution)
    (trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (setup.initialLaw.map fun draw => PhaseRuntimeState.initial plan (encodeInputs draw))
      horizon scheduler).Trace (some ⟨remaining, some owner, execution⟩))
    (response : PhaseProposal.Response runtime leaks bounds owner (execution.recall owner)
      (execution.observe app owner))
    (prepared : phaseProposalResponsePrepared setup mode runtime leaks response.val) :
    response ∈ (phaseProposalOrdinaryResponses setup mode runtime leaks bounds plan values rates
      owner (execution.recall owner) (execution.observe app owner)).support := by
  classical
  let inputs := setup.initialLaw.map encodeInputs
  have counted : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace
        (some ⟨remaining, some owner, execution⟩) := by
    dsimp only [inputs]
    rw [PMF.map_comp]
    exact trace
  let past := execution.recall owner
  let view := execution.observe app owner
  by_cases absent : ∀ coordinate, ¬execution.application.SeedRequest owner coordinate
  · have silent := PhaseCount.onePacketActions_eq_singleton_of_no_request runtime leaks bounds
      plan inputs horizon scheduler remaining owner execution counted absent
    have unique (chosen : PhaseProposal.Response runtime leaks bounds owner past view) :
        chosen.val = ⟨none⟩ := by
      have member := chosen.property
      change chosen.val ∈ PhaseCount.onePacketActions runtime leaks bounds owner
        (execution.recall owner) (execution.observe app owner) at member
      have same := congrArg (fun choices : Finset (app).Action => chosen.val ∈ choices) silent
      exact Finset.mem_singleton.mp (Eq.mp same member)
    let : Subsingleton (PhaseProposal.Response runtime leaks bounds owner past view) :=
      ⟨fun first second => Subtype.ext ((unique first).trans (unique second).symm)⟩
    rw [eq_pure_of_subsingleton
      (phaseProposalOrdinaryResponses setup mode runtime leaks bounds plan values rates owner
        past view) response]
    exact (PMF.mem_support_pure_iff _ _).mpr rfl
  · obtain ⟨⟨attempt, event⟩, offered⟩ := not_forall.mp absent
    have request : execution.application.SeedRequest owner ⟨attempt, event⟩ := not_not.mp offered
    have sameAttempt := request.1
    change attempt = execution.application.attempt at sameAttempt
    subst attempt
    cases node : nodeView (serviceGraph setup mode) event with
    | bind actor payload binding code =>
        have same : actor = owner := Option.some.inj
          (((serviceGraph setup mode).actor?_of_outputLayout_binding binding).symm.trans
            request.2.2.2.1)
        subst actor
        rcases response with ⟨⟨transmission⟩, member⟩
        cases transmission with
        | none =>
            obtain ⟨draw, native⟩ := phaseNativeInvariant_history runtime leaks plan inputs horizon
              scheduler ((PhaseCount.onePacketMenu runtime leaks bounds).toRawTrace _ horizon
                scheduler counted)
            apply phaseProposalOrdinaryResponses_mem_of_class setup mode runtime leaks bounds plan
              values rates aliases owner past view
            apply phaseProposalBaseClasses_mem_of_response setup mode runtime leaks bounds plan
              values rates.ordinary owner past view ⟨⟨none⟩, member⟩
            unfold phaseProposalBasePolicy
            rw [phasePolicyDispatch_binding setup mode runtime leaks _ _ execution native owner
              event payload binding request]
            exact mem_support_mix_left _ _ _ waitPositive
              ((PMF.mem_support_pure_iff _ _).mpr rfl)
        | some material =>
            obtain ⟨serial, opening, evidence, rfl, _bounded, _fresh⟩ :=
              PhaseCount.onePacket_binding_shape runtime leaks bounds plan
                (serviceGraph_revealRelaxedOrdered setup mode) inputs horizon scheduler remaining
                  owner execution counted event payload binding request material member
            cases decoded : opening.bind (fun raw => raw.as? payload) with
            | none =>
                have impossible := prepared _ event (owner, .prepared serial) rfl rfl
                apply False.elim
                apply impossible
                simp only [PhaseProposal.bindingPreparation, binding, decoded, Option.map_none]
            | some value =>
                exact phaseProposalOrdinaryBindingResponses_supported setup mode runtime leaks
                  bounds plan complete covered maximal values fullValues rates waitBelow slots
                    aliases horizon scheduler remaining owner execution trace event payload binding
                      request serial opening evidence member value decoded
    | resolve actor payload binding checks outputEq codeEq =>
        have actualActor : (serviceGraph setup mode).actor? event = some actor := by
          change (((serviceGraph setup mode).nodes event).actor) = _
          rw [← EventCode.actor_cast outputEq ((serviceGraph setup mode).nodes event), codeEq]
          rfl
        have same : actor = owner := Option.some.inj (actualActor.symm.trans request.2.2.2.1)
        subst actor
        have bounded := covered event
        rw [outputEq] at bounded
        apply phaseProposalOrdinaryResponses_mem_of_class setup mode runtime leaks bounds plan
          values rates aliases owner past view
        exact phaseProposalOpeningClasses_fullSupport setup mode runtime leaks bounds plan values
          rates.ordinary waitPositive waitBelow inputs horizon scheduler remaining owner execution
            counted event payload binding checks outputEq codeEq node request bounded _
    | sample payload law outputEq codeEq =>
        have actualActor : (serviceGraph setup mode).actor? event = none := by
          change (((serviceGraph setup mode).nodes event).actor) = _
          rw [← EventCode.actor_cast outputEq ((serviceGraph setup mode).nodes event), codeEq]
          rfl
        have impossible := request.2.2.2.1
        rw [actualActor] at impossible
        cases impossible

end Vegas
