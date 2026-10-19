/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseProposalOpeningSupport
import Vegas.Game.PhaseProposalQueryDomain
import Vegas.Pending.PhaseBindingIdleMenu
import Vegas.Pending.ReactiveFiniteCompiler

/-! # The actual reference fallback is absent on every genuine counted input -/

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

private theorem baseClasses_full_of_silent
    (values : ∀ who (key : setup.ProposalRecoveryComponent who),
      PMF (setup.CommitRecoveryValueChoice who key.1))
    (rates : PhaseProposalRates) (owner : Player) (past : List (app).PlayerEntry)
    (view : (app).PlayerView)
    (silent : PhaseCount.onePacketActions runtime leaks bounds owner past view = {⟨none⟩}) :
    FullSupport (phaseProposalBaseClasses setup mode runtime leaks bounds plan values rates owner
      past view) := by
  classical
  have unique (response : PhaseProposal.Response runtime leaks bounds owner past view) :
      response.val = ⟨none⟩ := by
    have present := response.property
    simpa only [silent, Finset.mem_singleton] using present
  let : Subsingleton (PhaseProposal.ResponseClass runtime leaks bounds owner past view) :=
    ⟨fun first second => by
      obtain ⟨left, leftEq⟩ := first.property
      obtain ⟨right, rightEq⟩ := second.property
      have same : left = right := Subtype.ext ((unique left).trans (unique right).symm)
      subst right
      exact Subtype.ext (leftEq.symm.trans rightEq)⟩
  intro chosen
  rw [eq_pure_of_subsingleton
    (phaseProposalBaseClasses setup mode runtime leaks bounds plan values rates owner past view)
    chosen]
  exact (PMF.mem_support_pure_iff _ _).mpr rfl

/-- Actual menu shapes and the actual genuine source query remove support
totalization at EVERY counted input. Original-law histories may include any
prior counted deviations, private preparation failures, omissions or debt.
No clean-path, desired source counterpart or support premise is supplied. -/
theorem phaseProposalBaseClasses_fullSupport_of_counted
    (complete : leaks = MessageNetwork.completePendingObservation)
    (covered : bounds.CoversOutputValues)
    (maximal : plan.phases.IsChain fun first last =>
      first.kind ≠ last.kind ∨ first.kind = .sample)
    (values : ∀ who (key : setup.ProposalRecoveryComponent who),
      PMF (setup.CommitRecoveryValueChoice who key.1))
    (fullValues : ∀ who key, FullSupport (values who key))
    (rates : PhaseProposalRates) (waitPositive : 0 < rates.waiting.val)
    (waitBelow : rates.waiting.val < 1) (slotPositive : 0 < rates.slots.val)
    (badPositive : 0 < rates.badPreparation.val) (badBelow : rates.badPreparation.val < 1)
    (horizon : Nat) (scheduler : (app).Scheduler) (remaining : Nat) (owner : Player)
    (execution : (app).Execution)
    (trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (setup.initialLaw.map fun draw => PhaseRuntimeState.initial plan (encodeInputs draw))
      horizon scheduler).Trace (some ⟨remaining, some owner, execution⟩)) :
    FullSupport (phaseProposalBaseClasses setup mode runtime leaks bounds plan values rates owner
      (execution.recall owner) (execution.observe app owner)) := by
  classical
  let inputs := setup.initialLaw.map encodeInputs
  have counted : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace
        (some ⟨remaining, some owner, execution⟩) := by
    dsimp only [inputs]
    rw [PMF.map_comp]
    exact trace
  by_cases absent : ∀ coordinate, ¬execution.application.SeedRequest owner coordinate
  · exact baseClasses_full_of_silent setup mode runtime leaks bounds plan values rates owner
      (execution.recall owner) (execution.observe app owner)
      (PhaseCount.onePacketActions_eq_singleton_of_no_request runtime leaks bounds plan inputs
        horizon scheduler remaining owner execution counted absent)
  · obtain ⟨⟨attempt, event⟩, request⟩ := not_forall.mp absent
    have request : execution.application.SeedRequest owner ⟨attempt, event⟩ := not_not.mp request
    have sameAttempt : attempt = execution.application.attempt := request.1
    subst attempt
    cases node : nodeView (serviceGraph setup mode) event with
    | bind actor payload binding code =>
        have same : actor = owner := Option.some.inj
          (((serviceGraph setup mode).actor?_of_outputLayout_binding binding).symm.trans
            request.2.2.2.1)
        subst actor
        have bounded := covered event
        rw [binding] at bounded
        have results := phaseProposalBindingResults_fullSupport_of_binding setup mode runtime leaks
          complete plan maximal values fullValues rates badPositive badBelow horizon scheduler
          ((PhaseCount.onePacketMenu runtime leaks bounds).toRawTrace _ horizon scheduler trace)
          owner rfl event payload binding request
        exact phaseProposalBindingClasses_fullSupport setup mode runtime leaks bounds plan values
          rates waitPositive waitBelow slotPositive inputs horizon scheduler remaining owner
            execution counted event payload binding request bounded results
    | resolve actor payload binding checks outputEq codeEq =>
        have actualActor : (serviceGraph setup mode).actor? event = some actor := by
          change (((serviceGraph setup mode).nodes event).actor) = _
          rw [← EventCode.actor_cast outputEq ((serviceGraph setup mode).nodes event), codeEq]
          rfl
        have same : actor = owner := Option.some.inj (actualActor.symm.trans request.2.2.2.1)
        subst actor
        have bounded := covered event
        rw [outputEq] at bounded
        exact phaseProposalOpeningClasses_fullSupport setup mode runtime leaks bounds plan values
          rates waitPositive waitBelow inputs horizon scheduler remaining owner execution counted
            event payload binding checks outputEq codeEq node request bounded
    | sample payload law outputEq codeEq =>
        have actualActor : (serviceGraph setup mode).actor? event = none := by
          change (((serviceGraph setup mode).nodes event).actor) = _
          rw [← EventCode.actor_cast outputEq ((serviceGraph setup mode).nodes event), codeEq]
          rfl
        have impossible := request.2.2.2.1
        rw [actualActor] at impossible
        cases impossible

end Vegas
