/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.PhaseProposalBindingSupport
import Vegas.Pending.PhaseProposalCanonicalOpening

/-! # Genuine publication classes exhaust the reference opening law -/

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

/-- A current truthful opening is the only nonsilent packet/preparation class
available at an actual publication callback. Failed guards remain allowed;
neither successful publication nor timely inclusion is assumed. -/
theorem phaseProposalOpeningClasses_fullSupport
    (values : ∀ who (key : setup.ProposalRecoveryComponent who),
      PMF (setup.CommitRecoveryValueChoice who key.1))
    (rates : PhaseProposalRates) (waitPositive : 0 < rates.waiting.val)
    (waitBelow : rates.waiting.val < 1)
    (inputs : PMF (serviceGraph setup mode).Inputs) (horizon : Nat)
    (scheduler : (app).Scheduler) (remaining : Nat) (owner : Player)
    (execution : (app).Execution)
    (trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace
        (some ⟨remaining, some owner, execution⟩))
    (event : (serviceGraph setup mode).EventId) (payload : L.Ty)
    (binding : FieldRef (serviceGraph setup mode).layout (.binding owner payload))
    (checks : List (GuardCheck (serviceGraph setup mode).layout payload))
    (outputEq : (serviceGraph setup mode).outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventCode (serviceGraph setup mode).layout) outputEq)
      ((serviceGraph setup mode).nodes event) = .resolve owner payload binding checks)
    (node : nodeView (serviceGraph setup mode) event =
      .resolve owner payload binding checks outputEq codeEq)
    (request : execution.application.SeedRequest owner ⟨execution.application.attempt, event⟩)
    (boundedValues : ∀ value : L.Val payload, (⟨payload, value⟩ : Raw L) ∈ bounds.values) :
    FullSupport (phaseProposalBaseClasses setup mode runtime leaks bounds plan values rates owner
      (execution.recall owner) (execution.observe app owner)) := by
  classical
  let past := execution.recall owner
  let view := execution.observe app owner
  let opens := fun (_ : List (app).PlayerEntry) (_ : (app).PlayerView) =>
    mix rates.waiting.val rates.waiting.property.1 rates.waiting.property.2
      (PMF.pure false) (PMF.pure true)
  have raw := (PhaseCount.onePacketMenu runtime leaks bounds).toRawTrace _ horizon scheduler trace
  obtain ⟨draw, native⟩ := phaseNativeInvariant_history runtime leaks plan inputs horizon scheduler
    raw
  have base : phaseProposalBasePolicy setup mode runtime leaks bounds plan values rates owner
      past view = PhaseCount.phaseOpeningPolicy runtime leaks bounds owner event payload binding
        opens past view := by
    unfold phaseProposalBasePolicy
    exact phasePolicyDispatch_opening setup mode runtime leaks _ _ execution native owner event
      payload binding checks outputEq codeEq request
  have silent : (⟨none⟩ : (app).Action) ∈
      (phaseProposalBasePolicy setup mode runtime leaks bounds plan values rates owner
        past view).support := by
    rw [base]
    unfold PhaseCount.phaseOpeningPolicy
    split
    · dsimp only
      split
      · exact (PMF.mem_support_map_iff _ _ _).mpr
          ⟨false, mem_support_mix_left _ _ _ waitPositive
            ((PMF.mem_support_pure_iff _ _).mpr rfl), rfl⟩
      · exact (PMF.mem_support_pure_iff _ _).mpr rfl
    · exact (PMF.mem_support_pure_iff _ _).mpr rfl
  intro chosen
  obtain ⟨response, projects⟩ := chosen.property
  have classEq : PhaseProposal.projectResponse runtime leaks bounds owner past view response =
      chosen := Subtype.ext projects
  rw [← classEq]
  rcases response with ⟨⟨transmission⟩, member⟩
  cases transmission with
  | none =>
      exact phaseProposalBaseClasses_mem_of_response setup mode runtime leaks bounds plan values
        rates owner past view ⟨⟨none⟩, member⟩ silent
  | some material =>
      obtain ⟨candidate, value, call, stored, accepted, _fixed⟩ :=
        PhaseCount.onePacket_opening_shape runtime leaks bounds plan
          (serviceGraph_revealRelaxedOrdered setup mode) inputs horizon scheduler remaining owner
            execution trace event payload binding checks outputEq codeEq node request material
              member
      have unsent := PhaseCount.unsent_of_nonsilent runtime leaks bounds plan
        (serviceGraph_revealRelaxedOrdered setup mode) inputs horizon scheduler remaining owner
          execution trace ⟨execution.application.attempt, event⟩ request material member
      obtain ⟨actual, actualAccepted, available⟩ :=
        PhaseCount.phaseOpeningPolicy_of_history runtime leaks bounds plan inputs horizon scheduler
          trace owner event payload binding checks outputEq codeEq node request unsent value stored
            (boundedValues value) opens
      have actualEq : actual = candidate := Option.some.inj (actualAccepted.symm.trans accepted)
      subst actual
      have canonicalSupported :
          PhaseCount.phaseOpeningResponse runtime leaks event candidate ⟨payload, value⟩ ∈
            (PhaseCount.phaseOpeningPolicy runtime leaks bounds owner event payload binding opens
              past view).support := by
        rw [available]
        exact (PMF.mem_support_map_iff _ _ _).mpr
          ⟨true, mem_support_mix_right _ _ _ waitBelow
            ((PMF.mem_support_pure_iff _ _).mpr rfl), rfl⟩
      have canonicalMember := PhaseCount.phaseOpeningPolicy_covered runtime leaks bounds owner event
        payload binding opens past view _ canonicalSupported
      rcases material with ⟨⟨packet, preparation⟩, evidence⟩
      change packet = .opening event candidate ⟨payload, value⟩ at call
      subst packet
      have same := PhaseProposal.responseClass_opening runtime leaks bounds owner past view event
        candidate ⟨payload, value⟩ preparation evidence member canonicalMember
      have projected : PhaseProposal.projectResponse runtime leaks bounds owner past view
          ⟨⟨some ⟨⟨.opening event candidate ⟨payload, value⟩, preparation⟩, evidence⟩⟩, member⟩ =
        PhaseProposal.projectResponse runtime leaks bounds owner past view
          ⟨PhaseCount.phaseOpeningResponse runtime leaks event candidate ⟨payload, value⟩,
            canonicalMember⟩ := Subtype.ext same
      rw [projected]
      apply phaseProposalBaseClasses_mem_of_response setup mode runtime leaks bounds plan values
        rates owner past view ⟨_, canonicalMember⟩
      rwa [base]

end Vegas
