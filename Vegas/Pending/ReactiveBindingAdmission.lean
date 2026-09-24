/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveBinding
import Vegas.Pending.ReactiveCommitmentProtection
import Vegas.Pending.ReactiveAssociationEvidence
import Interaction.ReactivePendingRetention

/-! # Admission of a prescribed pending binding after arbitrary reactions

The fixed candidate remains unused while its event is unfinished, and every
unfinished event has a vacant association cell. Thus readiness and the deadline
are the only application-admission premises left at inclusion. Network choice,
pending-envelope retention, and a timely service opportunity remain distinct
obligations; these theorems do not assume or assert a service correspondence.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open GameTheory.Math.Probability Interaction EventGraph

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

theorem reactiveBinding_continuation_resources (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (who : Player) (event : graph.EventId) (payload : L.Ty)
    (result : PublicationResult (L.Val payload)) (serial : Nat)
    (execution next : (runtime.reactiveApplication leaks).Execution)
    (valid : execution.application.BindingInvariant)
    (fixed : runtime.ReactiveCommitmentsFixed leaks execution)
    (fresh : execution.application.candidates.lookup (who, .prepared serial) = .fresh)
    (policy : graph.BehavioralPolicy who)
    (players : Player → (runtime.reactiveApplication leaks).Policy)
    (prescribed : players who = runtime.prescribedReactivePolicy leaks who policy)
    (scheduler : (runtime.reactiveApplication leaks).Scheduler) (rounds : Nat)
    (reached : next ∈ ((runtime.reactiveApplication leaks).runRounds scheduler players rounds
      (execution.respond (runtime.reactiveApplication leaks) who
        (runtime.reactiveBinding leaks who event payload result serial))).support)
    (unfinished : event ∉ next.application.config.cut.completed) :
    next.application.accepted (.inr event) = none ∧
      next.application.HandleUnused (who, .prepared serial) := by
  let submitted := execution.respond (runtime.reactiveApplication leaks) who
    (runtime.reactiveBinding leaks who event payload result serial)
  have unused : execution.application.HandleUnused (who, .prepared serial) :=
    fun field associated => valid.accepted_fixed field _ associated fresh
  have protection := runtime.reactiveBinding_protection leaks who event payload result serial
    execution fixed fresh unused
  have protectedAfter := (runtime.reactiveCandidateProtection_policy leaks who event
    (who, .prepared serial) rfl policy players prescribed).runRounds scheduler rounds
      submitted next protection reached
  have associatedAfter := (ReactiveApplication.Invariant.policyInvariant
    (runtime.reactiveApplication leaks) (runtime.reactiveBindingInvariant leaks) players).runRounds
      scheduler rounds submitted next
      ((runtime.reactiveBindingInvariant leaks).respond execution who
        (runtime.reactiveBinding leaks who event payload result serial) valid) reached
  refine ⟨?_, protectedAfter.unused unfinished⟩
  cases associated : next.application.accepted (.inr event) with
  | none => rfl
  | some candidate =>
      exact False.elim (unfinished
        (associatedAfter.toAssociationInvariant.accepted_complete event candidate associated))

/-- A ready, timely inclusion of the actual compiler's pending binding cannot
be rejected because another event has consumed its fresh candidate. Only its
owner follows the prescribed policy; every intervening opponent action,
passive observation rule, and scheduler remains arbitrary. -/
theorem reactiveDecision_binding_continuation_admitted (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (owner : Player) (event : graph.EventId) (payload : L.Ty)
    (outputEq : graph.outputLayout event = .binding owner payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .bind owner payload)
    (node : nodeView graph event = .bind owner payload outputEq codeEq)
    (action : graph.Action event) (serial : Nat)
    (execution next : (runtime.reactiveApplication leaks).Execution)
    (valid : execution.application.BindingInvariant)
    (fixed : runtime.ReactiveCommitmentsFixed leaks execution)
    (allocated : reactiveFreshSlot
      ((runtime.reactiveApplication leaks).observePlayer execution.application owner) = some serial)
    (policy : graph.BehavioralPolicy owner)
    (players : Player → (runtime.reactiveApplication leaks).Policy)
    (prescribed : players owner = runtime.prescribedReactivePolicy leaks owner policy)
    (scheduler : (runtime.reactiveApplication leaks).Scheduler) (rounds : Nat)
    (reached : next ∈ ((runtime.reactiveApplication leaks).runRounds scheduler players rounds
      (execution.respond (runtime.reactiveApplication leaks) owner
        (runtime.reactiveDecision leaks owner event action
          ((runtime.reactiveApplication leaks).observePlayer
            execution.application owner)))).support)
    (pending : next.network.lookup (owner, execution.network.nextSerial owner) =
      some ⟨(owner, execution.network.nextSerial owner),
        ⟨.commitment event (owner, .prepared serial), none⟩⟩)
    (ready : next.application.config.cut.Ready event)
    (timely : next.application.WithinDeadline runtime event) :
    FinDist.pure ((next.includePending (runtime.reactiveApplication leaks)
      (owner, execution.network.nextSerial owner)).application.config) =
        next.application.config.step event ready action ∧
    (next.includePending (runtime.reactiveApplication leaks)
      (owner, execution.network.nextSerial owner)).receipts =
        next.receipts ++ [((owner, execution.network.nextSerial owner), true)] := by
  have fresh := reactiveFreshSlot_spec
    ((runtime.reactiveApplication leaks).observePlayer execution.application owner) serial allocated
  have same := runtime.reactiveDecision_binding_eq leaks owner owner event payload outputEq codeEq
    node action _ serial allocated
  have bindingReached := reached
  rw [same] at bindingReached
  obtain ⟨vacant, unused⟩ := runtime.reactiveBinding_continuation_resources leaks owner event
    payload (cast (congrArg EventField.Action outputEq) action) serial execution next valid fixed
    fresh policy players prescribed scheduler rounds bindingReached ready.1
  exact runtime.reactiveDecision_binding_continuation_step leaks owner event payload outputEq
    codeEq node action serial execution next allocated scheduler players rounds reached pending
      ready timely vacant unused

/-- Any single wire inclusion either retains this original envelope or applies
exactly its chosen graph action. At-most-once service cannot consume it through
a rejected inclusion while these readiness and deadline hypotheses hold. -/
theorem reactiveDecision_binding_retained_or_realized (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (owner : Player) (event : graph.EventId) (payload : L.Ty)
    (outputEq : graph.outputLayout event = .binding owner payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .bind owner payload)
    (node : nodeView graph event = .bind owner payload outputEq codeEq)
    (action : graph.Action event) (serial : Nat)
    (execution next : (runtime.reactiveApplication leaks).Execution)
    (valid : execution.application.BindingInvariant)
    (fixed : runtime.ReactiveCommitmentsFixed leaks execution)
    (allocated : reactiveFreshSlot
      ((runtime.reactiveApplication leaks).observePlayer execution.application owner) = some serial)
    (policy : graph.BehavioralPolicy owner)
    (players : Player → (runtime.reactiveApplication leaks).Policy)
    (prescribed : players owner = runtime.prescribedReactivePolicy leaks owner policy)
    (scheduler : (runtime.reactiveApplication leaks).Scheduler) (rounds : Nat)
    (reached : next ∈ ((runtime.reactiveApplication leaks).runRounds scheduler players rounds
      (execution.respond (runtime.reactiveApplication leaks) owner
        (runtime.reactiveDecision leaks owner event action
          ((runtime.reactiveApplication leaks).observePlayer
            execution.application owner)))).support)
    (pending : (⟨(owner, execution.network.nextSerial owner),
        ⟨.commitment event (owner, .prepared serial), none⟩⟩ :
          Message Player (WitnessedPacket graph)) ∈ next.network.pending)
    (ready : next.application.config.cut.Ready event)
    (timely : next.application.WithinDeadline runtime event) (selected : MessageId Player) :
    (⟨(owner, execution.network.nextSerial owner),
        ⟨.commitment event (owner, .prepared serial), none⟩⟩ :
          Message Player (WitnessedPacket graph)) ∈
      (next.includePending (runtime.reactiveApplication leaks) selected).network.pending ∨
    FinDist.pure
        (next.includePending (runtime.reactiveApplication leaks) selected).application.config =
      next.application.config.step event ready action ∧
      (next.includePending (runtime.reactiveApplication leaks) selected).receipts =
        next.receipts ++ [((owner, execution.network.nextSerial owner), true)] := by
  rcases (runtime.reactiveApplication leaks).includePending_retained_or_selected next selected
      _ pending with retained | found
  · exact Or.inl retained
  · have same : (owner, execution.network.nextSerial owner) = selected := by
      simpa only [MessageNetwork.lookup, decide_eq_true_eq] using
        (List.find?_some found)
    subst selected
    exact Or.inr (runtime.reactiveDecision_binding_continuation_admitted leaks owner event payload
      outputEq codeEq node action serial execution next valid fixed allocated policy players
      prescribed scheduler rounds reached found ready timely)

end Vegas.EventGraphRuntime
