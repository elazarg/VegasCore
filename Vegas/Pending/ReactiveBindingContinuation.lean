/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveBindingShadowStep
import Vegas.Pending.ReactiveCompiledMenu
import GameTheory.Math.Probability.ConditionalObservation
import GameTheory.Math.Probability.ExpectationConditioning
import GameTheoryExtensions.Math.Probability.Support

/-! # A legal retained continuation from private binding repair

The repaired implementation is made legal at every input by choosing a fixed
retained response whenever its proposed response is unavailable. Before that
case, it is exactly the owner-local shadow implementation. Its behavioral
realization is one legal continuation for all hidden histories sharing the
starting own recall. The payoff comparison still requires the stopped-run
coupling and collection proof; availability is not a deterrence premise.
-/

noncomputable section

namespace Vegas.EventGraphRuntime.BindingMemory

open Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
  (menu : (runtime.reactiveApplication leaks).ResponseMenu)

open Classical in
def retainedImplementation (who : Player)
    (reference : List (runtime.reactiveApplication leaks).PlayerEntry)
    (policy : (runtime.reactiveApplication leaks).Policy) :
    (runtime.reactiveApplication leaks).Implementation (BindingMemory runtime leaks) where
  initial := PMF.pure (atRecall runtime leaks reference)
  respond memory input :=
    ((implementation runtime leaks who reference policy).respond memory input).map fun result =>
      (if result.1 ∈ menu.actions who input.1 input.2 then result.1
       else (menu.nonempty who input.1 input.2).choose, result.2)

/-- Before the first excluded response, restriction changes no implementation
transition, including its private memory update. -/
theorem retainedImplementation_respond_eq (who : Player)
    (reference : List (runtime.reactiveApplication leaks).PlayerEntry)
    (policy : (runtime.reactiveApplication leaks).Policy)
    (memory : BindingMemory runtime leaks)
    (input : List (runtime.reactiveApplication leaks).PlayerEntry ×
      (runtime.reactiveApplication leaks).PlayerView)
    (covered : ∀ result ∈ ((implementation runtime leaks who reference policy).respond
      memory input).support,
        result.1 ∈ menu.actions who input.1 input.2) :
    (retainedImplementation runtime leaks menu who reference policy).respond memory input =
      (implementation runtime leaks who reference policy).respond memory input := by
  unfold retainedImplementation
  calc
    _ = ((implementation runtime leaks who reference policy).respond memory input).map id := by
      apply map_congr_on_support _
      intro result supported
      simp only [covered result supported, ↓reduceIte, id_eq]
    _ = _ := PMF.map_id _

theorem retainedImplementation_response_available (who : Player)
    (reference : List (runtime.reactiveApplication leaks).PlayerEntry)
    (policy : (runtime.reactiveApplication leaks).Policy)
    (memory : BindingMemory runtime leaks)
    (input : List (runtime.reactiveApplication leaks).PlayerEntry ×
      (runtime.reactiveApplication leaks).PlayerView)
    (result : (runtime.reactiveApplication leaks).Action × BindingMemory runtime leaks)
    (supported : result ∈
      ((retainedImplementation runtime leaks menu who reference policy).respond memory
        input).support) :
    result.1 ∈ menu.actions who input.1 input.2 := by
  obtain ⟨original, _, rfl⟩ := PMF.support_map .. ▸ supported
  dsimp only
  split
  · assumption
  · exact (menu.nonempty who input.1 input.2).choose_spec

theorem retainedImplementation_policy_available (who : Player)
    (reference : List (runtime.reactiveApplication leaks).PlayerEntry)
    (policy : (runtime.reactiveApplication leaks).Policy)
    (past : List (runtime.reactiveApplication leaks).PlayerEntry)
    (view : (runtime.reactiveApplication leaks).PlayerView)
    (response : (runtime.reactiveApplication leaks).Action)
    (supported : response ∈
      ((retainedImplementation runtime leaks menu who reference policy).policy
        past view).support) :
    response ∈ menu.actions who past view := by
  rw [ReactiveApplication.Implementation.policy_eq, PMF.support_map] at supported
  obtain ⟨result, member, rfl⟩ := supported
  obtain ⟨memory, _, member⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ member)
  exact retainedImplementation_response_available runtime leaks menu who reference policy
    memory (past, view) result member

theorem retainedImplementation_admissible
    (initial : PMF (runtime.reactiveApplication leaks).State) (horizon : Nat)
    (scheduler : (runtime.reactiveApplication leaks).Scheduler) (who : Player)
    (reference : List (runtime.reactiveApplication leaks).PlayerEntry)
    (policy : (runtime.reactiveApplication leaks).Policy) :
    menu.Admissible initial horizon scheduler who
      (retainedImplementation runtime leaks menu who reference policy).policy := by
  intro control _ _ response supported
  exact retainedImplementation_policy_available runtime leaks menu who reference policy
    _ _ response supported

def retainedPolicy [Fintype Player]
    (initial : PMF (runtime.reactiveApplication leaks).State) (horizon : Nat)
    (scheduler : (runtime.reactiveApplication leaks).Scheduler) (who : Player)
    (reference : List (runtime.reactiveApplication leaks).PlayerEntry)
    (policy : (runtime.reactiveApplication leaks).Policy) :
    (menu.information initial horizon scheduler).BehavioralPolicy
      who :=
  menu.restrictPolicy initial horizon scheduler who
    (retainedImplementation runtime leaks menu who reference policy).policy

theorem retainedPolicy_decode [Fintype Player]
    (initial : PMF (runtime.reactiveApplication leaks).State)
    (horizon : Nat) (scheduler : (runtime.reactiveApplication leaks).Scheduler) (who : Player)
    (reference : List (runtime.reactiveApplication leaks).PlayerEntry)
    (policy : (runtime.reactiveApplication leaks).Policy) :
    (runtime.reactiveApplication leaks).decodePolicy
      (menu.embedPolicy initial horizon scheduler who
        (retainedPolicy runtime leaks menu initial horizon scheduler who reference policy)) =
      (retainedImplementation runtime leaks menu who reference policy).policy := by
  apply menu.decode_restrictPolicy_of_covered
  exact retainedImplementation_policy_available runtime leaks menu who reference policy

private theorem retainedImplementation_response_prefix (who : Player)
    (reference past : List (runtime.reactiveApplication leaks).PlayerEntry)
    (policy : (runtime.reactiveApplication leaks).Policy)
    (view : (runtime.reactiveApplication leaks).PlayerView)
    (short : past.length < reference.length)
    (response : (runtime.reactiveApplication leaks).Action × BindingMemory runtime leaks)
    (supported : response ∈
      ((retainedImplementation runtime leaks menu who reference policy).respond
        (atRecall runtime leaks reference) (past, view)).support) :
    response.2 = atRecall runtime leaks reference := by
  obtain ⟨original, member, rfl⟩ := PMF.support_map .. ▸ supported
  simp only [implementation, short, ↓reduceIte, PMF.support_map] at member
  obtain ⟨action, _, rfl⟩ := member
  rfl

theorem retainedImplementation_posterior_prefix (who : Player)
    (reference past : List (runtime.reactiveApplication leaks).PlayerEntry)
    (policy : (runtime.reactiveApplication leaks).Policy)
    (short : past.length ≤ reference.length) :
    (retainedImplementation runtime leaks menu who reference policy).posterior past =
      PMF.pure (atRecall runtime leaks reference) := by
  induction past using List.reverseRecOn with
  | nil => rfl
  | append_singleton past entry ih =>
      have earlier : past.length ≤ reference.length := by
        simp only [List.length_append, List.length_singleton] at short
        omega
      have shorter : past.length < reference.length := by
        simp only [List.length_append, List.length_singleton] at short
        omega
      rw [ReactiveApplication.Implementation.posterior_snoc, ih earlier, PMF.pure_bind]
      apply pmf_eq_pure_of_support_subset_singleton
      intro memory member
      obtain ⟨response, supported, rfl⟩ := PMF.support_map .. ▸ member
      have original : response ∈
          ((retainedImplementation runtime leaks menu who reference policy).respond
            (atRecall runtime leaks reference) (past, entry.beforeView)).support := by
        unfold fiberPosterior at supported
        split at supported
        · exact ((PMF.mem_support_filter_iff _).mp supported).2
        · exact supported
      exact retainedImplementation_response_prefix runtime leaks menu who reference past
        policy entry.beforeView shorter response original

/-- Behavioral realization uses one fixed private seed across the entire
starting information set, and every subsequent response belongs to C. -/
theorem retainedImplementation_continuation (who : Player)
    (reference : List (runtime.reactiveApplication leaks).PlayerEntry)
    (policy : (runtime.reactiveApplication leaks).Policy)
    (players : Player → (runtime.reactiveApplication leaks).Policy)
    (scheduler : (runtime.reactiveApplication leaks).Scheduler)
    (count : Nat) (execution : (runtime.reactiveApplication leaks).Execution)
    (recalled : execution.recall who = reference) :
    let strategy := retainedImplementation runtime leaks menu who reference policy
    (strategy.resume who players (some who) execution (atRecall runtime leaks reference)).bind
        (fun result => strategy.run who players scheduler count result.1 result.2) =
      ((runtime.reactiveApplication leaks).resume
        (Function.update players who strategy.policy) (some who) execution).bind
          ((runtime.reactiveApplication leaks).runRounds scheduler
            (Function.update players who strategy.policy) count) := by
  let strategy := retainedImplementation runtime leaks menu who reference policy
  have realized := strategy.realize_continuation who players scheduler count (some who) execution
  rw [recalled, retainedImplementation_posterior_prefix runtime leaks menu who reference
    reference policy (Nat.le_refl _), PMF.pure_bind] at realized
  exact realized

/-- An unobservable unusable commitment under the canonical fresh handle is
repaired to an actual retained action, rather than sent to the fallback branch. -/
theorem repairResponse_required [Fintype Player] (bounds : MessageBounds graph)
    (who : Player) (memory : BindingMemory runtime leaks)
    (past : List (runtime.reactiveApplication leaks).PlayerEntry)
    (view : (runtime.reactiveApplication leaks).PlayerView)
    (event : graph.EventId) (payload : L.Ty)
    (outputEq : graph.outputLayout event = .binding who payload)
    (codeEq : cast (congrArg (EventGraph.EventCode graph.layout) outputEq)
      (graph.nodes event) = .bind who payload)
    (node : nodeView graph event = .bind who payload outputEq codeEq)
    (turn : view.application.publicView.OwnTurn who event)
    (owned : graph.actor? event = some who)
    (ready : view.application.publicView.EventReady event)
    (unsent : runtime.eventRecorded leaks past event = false)
    (serial : Nat) (fresh : reactiveFreshSlot view.application = some serial)
    (capacity : serial < bounds.candidateCount)
    (default : (⟨payload, L.someValue payload⟩ : Raw L) ∈ bounds.values)
    (opening : Option (Raw L))
    (originalFresh : (memory.shadow.inputView runtime leaks view).application.candidates
      (.prepared serial) = .fresh)
    (unusable : opening.bind (fun raw => raw.as? payload) = none) :
    (memory.repairResponse runtime leaks who view
      ⟨some (.submit ⟨⟨.commitment event (who, .prepared serial), opening⟩, .none⟩)⟩).1 ∈
      bounds.requiredBindingActions runtime leaks who past view := by
  have turnSome := view.application.publicView.ownTurn?_of_ownTurn who event turn
  have actualFresh := reactiveFreshSlot_spec view.application serial fresh
  rw [memory.repairResponse_unusable runtime leaks who view event payload outputEq codeEq node
    serial opening originalFresh actualFresh unusable]
  have represented := bounds.binding_value_required runtime leaks who past view event payload
    outputEq codeEq node turn owned ready unsent serial fresh capacity
    (L.someValue payload) default
  rw [runtime.serviceDecision_binding leaks who past view event payload outputEq codeEq node
    serial fresh, runtime.reactiveBinding_normal_of_fresh leaks who past view event payload _
      serial actualFresh] at represented
  exact represented

end Vegas.EventGraphRuntime.BindingMemory
