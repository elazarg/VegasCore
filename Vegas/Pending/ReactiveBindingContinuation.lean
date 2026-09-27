/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveBindingShadowStep
import Vegas.Pending.ReactiveCompiledMenu

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

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
  (bounds : MessageBounds graph)

open Classical in
def compiledImplementation (who : Player)
    (reference : List (runtime.reactiveApplication leaks).PlayerEntry)
    (policy : (runtime.reactiveApplication leaks).Policy) :
    (runtime.reactiveApplication leaks).Implementation (BindingMemory runtime leaks) where
  initial := FinDist.pure (atRecall runtime leaks reference)
  respond memory input :=
    ((implementation runtime leaks who reference policy).respond memory input).map fun result =>
      (if result.1 ∈ bounds.compiledActions runtime leaks who input.1 input.2 then result.1
       else (bounds.compiledActions_nonempty runtime leaks who input.1 input.2).choose, result.2)

/-- Before the first excluded response, restriction changes no implementation
transition, including its private memory update. -/
theorem compiledImplementation_respond_eq (who : Player)
    (reference : List (runtime.reactiveApplication leaks).PlayerEntry)
    (policy : (runtime.reactiveApplication leaks).Policy)
    (memory : BindingMemory runtime leaks)
    (input : List (runtime.reactiveApplication leaks).PlayerEntry ×
      (runtime.reactiveApplication leaks).PlayerView)
    (covered : ∀ result ∈ ((implementation runtime leaks who reference policy).respond
      memory input).support,
        result.1 ∈ bounds.compiledActions runtime leaks who input.1 input.2) :
    (compiledImplementation runtime leaks bounds who reference policy).respond memory input =
      (implementation runtime leaks who reference policy).respond memory input := by
  unfold compiledImplementation
  calc
    _ = ((implementation runtime leaks who reference policy).respond memory input).map id := by
      apply FinDist.map_congr_of_eq_on_support
      intro result supported
      simp only [covered result supported, ↓reduceIte, id_eq]
    _ = _ := FinDist.map_id _

/-- An unobservable unusable commitment under the canonical fresh handle is
repaired to an actual retained action, rather than sent to the fallback branch. -/
theorem repairResponse_compiled (who : Player) (memory : BindingMemory runtime leaks)
    (past : List (runtime.reactiveApplication leaks).PlayerEntry)
    (view : (runtime.reactiveApplication leaks).PlayerView)
    (event : graph.EventId) (payload : L.Ty)
    (outputEq : graph.outputLayout event = .binding who payload)
    (codeEq : cast (congrArg (EventGraph.EventCode graph.layout) outputEq)
      (graph.nodes event) = .bind who payload)
    (node : nodeView graph event = .bind who payload outputEq codeEq)
    (granted : view.application.publicView.serviceGrant = some event)
    (owned : graph.actor? event = some who)
    (ready : view.application.publicView.EventReady event)
    (serial : Nat) (fresh : reactiveFreshSlot view.application = some serial)
    (capacity : serial < bounds.candidateCount)
    (default : (⟨payload, L.someValue payload⟩ : Raw L) ∈ bounds.values)
    (opening : Option (Raw L))
    (originalFresh : (memory.shadow.inputView runtime leaks view).application.candidates
      (.prepared serial) = .fresh)
    (unusable : opening.bind (fun raw => raw.as? payload) = none) :
    (memory.repairResponse runtime leaks who view
      ⟨some (.submit ⟨⟨.commitment event (who, .prepared serial), opening⟩, .none⟩)⟩).1 ∈
      bounds.compiledActions runtime leaks who past view := by
  have actualFresh := reactiveFreshSlot_spec view.application serial fresh
  rw [memory.repairResponse_unusable runtime leaks who view event payload outputEq codeEq node
    serial opening originalFresh actualFresh unusable]
  have represented := bounds.binding_value_compiled runtime leaks who past view event payload
    outputEq codeEq node granted owned ready serial fresh capacity (L.someValue payload) default
  rw [runtime.serviceDecision_binding leaks who past view event payload outputEq codeEq node
    serial fresh, runtime.reactiveBinding_normal_of_fresh leaks who past view event payload _
      serial actualFresh] at represented
  exact represented

theorem compiledImplementation_response_available (who : Player)
    (reference : List (runtime.reactiveApplication leaks).PlayerEntry)
    (policy : (runtime.reactiveApplication leaks).Policy)
    (memory : BindingMemory runtime leaks)
    (input : List (runtime.reactiveApplication leaks).PlayerEntry ×
      (runtime.reactiveApplication leaks).PlayerView)
    (result : (runtime.reactiveApplication leaks).Action × BindingMemory runtime leaks)
    (supported : result ∈
      ((compiledImplementation runtime leaks bounds who reference policy).respond memory
        input).support) :
    result.1 ∈ bounds.compiledActions runtime leaks who input.1 input.2 := by
  obtain ⟨original, _, rfl⟩ := FinDist.support_map .. ▸ supported
  dsimp only
  split
  · assumption
  · exact (bounds.compiledActions_nonempty runtime leaks who input.1 input.2).choose_spec

theorem compiledImplementation_policy_available (who : Player)
    (reference : List (runtime.reactiveApplication leaks).PlayerEntry)
    (policy : (runtime.reactiveApplication leaks).Policy)
    (past : List (runtime.reactiveApplication leaks).PlayerEntry)
    (view : (runtime.reactiveApplication leaks).PlayerView)
    (response : (runtime.reactiveApplication leaks).Action)
    (supported : response ∈
      ((compiledImplementation runtime leaks bounds who reference policy).policy
        past view).support) :
    response ∈ bounds.compiledActions runtime leaks who past view := by
  rw [ReactiveApplication.Implementation.policy_eq, FinDist.support_map] at supported
  obtain ⟨result, member, rfl⟩ := supported
  obtain ⟨memory, _, member⟩ := Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ member)
  exact compiledImplementation_response_available runtime leaks bounds who reference policy
    memory (past, view) result member

theorem compiledImplementation_admissible
    (initial : FinDist (runtime.reactiveApplication leaks).State) (horizon : Nat)
    (scheduler : (runtime.reactiveApplication leaks).Scheduler) (who : Player)
    (reference : List (runtime.reactiveApplication leaks).PlayerEntry)
    (policy : (runtime.reactiveApplication leaks).Policy) :
    (bounds.compiledMenu runtime leaks).Admissible initial horizon scheduler who
      (compiledImplementation runtime leaks bounds who reference policy).policy := by
  intro control _ _ response supported
  exact compiledImplementation_policy_available runtime leaks bounds who reference policy
    _ _ response supported

def compiledPolicy (initial : FinDist (runtime.reactiveApplication leaks).State) (horizon : Nat)
    (scheduler : (runtime.reactiveApplication leaks).Scheduler) (who : Player)
    (reference : List (runtime.reactiveApplication leaks).PlayerEntry)
    (policy : (runtime.reactiveApplication leaks).Policy) :
    ((bounds.compiledMenu runtime leaks).information initial horizon scheduler).BehavioralPolicy
      who :=
  (bounds.compiledMenu runtime leaks).restrictPolicy initial horizon scheduler who
    (compiledImplementation runtime leaks bounds who reference policy).policy
    (compiledImplementation_admissible runtime leaks bounds initial horizon scheduler who
      reference policy)

theorem compiledPolicy_decode (initial : FinDist (runtime.reactiveApplication leaks).State)
    (horizon : Nat) (scheduler : (runtime.reactiveApplication leaks).Scheduler) (who : Player)
    (reference : List (runtime.reactiveApplication leaks).PlayerEntry)
    (policy : (runtime.reactiveApplication leaks).Policy) :
    (runtime.reactiveApplication leaks).decodePolicy
      ((bounds.compiledMenu runtime leaks).embedPolicy initial horizon scheduler who
        (compiledPolicy runtime leaks bounds initial horizon scheduler who reference policy)) =
      (compiledImplementation runtime leaks bounds who reference policy).policy := by
  apply (bounds.compiledMenu runtime leaks).decode_restrictPolicy_of_covered
  exact compiledImplementation_policy_available runtime leaks bounds who reference policy

private theorem compiledImplementation_response_prefix (who : Player)
    (reference past : List (runtime.reactiveApplication leaks).PlayerEntry)
    (policy : (runtime.reactiveApplication leaks).Policy)
    (view : (runtime.reactiveApplication leaks).PlayerView)
    (short : past.length < reference.length)
    (response : (runtime.reactiveApplication leaks).Action × BindingMemory runtime leaks)
    (supported : response ∈
      ((compiledImplementation runtime leaks bounds who reference policy).respond
        (atRecall runtime leaks reference) (past, view)).support) :
    response.2 = atRecall runtime leaks reference := by
  obtain ⟨original, member, rfl⟩ := FinDist.support_map .. ▸ supported
  simp only [implementation, short, ↓reduceIte, FinDist.support_map] at member
  obtain ⟨action, _, rfl⟩ := member
  rfl

theorem compiledImplementation_posterior_prefix (who : Player)
    (reference past : List (runtime.reactiveApplication leaks).PlayerEntry)
    (policy : (runtime.reactiveApplication leaks).Policy)
    (short : past.length ≤ reference.length) :
    (compiledImplementation runtime leaks bounds who reference policy).posterior past =
      FinDist.pure (atRecall runtime leaks reference) := by
  induction past using List.reverseRecOn with
  | nil => rfl
  | append_singleton past entry ih =>
      have earlier : past.length ≤ reference.length := by
        simp only [List.length_append, List.length_singleton] at short
        omega
      have shorter : past.length < reference.length := by
        simp only [List.length_append, List.length_singleton] at short
        omega
      rw [ReactiveApplication.Implementation.posterior_snoc, ih earlier, FinDist.pure_bind]
      apply FinDist.eq_pure_of_support_subset_singleton
      intro memory member
      obtain ⟨response, supported, rfl⟩ := FinDist.support_map .. ▸ member
      have original : response ∈
          ((compiledImplementation runtime leaks bounds who reference policy).respond
            (atRecall runtime leaks reference) (past, entry.beforeView)).support := by
        unfold FinDist.condOnFibre at supported
        split at supported
        · exact (FinDist.support_condOn _ _ _ supported).2
        · exact supported
      exact compiledImplementation_response_prefix runtime leaks bounds who reference past
        policy entry.beforeView shorter response original

/-- Behavioral realization uses one fixed private seed across the entire
starting information set, and every subsequent response belongs to C. -/
theorem compiledImplementation_continuation (who : Player)
    (reference : List (runtime.reactiveApplication leaks).PlayerEntry)
    (policy : (runtime.reactiveApplication leaks).Policy)
    (players : Player → (runtime.reactiveApplication leaks).Policy)
    (scheduler : (runtime.reactiveApplication leaks).Scheduler)
    (count : Nat) (execution : (runtime.reactiveApplication leaks).Execution)
    (recalled : execution.recall who = reference) :
    let strategy := compiledImplementation runtime leaks bounds who reference policy
    (strategy.resume who players (some who) execution (atRecall runtime leaks reference)).bind
        (fun result => strategy.run who players scheduler count result.1 result.2) =
      ((runtime.reactiveApplication leaks).resume
        (Function.update players who strategy.policy) (some who) execution).bind
          ((runtime.reactiveApplication leaks).runRounds scheduler
            (Function.update players who strategy.policy) count) := by
  let strategy := compiledImplementation runtime leaks bounds who reference policy
  have realized := strategy.realize_continuation who players scheduler count (some who) execution
  rw [recalled, compiledImplementation_posterior_prefix runtime leaks bounds who reference
    reference policy (Nat.le_refl _), FinDist.pure_bind] at realized
  exact realized

end Vegas.EventGraphRuntime.BindingMemory
