/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactivePendingFrontierReadiness
/-! # Sampling coverage at actual prescribed responses -/

noncomputable section
namespace Vegas.EventGraphRuntime
open Interaction EventGraph GameTheory.Math.Probability
variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

/-- At a genuine ready own turn, an absent new intention means the compiler
has already recorded that event, rather than declining a fresh sample. -/
theorem prescribedReactiveResponse_none_blocked (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (who : Player) (policy : graph.BehavioralPolicy who)
    (history : List (runtime.reactiveApplication leaks).PlayerEntry)
    (intentions : List (Option graph.Completion))
    (view : (runtime.reactiveApplication leaks).PlayerView)
    (event : graph.EventId)
    (turn : view.application.publicView.ownTurn? who = some event)
    (owner : view.application.who = who)
    (ready : view.application.publicView.EventReady event)
    (actor : graph.actor? event = some who)
    (action : (runtime.reactiveApplication leaks).Action)
    (supported : (action, none) ∈
      (runtime.prescribedReactiveResponse leaks who policy history intentions view).support) :
    runtime.reactiveAlreadySubmitted leaks history event = true ∨
      runtime.reactiveAlreadyDecided leaks who history intentions event = true := by
  unfold prescribedReactiveResponse at supported
  simp only [turn] at supported
  split at supported
  · rename_i blocked
    exact Bool.or_eq_true_iff.mp blocked
  · try simp only [owner, ready, actor, ↓reduceDIte, ↓reduceIte] at supported
    rw [PMF.support_map] at supported
    obtain ⟨choice, _, equality⟩ := supported
    have impossible := congrArg Prod.snd equality
    cases impossible
/-- Every supported compiler response without a remembered intention is
physically silent; a transmitted call always retains its sampled decision. -/
theorem prescribedReactiveResponse_none_silent (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (who : Player) (policy : graph.BehavioralPolicy who)
    (history : List (runtime.reactiveApplication leaks).PlayerEntry)
    (intentions : List (Option graph.Completion))
    (view : (runtime.reactiveApplication leaks).PlayerView)
    (action : (runtime.reactiveApplication leaks).Action)
    (supported : (action, none) ∈
      (runtime.prescribedReactiveResponse leaks who policy history intentions view).support) :
    action.transmission = none := by
  unfold prescribedReactiveResponse at supported
  split at supported
  · have equal := (PMF.mem_support_pure_iff _ _).mp supported
    exact congrArg (fun pair => pair.1.transmission) equal
  · split at supported
    · have equal := (PMF.mem_support_pure_iff _ _).mp supported
      exact congrArg (fun pair => pair.1.transmission) equal
    · split at supported
      · split at supported
        · split at supported
          · rw [PMF.support_map] at supported
            obtain ⟨choice, _, equal⟩ := supported
            have impossible := congrArg Prod.snd equal
            cases impossible
          · have equal := (PMF.mem_support_pure_iff _ _).mp supported
            exact congrArg (fun pair => pair.1.transmission) equal
        · have equal := (PMF.mem_support_pure_iff _ _).mp supported
          exact congrArg (fun pair => pair.1.transmission) equal
      · have equal := (PMF.mem_support_pure_iff _ _).mp supported
        exact congrArg (fun pair => pair.1.transmission) equal

/-- The actual supported transmitting response addresses its remembered event,
which was genuinely ready and owned at the recorded input. -/
theorem prescribedReactiveResponse_transmitted_event (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (who : Player) (policy : graph.BehavioralPolicy who)
    (history : List (runtime.reactiveApplication leaks).PlayerEntry)
    (intentions : List (Option graph.Completion))
    (view : (runtime.reactiveApplication leaks).PlayerView)
    (action : (runtime.reactiveApplication leaks).Action) (remembered : graph.Completion)
    (supported : (action, some remembered) ∈
      (runtime.prescribedReactiveResponse leaks who policy history intentions view).support)
    (material : WitnessedSubmission graph) (transmitted : action.transmission = some material) :
    view.application.publicView.EventReady remembered.event ∧
      graph.actor? remembered.event = some who ∧
      material.call.packet.event? graph = some remembered.event := by
  have ready := runtime.prescribedReactiveResponse_some_ready leaks who policy history intentions
    view action remembered supported
  have matching := (runtime.prescribedReactiveResponse_some_fresh leaks who policy history
    intentions view action remembered supported).2.2
  have selected : (runtime.reactiveDecision leaks who remembered.event remembered.action
      view.application).transmission = some material :=
    (congrArg ReactiveApplication.Action.transmission matching).symm.trans transmitted
  refine ⟨ready.1, ready.2, ?_⟩
  rcases runtime.reactiveDecision_transmission leaks who remembered.event remembered.action
    view.application with absent | ⟨actual, actualSent, addressed⟩
  · rw [selected] at absent
    cases absent
  · have same : actual = material := Option.some.inj (actualSent.symm.trans selected)
    subst actual
    exact addressed

/-- Every actual emitted prescribed event packet has a retained sampled
intention in every supported posterior, including earlier transmissions. -/
theorem prescribedReactivePosterior_emitted_coverage (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (who : Player) (policy : graph.BehavioralPolicy who)
    {history : List (runtime.reactiveApplication leaks).PlayerEntry}
    (consistent : (runtime.prescribedReactivePolicy leaks who policy).Consistent history)
    (quiet : ∀ entry ∈ history, entry.action.transmission = none → entry.emitted = none)
    (sent : ∀ entry ∈ history, ∀ material, entry.action.transmission = some material →
      ∃ message, entry.emitted = some message ∧ message.payload.call = material.call.packet)
    (intentions : List (Option graph.Completion))
    (supported : intentions ∈
      ((runtime.prescribedReactiveImplementation leaks who policy).posterior history).support) :
    ∀ entry ∈ history, ∀ message, entry.emitted = some message →
      ∃ remembered, some remembered ∈ intentions ∧
        message.payload.call.event? graph = some remembered.event := by
  induction consistent generalizing intentions with
  | nil => simp
  | @snoc history latest consistent positive ih =>
      obtain ⟨previous, prior, saved, memoryEq, produced⟩ :=
        runtime.prescribedReactivePosterior_snoc_support leaks who policy history latest
          positive intentions supported
      intro entry member message emitted
      rw [memoryEq]
      rcases List.mem_append.mp member with earlier | last
      · obtain ⟨remembered, retained, named⟩ := ih
          (fun entry member => quiet entry (List.mem_append_left _ member))
          (fun entry member => sent entry (List.mem_append_left _ member))
          previous prior entry earlier message emitted
        exact ⟨remembered, List.mem_append_left _ retained, named⟩
      · have sameEntry : entry = latest := List.mem_singleton.mp last
        subst entry
        have latestMember : latest ∈ history ++ [latest] := by simp
        cases saved with
        | none =>
            have silent := runtime.prescribedReactiveResponse_none_silent leaks who policy history
              previous latest.beforeView latest.action produced
            have absent := quiet latest latestMember silent
            rw [emitted] at absent
            cases absent
        | some remembered =>
            have matching := (runtime.prescribedReactiveResponse_some_fresh leaks who policy history
              previous latest.beforeView latest.action remembered produced).2.2
            cases transmitted : latest.action.transmission with
            | none =>
                have absent := quiet latest latestMember transmitted
                rw [emitted] at absent
                cases absent
            | some material =>
                obtain ⟨actual, actualEmitted, packet⟩ :=
                  sent latest latestMember material transmitted
                have actualEq : actual = message :=
                  Option.some.inj (actualEmitted.symm.trans emitted)
                subst actual
                have decisionSent : (runtime.reactiveDecision leaks who remembered.event
                    remembered.action latest.beforeView.application).transmission = some material :=
                  (congrArg ReactiveApplication.Action.transmission matching).symm.trans transmitted
                refine ⟨remembered, List.mem_append_right _ (by simp), ?_⟩
                rw [packet]
                rcases runtime.reactiveDecision_transmission leaks who remembered.event
                  remembered.action latest.beforeView.application with absent |
                    ⟨selected, selectedSent, addressed⟩
                · rw [decisionSent] at absent
                  cases absent
                · have equal : selected = material := Option.some.inj
                    (selectedSent.symm.trans decisionSent)
                  subst selected
                  exact addressed

/-- A recorded event submission cannot suppress sampling without a genuine
retained intention in the supported private posterior. -/
theorem prescribedReactivePosterior_submitted_coverage (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (who : Player) (policy : graph.BehavioralPolicy who)
    {history : List (runtime.reactiveApplication leaks).PlayerEntry}
    (consistent : (runtime.prescribedReactivePolicy leaks who policy).Consistent history)
    (quiet : ∀ entry ∈ history, entry.action.transmission = none → entry.emitted = none)
    (sent : ∀ entry ∈ history, ∀ material, entry.action.transmission = some material →
      ∃ message, entry.emitted = some message ∧ message.payload.call = material.call.packet)
    (intentions : List (Option graph.Completion))
    (supported : intentions ∈
      ((runtime.prescribedReactiveImplementation leaks who policy).posterior history).support)
    (event : graph.EventId)
    (submitted : runtime.reactiveAlreadySubmitted leaks history event = true) :
    ∃ remembered, some remembered ∈ intentions ∧ remembered.event = event := by
  have recorded := (runtime.reactiveAlreadySubmitted_iff leaks history event).mp submitted
  obtain ⟨entry, member, addressed⟩ := List.mem_filterMap.mp recorded
  cases emitted : entry.emitted with
  | none => simp [emitted] at addressed
  | some message =>
      have named : message.payload.call.event? graph = some event := by
        simpa only [emitted, Option.bind_some] using addressed
      obtain ⟨remembered, retained, intentionNamed⟩ :=
        runtime.prescribedReactivePosterior_emitted_coverage leaks who policy consistent quiet sent
          intentions supported entry member message emitted
      exact ⟨remembered, retained, Option.some.inj (intentionNamed.symm.trans named)⟩

/-- A remembered silent decision has an actual retained event intention. -/
theorem reactiveAlreadyDecided_memory (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (who : Player) (history : List (runtime.reactiveApplication leaks).PlayerEntry)
    (intentions : List (Option graph.Completion)) (event : graph.EventId)
    (decided : runtime.reactiveAlreadyDecided leaks who history intentions event = true) :
    ∃ remembered, some remembered ∈ intentions ∧ remembered.event = event := by
  classical
  unfold reactiveAlreadyDecided at decided
  obtain ⟨entry, remembered, retained, named, _⟩ := of_decide_eq_true decided
  exact ⟨remembered, (List.of_mem_zip retained).2, named⟩

/-- A freshly remembered intention at a ready own turn names that actual turn. -/
theorem prescribedReactiveResponse_some_event (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (who : Player) (policy : graph.BehavioralPolicy who)
    (history : List (runtime.reactiveApplication leaks).PlayerEntry)
    (intentions : List (Option graph.Completion))
    (view : (runtime.reactiveApplication leaks).PlayerView)
    (event : graph.EventId)
    (turn : view.application.publicView.ownTurn? who = some event)
    (owner : view.application.who = who)
    (ready : view.application.publicView.EventReady event)
    (actor : graph.actor? event = some who)
    (action : (runtime.reactiveApplication leaks).Action) (remembered : graph.Completion)
    (supported : (action, some remembered) ∈
      (runtime.prescribedReactiveResponse leaks who policy history intentions view).support) :
    remembered.event = event := by
  simp only [prescribedReactiveResponse, turn, owner, ready, actor, ↓reduceDIte, ↓reduceIte]
    at supported
  split at supported
  · simp at supported
  · rw [PMF.support_map] at supported
    obtain ⟨choice, _, equal⟩ := supported
    have rememberedEq := Option.some.inj (congrArg Prod.snd equal)
    exact (congrArg Completion.event rememberedEq).symm

/-- Every supported posterior after an actual ready owned response retains its
event's original sampled decision, whether this callback sampled or reused it. -/
theorem prescribedReactivePosterior_ready_response_coverage (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (who : Player) (policy : graph.BehavioralPolicy who)
    (history : List (runtime.reactiveApplication leaks).PlayerEntry)
    (entry : (runtime.reactiveApplication leaks).PlayerEntry)
    (consistent : (runtime.prescribedReactivePolicy leaks who policy).Consistent history)
    (positive : entry.action ∈
      (runtime.prescribedReactivePolicy leaks who policy history entry.beforeView).support)
    (quiet : ∀ record ∈ history, record.action.transmission = none → record.emitted = none)
    (sent : ∀ record ∈ history, ∀ material, record.action.transmission = some material →
      ∃ message, record.emitted = some message ∧ message.payload.call = material.call.packet)
    (event : graph.EventId)
    (turn : entry.beforeView.application.publicView.ownTurn? who = some event)
    (owner : entry.beforeView.application.who = who)
    (ready : entry.beforeView.application.publicView.EventReady event)
    (actor : graph.actor? event = some who)
    (intentions : List (Option graph.Completion))
    (supported : intentions ∈
      ((runtime.prescribedReactiveImplementation leaks who policy).posterior
        (history ++ [entry])).support) :
    ∃ remembered, some remembered ∈ intentions ∧ remembered.event = event := by
  obtain ⟨previous, prior, saved, memoryEq, produced⟩ :=
    runtime.prescribedReactivePosterior_snoc_support leaks who policy history entry positive
      intentions supported
  rw [memoryEq]
  cases saved with
  | none =>
      have blocked := runtime.prescribedReactiveResponse_none_blocked leaks who policy history
        previous entry.beforeView event turn owner ready actor entry.action produced
      rcases blocked with submitted | decided
      · obtain ⟨remembered, retained, named⟩ :=
          runtime.prescribedReactivePosterior_submitted_coverage leaks who policy consistent quiet
            sent previous prior event submitted
        exact ⟨remembered, List.mem_append_left _ retained, named⟩
      · obtain ⟨remembered, retained, named⟩ :=
          runtime.reactiveAlreadyDecided_memory leaks who history previous event decided
        exact ⟨remembered, List.mem_append_left _ retained, named⟩
  | some remembered =>
      exact ⟨remembered, List.mem_append_right _ (by simp),
        runtime.prescribedReactiveResponse_some_event leaks who policy history previous
          entry.beforeView event turn owner ready actor entry.action remembered produced⟩

/-- Positive-history extensions cannot erase the original event sampled at a
ready own response from the supported private memory. -/
theorem prescribedReactivePosterior_coverage_extension (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (who : Player) (policy : graph.BehavioralPolicy who)
    (history later : List (runtime.reactiveApplication leaks).PlayerEntry)
    (event : graph.EventId)
    (consistent : (runtime.prescribedReactivePolicy leaks who policy).Consistent (history ++ later))
    (covered : ∀ intentions ∈
      ((runtime.prescribedReactiveImplementation leaks who policy).posterior history).support,
      ∃ remembered, some remembered ∈ intentions ∧ remembered.event = event)
    (intentions : List (Option graph.Completion))
    (supported : intentions ∈
      ((runtime.prescribedReactiveImplementation leaks who policy).posterior
        (history ++ later)).support) :
    ∃ remembered, some remembered ∈ intentions ∧ remembered.event = event := by
  induction later using List.reverseRecOn generalizing intentions with
  | nil =>
      exact covered intentions (by simpa only [List.append_nil] using supported)
  | append_singleton later entry ih =>
      have stepConsistent : (runtime.prescribedReactivePolicy leaks who policy).Consistent
          ((history ++ later) ++ [entry]) := by
        simpa only [List.append_assoc] using consistent
      have step := (ReactiveApplication.Policy.consistent_snoc_iff _ _ _).mp stepConsistent
      have stepSupported : intentions ∈
          ((runtime.prescribedReactiveImplementation leaks who policy).posterior
            ((history ++ later) ++ [entry])).support := by
        simpa only [List.append_assoc] using supported
      obtain ⟨previous, prior, saved, memoryEq, _⟩ :=
        runtime.prescribedReactivePosterior_snoc_support leaks who policy (history ++ later) entry
          step.2 intentions stepSupported
      obtain ⟨remembered, retained, named⟩ := ih step.1 previous prior
      exact ⟨remembered, memoryEq ▸ List.mem_append_left _ retained, named⟩

/-- A retained genuine ready own response witnesses the sampled event in every
supported current posterior, regardless of later responses or conditioning. -/
theorem prescribedReactivePosterior_recorded_ready_coverage (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (who : Player) (policy : graph.BehavioralPolicy who)
    (history : List (runtime.reactiveApplication leaks).PlayerEntry)
    (consistent : (runtime.prescribedReactivePolicy leaks who policy).Consistent history)
    (quiet : ∀ record ∈ history, record.action.transmission = none → record.emitted = none)
    (sent : ∀ record ∈ history, ∀ material, record.action.transmission = some material →
      ∃ message, record.emitted = some message ∧ message.payload.call = material.call.packet)
    (entry : (runtime.reactiveApplication leaks).PlayerEntry) (retained : entry ∈ history)
    (event : graph.EventId)
    (turn : entry.beforeView.application.publicView.ownTurn? who = some event)
    (owner : entry.beforeView.application.who = who)
    (ready : entry.beforeView.application.publicView.EventReady event)
    (actor : graph.actor? event = some who)
    (intentions : List (Option graph.Completion))
    (supported : intentions ∈
      ((runtime.prescribedReactiveImplementation leaks who policy).posterior history).support) :
    ∃ remembered, some remembered ∈ intentions ∧ remembered.event = event := by
  obtain ⟨before, after, split⟩ := List.mem_iff_append.mp retained
  have split' : history = (before ++ [entry]) ++ after := by
    simpa only [List.append_assoc, List.singleton_append] using split
  rw [split'] at consistent supported
  have prefixConsistent := consistent.of_append
  have step := (ReactiveApplication.Policy.consistent_snoc_iff _ _ _).mp prefixConsistent
  apply runtime.prescribedReactivePosterior_coverage_extension leaks who policy
    (before ++ [entry]) after event consistent _ intentions supported
  intro previous prior
  apply runtime.prescribedReactivePosterior_ready_response_coverage leaks who policy before entry
    step.1 step.2 _ _ event turn owner ready actor previous prior
  · intro record member
    apply quiet record
    rw [split']
    exact List.mem_append_left _ (List.mem_append_left _ member)
  · intro record member
    apply sent record
    rw [split']
    exact List.mem_append_left _ (List.mem_append_left _ member)

end Vegas.EventGraphRuntime
