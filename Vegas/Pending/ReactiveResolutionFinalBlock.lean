/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveResolutionAuditStep
import Vegas.Pending.ReactiveDecisionFinalMiss

/-! # The final required resolution response

An accepted canonical TRUE or FALSE response preserves the repair frame.
Silence at the last owner visit instead has a proved actual missed-decision
marker after the remaining foreign visits and due expiry. The fixed repaired
response law is shared across all hidden responses.
-/

noncomputable section

namespace Vegas.EventGraphRuntime.BindingMemory.Frame

open Interaction EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  {runtime : EventGraphRuntime graph}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph)}
  {memory : BindingMemory runtime leaks} {owner : Player}
  {original repaired : (runtime.reactiveApplication leaks).Execution}

private theorem required_of_compiled
    (bounds : MessageBounds graph) (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (who : Player) (past : List (runtime.reactiveApplication leaks).PlayerEntry)
    (view : (runtime.reactiveApplication leaks).PlayerView)
    (response : (runtime.reactiveApplication leaks).Action)
    (member : response ∈ bounds.compiledActions runtime leaks who past view)
    (nonSilent : response ≠ ⟨none⟩) :
    response ∈ bounds.requiredDecisionActions runtime leaks who past view := by
  classical
  obtain ⟨admitted, available⟩ := Finset.mem_inter.mp member
  rcases Finset.mem_union.mp admitted with decision | silent
  · obtain ⟨chosen, first⟩ := Finset.mem_filter.mp decision
    exact bounds.decision_required runtime leaks who past view response chosen first available
  · exact (nonSilent (Finset.mem_singleton.mp silent)).elim

theorem required_resolution_stopped_response_coupling
    (frame : Frame runtime leaks memory owner original repaired)
    (bounds : MessageBounds graph)
    (menu : (runtime.reactiveApplication leaks).ResponseMenu)
    (players : Player → (runtime.reactiveApplication leaks).Policy)
    (reference : List (runtime.reactiveApplication leaks).PlayerEntry)
    (started : reference.length ≤ (repaired.recall owner).length)
    (leftRecall : original.InputRecall (runtime.reactiveApplication leaks))
    (rightRecall : repaired.InputRecall (runtime.reactiveApplication leaks))
    (sound : (runtime.packetEvidence leaks).Sound original)
    (leftBinding : original.application.BindingInvariant)
    (rightBinding : repaired.application.BindingInvariant)
    (remaining : Nat) (event : graph.EventId) (payload : L.Ty)
    (binding : FieldRef graph.layout (.binding owner payload))
    (checks : List (GuardCheck graph.layout payload))
    (outputEq : graph.outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .resolve owner payload binding checks)
    (node : nodeView graph event = .resolve owner payload binding checks outputEq codeEq)
    (turn : original.application.publicView.OwnTurn owner event)
    (ready : original.application.config.cut.Ready event)
    (timely : original.application.WithinDeadline runtime event)
    (first : original.network.nextSerial owner =
      Message.distinctAuthoredCount original.network.ledger owner →
        runtime.eventRecorded leaks (original.recall owner) event = false)
    (serials : original.network.SerialsBeforeNext)
    (published : original.network.Satisfies fun message => message.sender = owner →
      message.id ∈ original.network.ledger.map Message.id)
    (entered ticks : Nat)
    (activated : original.application.activatedAt event = some entered)
    (due : runtime.deadline event ≤ original.application.clock + ticks - entered)
    (visits : List Player) (absent : owner ∉ visits)
    (coverage : bounds.requiredDecisionActions runtime leaks owner (repaired.recall owner)
      (repaired.observe (runtime.reactiveApplication leaks) owner) ⊆
        menu.actions owner (repaired.recall owner)
          (repaired.observe (runtime.reactiveApplication leaks) owner))
    (available : ∀ response ∈ (players owner (original.recall owner)
      (original.observe (runtime.reactiveApplication leaks) owner)).support,
        response ∈ (bounds.menu runtime leaks).actions owner (original.recall owner)
          (original.observe (runtime.reactiveApplication leaks) owner)) :
    let app := runtime.reactiveApplication leaks
    let strategy := retainedImplementation runtime leaks menu owner reference (players owner)
    ∃ coupling : PMF (app.Execution × app.Execution × BindingMemory runtime leaks),
      coupling.map Prod.fst = app.invoke players owner original ∧
      coupling.map Prod.snd = strategy.resume owner players (some owner) repaired memory ∧
      ∀ next ∈ coupling.support,
        (∃ record, app.trafficStep (some ⟨remaining, some owner, original⟩)
            (some ⟨remaining, none, next.1⟩) = [record] ∧
          record.envelope.sender = owner ∧
          runtime.permittedServiceEnvelope record.observation record.ledger
            record.envelope = false) ∨
        (∀ (later : Player → app.Policy) (network : runtime.NetworkPolicy leaks)
          (final : app.Execution), final ∈ (runtime.runInteractionPlan leaks later network
            (visits.map ServiceInstruction.player ++
              (.includeLatest event owner :: List.replicate ticks .tick ++ [.expire event]))
                next.1).support → event ∈ final.application.missedEvents) ∨
        (Frame runtime leaks next.2.2 owner next.1 next.2.1 ∧
          reference.length ≤ (next.2.1.recall owner).length ∧
          next.2.2.shadow = memory.shadow) := by
  classical
  have turnSome := original.application.publicView.ownTurn?_of_ownTurn owner event turn
  let app := runtime.reactiveApplication leaks
  let law := players owner (original.recall owner) (original.observe app owner)
  let proposed (response : app.Action) :=
    let changed := memory.repairResponse runtime leaks owner (repaired.observe app owner) response
    (changed.1, (⟨changed.2, memory.responses ++
      [(memory.shadow.inputView runtime leaks (repaired.observe app owner), response)]⟩ :
        BindingMemory runtime leaks))
  let adjusted (response : app.Action) :=
    let changed := retainedResponse runtime leaks menu owner memory
      (repaired.recall owner, repaired.observe app owner) response
    (changed.1, (⟨changed.2, memory.responses ++
      [(memory.shadow.inputView runtime leaks (repaired.observe app owner), response)]⟩ :
        BindingMemory runtime leaks))
  let coupling := law.map fun response =>
    (original.respond app owner response, repaired.respond app owner (adjusted response).1,
      (adjusted response).2)
  have responseLaw :
      (retainedImplementation runtime leaks menu owner reference (players owner)).respond memory
        (repaired.recall owner, repaired.observe app owner) = law.map adjusted := by
    rw [retainedImplementation_respond runtime leaks menu owner reference (players owner) memory
      (repaired.recall owner) (repaired.observe app owner) started, frame.past, frame.observed]
    simp only [law, adjusted]
    rw [show memory.shadow.inputView runtime leaks (repaired.observe app owner) =
      original.observe app owner from frame.observed]
  have adjustedEq (response : app.Action)
      (legal : (proposed response).1 ∈ menu.actions owner (repaired.recall owner)
        (repaired.observe app owner))
      (copyEq : response ∈ menu.actions owner (repaired.recall owner)
          (repaired.observe app owner) →
        memory.copyResponse runtime leaks owner (repaired.observe app owner) response =
          memory.repairResponse runtime leaks owner (repaired.observe app owner) response) :
      adjusted response = proposed response := by
    dsimp only [adjusted, proposed]
    rw [retainedResponse_eq_repairResponse runtime leaks menu owner memory
      (repaired.recall owner, repaired.observe app owner) response legal copyEq]
  have owned : graph.actor? event = some owner := by
    have actor := congrArg EventCode.actor codeEq
    rw [EventCode.actor_cast outputEq (graph.nodes event)] at actor
    exact actor
  refine ⟨coupling, ?_, ?_, ?_⟩
  · simp only [coupling, PMF.map_comp]
    rfl
  · simp only [coupling, PMF.map_comp, ReactiveApplication.Implementation.resume, ↓reduceIte]
    change law.map _ =
      ((retainedImplementation runtime leaks menu owner reference (players owner)).respond memory
        (repaired.recall owner, repaired.observe app owner)).map _
    rw [responseLaw, PMF.map_comp]
    rfl
  · intro next supported
    obtain ⟨response, selected, rfl⟩ := PMF.support_map .. ▸ supported
    rcases runtime.resolution_audit_response_cases leaks bounds original owner remaining sound
        leftBinding leftRecall serials event payload binding checks outputEq codeEq node turn
          first response (available response selected) with replay | withheld | canonical |
          departure
    · right
      left
      intro later network final reached
      apply runtime.last_decision_transport_miss leaks later network original owner event owned
        ready published entered ticks activated due visits absent response _ final reached
      intro material
      rcases app.silentPolicy_cases _ _ response replay with rfl
      simp
    · obtain ⟨same, firstResponse⟩ := withheld
      have actual : response = ⟨some ⟨⟨.withhold event, none⟩, .none⟩⟩ :=
        same.trans (runtime.serviceDecision_resolution_false leaks owner (original.recall owner)
          (original.observe app owner) event owner payload binding checks outputEq codeEq node)
      have unchanged : memory.repairResponse runtime leaks owner
          (repaired.observe app owner) response = (response, memory.shadow) := by
        rw [actual]
        rfl
      have legal : (proposed response).1 ∈ menu.actions owner (repaired.recall owner)
          (repaired.observe app owner) := by
        apply coverage
        dsimp only [proposed]
        rw [unchanged, actual]
        apply required_of_compiled bounds runtime leaks owner _ _ _
        · apply frame.withholding_response_retained bounds event payload binding checks outputEq
            codeEq node turn owned
          rwa [actual] at firstResponse
        · intro sameSilence
          cases sameSilence
      right
      right
      dsimp only
      rw [adjustedEq response legal (by
        intro _
        rw [actual]
        rfl)]
      dsimp only [proposed]
      rw [unchanged]
      refine ⟨?_, ?_, rfl⟩
      · rw [actual]
        exact frame.withholding_response_frame event
      · rw [app.respond_recall_length]
        omega
    · obtain ⟨value, stored, resolved, same, firstResponse⟩ := canonical
      have unchanged : memory.repairResponse runtime leaks owner
          (repaired.observe app owner) response = (response, memory.shadow) := by
        obtain ⟨_, candidate, associated, _, candidateOwned, fixed, _⟩ :=
          frame.successful_opening leftBinding rightBinding binding value stored
        have actual := runtime.serviceDecision_successful_opening leaks original leftRecall owner
          event payload binding checks outputEq codeEq node candidate value associated
            candidateOwned fixed resolved
        rw [same, actual]
        simp only [repairResponse, disclosureSubmission, WitnessedSubmission.normalizeReactive,
          Submission.normalizeReactive_none]
      have legal : (proposed response).1 ∈ menu.actions owner (repaired.recall owner)
          (repaired.observe app owner) := by
        apply coverage
        dsimp only [proposed]
        rw [unchanged]
        apply required_of_compiled bounds runtime leaks owner _ _ _
        · exact frame.successful_serviceDecision_retained bounds leftRecall rightRecall leftBinding
            rightBinding event payload binding checks outputEq codeEq node turn owned ready timely
              value stored resolved response same (available response selected) firstResponse
        · obtain ⟨_, candidate, associated, _, candidateOwned, fixed, _⟩ :=
            frame.successful_opening leftBinding rightBinding binding value stored
          have actual := runtime.serviceDecision_successful_opening leaks original leftRecall owner
            event payload binding checks outputEq codeEq node candidate value associated
              candidateOwned fixed resolved
          rw [same, actual]
          intro sameSilence
          cases sameSilence
      right
      right
      dsimp only
      rw [adjustedEq response legal (by
        intro _
        obtain ⟨_, candidate, associated, _, candidateOwned, fixed, _⟩ :=
          frame.successful_opening leftBinding rightBinding binding value stored
        have actual := runtime.serviceDecision_successful_opening leaks original leftRecall owner
          event payload binding checks outputEq codeEq node candidate value associated
            candidateOwned fixed resolved
        rw [same, actual]
        simp only [copyResponse, repairResponse, disclosureSubmission,
          WitnessedSubmission.normalizeReactive, Submission.normalizeReactive_none])]
      dsimp only [proposed]
      rw [unchanged]
      refine ⟨?_, ?_, rfl⟩
      · rw [same]
        exact frame.successful_response_frame leftRecall leftBinding rightBinding event payload
          binding checks outputEq codeEq node value stored resolved
      · rw [app.respond_recall_length]
        omega
    · exact Or.inl departure

theorem required_resolution_stopped_activation_coupling
    (frame : Frame runtime leaks memory owner original repaired)
    (bounds : MessageBounds graph)
    (menu : (runtime.reactiveApplication leaks).ResponseMenu)
    (players : Player → (runtime.reactiveApplication leaks).Policy)
    (reference : List (runtime.reactiveApplication leaks).PlayerEntry)
    (started : reference.length ≤ (repaired.recall owner).length)
    (leftRecall : original.InputRecall (runtime.reactiveApplication leaks))
    (rightRecall : repaired.InputRecall (runtime.reactiveApplication leaks))
    (sound : (runtime.packetEvidence leaks).Sound original)
    (leftBinding : original.application.BindingInvariant)
    (rightBinding : repaired.application.BindingInvariant)
    (remaining : Nat) (event : graph.EventId) (payload : L.Ty)
    (binding : FieldRef graph.layout (.binding owner payload))
    (checks : List (GuardCheck graph.layout payload))
    (outputEq : graph.outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .resolve owner payload binding checks)
    (node : nodeView graph event = .resolve owner payload binding checks outputEq codeEq)
    (turn : original.application.publicView.OwnTurn owner event)
    (ready : original.application.config.cut.Ready event)
    (timely : original.application.WithinDeadline runtime event)
    (first : original.network.nextSerial owner =
      Message.distinctAuthoredCount original.network.ledger owner →
        runtime.eventRecorded leaks (original.recall owner) event = false)
    (serials : original.network.SerialsBeforeNext)
    (published : original.network.Satisfies fun message => message.sender = owner →
      message.id ∈ original.network.ledger.map Message.id)
    (entered ticks : Nat)
    (activated : original.application.activatedAt event = some entered)
    (due : runtime.deadline event ≤ original.application.clock + ticks - entered)
    (visits : List Player) (absent : owner ∉ visits)
    (coverage : ∀ selected ∈ (leaks owner original.network.pending).support,
      let activated := repaired.sampledActivation (runtime.reactiveApplication leaks)
        owner selected
      bounds.requiredDecisionActions runtime leaks owner (activated.recall owner)
        (activated.observe (runtime.reactiveApplication leaks) owner) ⊆
          menu.actions owner (activated.recall owner)
            (activated.observe (runtime.reactiveApplication leaks) owner))
    (available : ∀ selected ∈ (leaks owner original.network.pending).support,
      let activated := original.sampledActivation (runtime.reactiveApplication leaks)
        owner selected
      ∀ response ∈ (players owner (activated.recall owner)
        (activated.observe (runtime.reactiveApplication leaks) owner)).support,
          response ∈ (bounds.menu runtime leaks).actions owner (activated.recall owner)
            (activated.observe (runtime.reactiveApplication leaks) owner)) :
    let app := runtime.reactiveApplication leaks
    let strategy := retainedImplementation runtime leaks menu owner reference (players owner)
    ∃ coupling : PMF (app.Execution × app.Execution × BindingMemory runtime leaks),
      coupling.map Prod.fst = app.dispatch players (.activate owner) original ∧
      coupling.map Prod.snd = (repaired.environmentStep app (.activate owner)).bind
        (fun execution => strategy.resume owner players (some owner) execution memory) ∧
      ∀ next ∈ coupling.support,
        (∃ record, app.trafficStep (some ⟨remaining + 1, none, original⟩)
            (some ⟨remaining, none, next.1⟩) = [record] ∧
          record.envelope.sender = owner ∧
          runtime.permittedServiceEnvelope record.observation record.ledger
            record.envelope = false) ∨
        (∀ (later : Player → app.Policy) (network : runtime.NetworkPolicy leaks)
          (final : app.Execution), final ∈ (runtime.runInteractionPlan leaks later network
            (visits.map ServiceInstruction.player ++
              (.includeLatest event owner :: List.replicate ticks .tick ++ [.expire event]))
                next.1).support → event ∈ final.application.missedEvents) ∨
        (Frame runtime leaks next.2.2 owner next.1 next.2.1 ∧
          reference.length ≤ (next.2.1.recall owner).length ∧
          next.2.2.shadow = memory.shadow) := by
  classical
  have turnSome := original.application.publicView.ownTurn?_of_ownTurn owner event turn
  let app := runtime.reactiveApplication leaks
  let strategy := retainedImplementation runtime leaks menu owner reference (players owner)
  let sample := leaks owner original.network.pending
  have existsStep (selected) (supported : selected ∈ sample.support) :=
    (frame.activate owner selected).required_resolution_stopped_response_coupling
      bounds menu players reference started leftRecall rightRecall
      (sound.learn owner selected) leftBinding
      rightBinding remaining event payload binding checks outputEq codeEq node turn ready
      timely first (serials.learn owner selected) (published.learn owner selected)
      entered ticks activated due visits absent (coverage selected supported)
      (available selected supported)
  let step := fun selected supported => (existsStep selected supported).choose
  refine ⟨sample.bindOnSupport step, ?_, ?_, ?_⟩
  · rw [map_bindOnSupport]
    change _ = (original.environmentStep app (.activate owner)).bind _
    rw [ReactiveApplication.Execution.activation_samples, PMF.bind_map]
    apply bindOnSupport_eq_bind_of_eq_on_support _
    intro selected supported
    exact (existsStep selected supported).choose_spec.1
  · rw [map_bindOnSupport, ReactiveApplication.Execution.activation_samples,
      PMF.bind_map]
    have same : leaks owner repaired.network.pending = sample := by
      rw [← frame.network]
    change _ = (leaks owner repaired.network.pending).bind _
    rw [same]
    apply bindOnSupport_eq_bind_of_eq_on_support _
    intro selected supported
    exact (existsStep selected supported).choose_spec.2.1
  · intro next supported
    obtain ⟨selected, member, reached⟩ :=
      Set.mem_iUnion₂.mp (PMF.support_bindOnSupport .. ▸ supported)
    rcases (existsStep selected member).choose_spec.2.2 next reached with bad | good
    · left
      exact bad
    · exact Or.inr good

end Vegas.EventGraphRuntime.BindingMemory.Frame
