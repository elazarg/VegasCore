module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.EventGraph.CompletionObservation
public import Vegas.EventGraph.ObservationStep
public import Vegas.Pending.EventApplication
public import Vegas.Pending.ReactiveCanonicalDecision

@[expose] public section

/-! # Observations after a foreign binding

The primary graph checkpoint after an active foreign binding preserves the
preceding observation and identifies admission. The submitted value remains
private, including the distinction between usable and unusable admission.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open EventGraph Interaction

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}

private theorem binding_default_admission (config : graph.Config)
    (event : graph.EventId) (ready : config.cut.Ready event)
    (owner : Player) {payload : L.Ty}
    (outputEq : graph.outputLayout event = .binding owner payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .bind owner payload)
    (active : owner ∉ config.defaulted)
    (choice : Option (PublicationResult (L.Val payload)))
    (value : (graph.outputLayout event).Value) :
    (config.complete event ready (cast (congrArg EventField.Action outputEq.symm)
      choice) value).defaults =
      config.defaults.record (if choice.isSome then none else some owner) := by
  let result := cast (congrArg EventField.Value outputEq) value
  have back : cast (congrArg EventField.Value outputEq.symm) result = value := by
    simp [result]
  rw [← back, Config.complete_defaults]
  cases choice with
  | none =>
      rw [config.completion_bind_none_defaultEvent event owner payload outputEq codeEq,
        ite_eq_right active]
      rfl
  | some choice =>
      rw [config.completion_bind_some_defaultEvent event owner payload outputEq codeEq]
      rfl

/-- Equality of focal observations after active foreign binding steps is
equivalent to equality before the steps and agreement on whether each owner
submitted a binding. In particular the new observation records admission
without exposing the hidden binding value. -/
theorem foreign_binding_step_observation_eq_iff
    (focal owner : Player) (foreign : owner ≠ focal)
    (event : graph.EventId) {payload : L.Ty}
    (outputEq : graph.outputLayout event = .binding owner payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .bind owner payload)
    (left right leftNext rightNext : graph.Config)
    (leftReady : left.cut.Ready event) (rightReady : right.cut.Ready event)
    (leftActive : owner ∉ left.defaulted) (rightActive : owner ∉ right.defaulted)
    (leftChoice rightChoice : Option (PublicationResult (L.Val payload)))
    (leftTaken : leftNext ∈ (left.step event leftReady
      (cast (congrArg EventField.Action outputEq.symm) leftChoice)).support)
    (rightTaken : rightNext ∈ (right.step event rightReady
      (cast (congrArg EventField.Action outputEq.symm) rightChoice)).support) :
    graph.playerObserve focal leftNext = graph.playerObserve focal rightNext ↔
      graph.playerObserve focal left = graph.playerObserve focal right ∧
        leftChoice.isSome = rightChoice.isSome := by
  have leftRollback :=
    beforeCompletion_playerObserve_of_step focal left event leftReady _ leftNext leftTaken
  have rightRollback :=
    beforeCompletion_playerObserve_of_step focal right event rightReady _ rightNext rightTaken
  rw [Config.step, PMF.support_map] at leftTaken rightTaken
  obtain ⟨leftValue, _, rfl⟩ := leftTaken
  obtain ⟨rightValue, _, rfl⟩ := rightTaken
  have leftDefault :=
    binding_default_admission left event leftReady owner outputEq codeEq leftActive leftChoice
      leftValue
  have rightDefault :=
    binding_default_admission right event rightReady owner outputEq codeEq rightActive rightChoice
      rightValue
  constructor
  · intro same
    have newest := congrArg
      (fun view : graph.PlayerObservation focal => view.defaults.events.head?) same
    change _ = _ at newest
    simp only [playerObserve, leftDefault, rightDefault, DefaultHistory.record, List.head?]
      at newest
    refine ⟨leftRollback.symm.trans ((congrArg (beforeCompletion event) same).trans rightRollback),
      ?_⟩
    cases leftChoice <;> cases rightChoice <;> simp_all
  · rintro ⟨same, admitted⟩
    apply playerObserve_complete_congr focal left right same
    · intro visible
      have hidden : ¬ graph.fieldVisibleTo focal (.inr event) := by
        change ¬ (graph.outputLayout event).VisibleTo focal
        rw [outputEq]
        simpa [EventField.VisibleTo] using foreign
      exact (hidden visible).elim
    · intro ownerEq
      exact (foreign (Option.some.inj ((nodeView_bind_actor outputEq codeEq).symm.trans
        ownerEq))).elim
    · have defaults : left.defaults = right.defaults :=
        congrArg EventPlayerObservation.defaults same
      have recorded := leftDefault.trans (by rw [defaults, admitted, ← rightDefault])
      simp only [Config.complete_defaults] at recorded
      exact (DefaultHistory.mk.inj recorded |> List.cons.inj).1

/-- With a fresh publicly counted slot in each execution, two active
canonical binding decisions of equal admission either both stay silent or
emit the same packet. Candidate values and prior private recall may differ. -/
theorem foreign_binding_canonical_packets
    (timeouts : EventTimeouts graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (owner : Player) (event : graph.EventId) {payload : L.Ty}
    (outputEq : graph.outputLayout event = .binding owner payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .bind owner payload)
    (node : nodeView graph event = .bind owner payload outputEq codeEq)
    (left right : (reactiveApplication timeouts leaks).Execution)
    (publics : left.application.publicView = right.application.publicView)
    (active : owner ∉ left.application.publicView.observation.defaulted)
    (leftFresh : left.application.candidates.lookup
      (owner, .prepared (left.application.publicView.bindingCount owner)) = .fresh)
    (rightFresh : right.application.candidates.lookup
      (owner, .prepared (right.application.publicView.bindingCount owner)) = .fresh)
    (leftChoice rightChoice : Option (PublicationResult (L.Val payload)))
    (admitted : leftChoice.isSome = rightChoice.isSome) :
    let app := reactiveApplication timeouts leaks
    let respond := fun (execution : app.Execution) selected =>
      canonicalServiceDecision timeouts leaks owner (execution.logs owner)
        (execution.observe app owner) event
        (cast (congrArg EventField.Action outputEq.symm) selected)
    (respond left leftChoice).transmission = none ∧
        (respond right rightChoice).transmission = none ∨
      ∃ leftMaterial rightMaterial,
        respond left leftChoice = ⟨some leftMaterial⟩ ∧
        respond right rightChoice = ⟨some rightMaterial⟩ ∧
        app.packet (app.submit left.application owner leftMaterial)
          owner (left.network.known owner) leftMaterial =
        app.packet (app.submit right.application owner rightMaterial)
          owner (right.network.known owner) rightMaterial := by
  intro app respond
  cases leftChoice with
  | none =>
      cases rightChoice with
      | some result => cases admitted
      | none =>
          left
          constructor
          · exact congrArg ReactiveApplication.Action.transmission
              (canonicalServiceDecision_binding_none timeouts leaks owner (left.logs owner)
                (left.observe app owner) event owner payload outputEq codeEq node)
          · exact congrArg ReactiveApplication.Action.transmission
              (canonicalServiceDecision_binding_none timeouts leaks owner (right.logs owner)
                (right.observe app owner) event owner payload outputEq codeEq node)
  | some leftResult =>
      cases rightChoice with
      | none => cases admitted
      | some rightResult =>
          right
          let serial := left.application.publicView.bindingCount owner
          have aligned : right.application.publicView.bindingCount owner = serial :=
            congrArg (fun view : PublicView graph => view.bindingCount owner) publics.symm
          have freshLeft : canonicalFreshSlot owner (left.observe app owner).application =
              some serial :=
            canonicalFreshSlot_canonical owner _ leftFresh
          have freshRight : canonicalFreshSlot owner (right.observe app owner).application =
              some serial :=
            (canonicalFreshSlot_canonical owner _ rightFresh).trans (congrArg some aligned)
          have leftRespond := canonicalServiceDecision_binding timeouts leaks owner
            (left.logs owner) (left.observe app owner) event payload outputEq codeEq node active
            serial freshLeft leftResult
          have rightActive : owner ∉ right.application.publicView.observation.defaulted :=
            publics ▸ active
          have rightRespond := canonicalServiceDecision_binding timeouts leaks owner
            (right.logs owner) (right.observe app owner) event payload outputEq codeEq node
            rightActive serial freshRight rightResult
          refine ⟨_, _, leftRespond, rightRespond, ?_⟩
          rw [reactiveApplication_packet_none, reactiveApplication_packet_none, publics]

end Vegas.EventGraphRuntime
