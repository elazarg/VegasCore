/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactivePacketEvidence
import Vegas.Pending.EventBindingInvariant
import Vegas.EventGraph.CommitmentEvidence

/-! # Previously observed openings authenticate later accepted bindings

A player may observe a candidate certificate before that candidate is used
by the game. Once its accepted association becomes public, the same evidence
certifies the typed graph binding. No new opening call, certificate delivery,
or successful opening receipt is required. The conclusion holds throughout
the observer's information set, including histories off the equilibrium path.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open GameTheory.Math.Probability Interaction

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

theorem reactiveBindingInvariant (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph)) :
    (runtime.reactiveApplication leaks).Invariant State.BindingInvariant where
  submit state who material valid := by
    apply submitStep_bindingInvariant _ _ who material.call.packet
    rw [material.call.register_eq]
    cases material.call.registrationCommand who with
    | none => exact valid
    | some command => exact privateStep_bindingInvariant state valid who command
  handle state message next valid accepted :=
    handle_bindingInvariant runtime state next ⟨message.id, message.payload.call⟩ valid accepted
  environment state command next valid reached :=
    environmentStep_bindingInvariant runtime state next command valid reached

/-- A carried candidate opening and its public graph association are jointly
recognizable from the recipient's own current view. -/
def bindingEvidenceObserved (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (view : (runtime.reactiveApplication leaks).PlayerView)
    (fact : Vegas.EventGraph.CommitmentEvidence graph) : Prop :=
  ∃ candidate, view.application.publicView.accepted fact.binding.field = some candidate ∧
    (⟨candidate, ⟨fact.payload, fact.value⟩⟩ : OpeningFact graph) ∈
      (runtime.packetEvidence leaks).observe view

theorem observed_bindingEvidence_valid (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (execution : (runtime.reactiveApplication leaks).Execution) (who : Player)
    (valid : execution.application.BindingInvariant)
    (sound : (runtime.packetEvidence leaks).Sound execution)
    (fact : Vegas.EventGraph.CommitmentEvidence graph)
    (observed : runtime.bindingEvidenceObserved leaks
      (execution.observe (runtime.reactiveApplication leaks) who) fact) :
    fact.Holds execution.application.config.store := by
  obtain ⟨candidate, associated, certificate⟩ := observed
  exact valid.opening_stored fact.binding candidate fact.value associated
    ((runtime.packetEvidence leaks).observed_valid execution who sound _ certificate)

theorem reactiveBindingInvariant_history (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (inputs : FinDist graph.Inputs) (horizon : Nat)
    (scheduler : (runtime.reactiveApplication leaks).Scheduler) {state}
    (trace : ((runtime.reactiveApplication leaks).protocol
      (inputs.map State.initial) horizon scheduler).Trace state) :
    ReactiveApplication.stateInvariant State.BindingInvariant state :=
  (runtime.reactiveBindingInvariant leaks).history (inputs.map State.initial) horizon scheduler
    (fun state member => by
      obtain ⟨input, _, rfl⟩ := FinDist.support_map .. ▸ member
      exact State.initial_bindingInvariant input) trace

/-- Retrospective certification: every compatible history has this named
binding value, whether the opening was observed before or after association. -/
theorem knows_bindingEvidence (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (inputs : FinDist graph.Inputs) (horizon : Nat)
    (scheduler : (runtime.reactiveApplication leaks).Scheduler)
    (who : Player) (past : List (runtime.reactiveApplication leaks).PlayerEntry)
    (view : (runtime.reactiveApplication leaks).PlayerView)
    (fact : Vegas.EventGraph.CommitmentEvidence graph)
    (observed : runtime.bindingEvidenceObserved leaks view fact) :
    ((runtime.reactiveApplication leaks).information
      (inputs.map State.initial) horizon scheduler).Knows who (some (past, view))
      (fun history => ReactiveApplication.stateInvariant
        (fun state : State graph => fact.Holds state.config.store) history.state) := by
  rintro ⟨⟨state, trace⟩, equal⟩
  change ((runtime.reactiveApplication leaks).signals
    (inputs.map State.initial) horizon scheduler).infoOf who trace = some (past, view) at equal
  rw [ReactiveApplication.info] at equal
  cases state with
  | none => cases equal
  | some control =>
      change (if control.actor = some who then
        some (control.execution.recall who,
          control.execution.observe (runtime.reactiveApplication leaks) who)
        else none) = some (past, view) at equal
      split at equal
      · have sameView := congrArg Prod.snd (Option.some.inj equal)
        change control.execution.observe (runtime.reactiveApplication leaks) who = view at sameView
        apply runtime.observed_bindingEvidence_valid leaks control.execution who
          (runtime.reactiveBindingInvariant_history leaks inputs horizon scheduler trace)
          ((runtime.packetEvidence leaks).history_sound
            (inputs.map State.initial) horizon scheduler trace) fact
        exact sameView.symm ▸ observed
      · cases equal

theorem knows_bindingEvidence_menu (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (menu : (runtime.reactiveApplication leaks).ResponseMenu)
    (inputs : FinDist graph.Inputs) (horizon : Nat)
    (scheduler : (runtime.reactiveApplication leaks).Scheduler)
    (who : Player) (past : List (runtime.reactiveApplication leaks).PlayerEntry)
    (view : (runtime.reactiveApplication leaks).PlayerView)
    (fact : Vegas.EventGraph.CommitmentEvidence graph)
    (observed : runtime.bindingEvidenceObserved leaks view fact) :
    (menu.information (inputs.map State.initial) horizon scheduler).Knows who (some (past, view))
      (fun history => ReactiveApplication.stateInvariant
        (fun state : State graph => fact.Holds state.config.store) history.state) := by
  rintro ⟨⟨state, trace⟩, equal⟩
  change (menu.signals (inputs.map State.initial) horizon scheduler).infoOf who trace =
    some (past, view) at equal
  rw [ReactiveApplication.ResponseMenu.info] at equal
  cases state with
  | none => cases equal
  | some control =>
      change (if control.actor = some who then
        some (control.execution.recall who,
          control.execution.observe (runtime.reactiveApplication leaks) who)
        else none) = some (past, view) at equal
      split at equal
      · have sameView := congrArg Prod.snd (Option.some.inj equal)
        change control.execution.observe (runtime.reactiveApplication leaks) who = view at sameView
        have raw := menu.toRawTrace (inputs.map State.initial) horizon scheduler trace
        apply runtime.observed_bindingEvidence_valid leaks control.execution who
          (runtime.reactiveBindingInvariant_history leaks inputs horizon scheduler raw)
          ((runtime.packetEvidence leaks).history_sound
            (inputs.map State.initial) horizon scheduler raw) fact
        exact sameView.symm ▸ observed
      · cases equal

end Vegas.EventGraphRuntime
