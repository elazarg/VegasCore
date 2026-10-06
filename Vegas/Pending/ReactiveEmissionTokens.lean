/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveRuntime
import Interaction.ReactiveServiceInvariant
import Interaction.ReactiveProvenance

/-! # Readiness tokens over whole histories

A sender never writes a readiness token: emission attaches the token issued by
the public view the sender observes when it responds. This module lifts that
per-response fact to every legal history. Each emission in a player's recall
carries exactly the token of the view recorded with that response, so a token
is present only when the prerequisites of the call's event had completed in
that view. Every envelope anywhere in the network, including pending, leaked
and published copies, is such an emission of its author.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open GameTheory.Math.Probability Interaction

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))

/-- Every emission recorded in a player's recall carries the readiness token
issued, for its call, by the public view recorded with that response. -/
def EmissionTokens (execution : (runtime.reactiveApplication leaks).Execution) : Prop :=
  ∀ who, ∀ entry ∈ execution.recall who, ∀ message, entry.emitted = some message →
    message.payload.token = entry.beforeView.application.publicView.tokenFor message.payload.call

theorem emissionTokens_respond (execution : (runtime.reactiveApplication leaks).Execution)
    (who : Player) (action : (runtime.reactiveApplication leaks).Action)
    (valid : runtime.EmissionTokens leaks execution) :
    runtime.EmissionTokens leaks (execution.respond (runtime.reactiveApplication leaks) who action)
    := by
  intro observer entry member message emitted
  by_cases same : observer = who
  · subst observer
    rcases action with ⟨transmission⟩
    cases transmission with
    | none =>
        simp only [ReactiveApplication.Execution.respond, ↓reduceIte, List.mem_append,
          List.mem_singleton] at member
        rcases member with prior | rfl
        · exact valid _ entry prior message emitted
        · cases emitted
    | some material =>
        simp only [ReactiveApplication.Execution.respond, ↓reduceIte, List.mem_append,
          List.mem_singleton] at member
        rcases member with prior | rfl
        · exact valid _ entry prior message emitted
        · cases Option.some.inj emitted
          exact runtime.reactiveApplication_packet_token leaks execution.application who
            (execution.network.known who) material
  · rw [(runtime.reactiveApplication leaks).respond_recall_other execution who observer same
      action] at member
    exact valid observer entry member message emitted

theorem emissionTokensInvariant
    (scheduler : (runtime.reactiveApplication leaks).Scheduler) :
    (runtime.reactiveApplication leaks).ServiceInvariant scheduler
      (runtime.EmissionTokens leaks) where
  respond execution who action valid := runtime.emissionTokens_respond leaks execution who action
    valid
  environment execution next command valid _ reached := by
    intro who entry member
    rw [(runtime.reactiveApplication leaks).environmentStep_recall execution next command
      reached] at member
    exact valid who entry member

/-- **Tokens over histories.** At every legal history, under arbitrary player
responses and every scheduler, every packet a player emitted carries exactly
the readiness token that the public view recorded with that response issues
for its call. -/
theorem history_emissionTokens (initial : PMF (State graph)) (horizon : Nat)
    (scheduler : (runtime.reactiveApplication leaks).Scheduler)
    {control : (runtime.reactiveApplication leaks).Control}
    (trace : ((runtime.reactiveApplication leaks).protocol initial horizon scheduler).Trace
      (some control)) :
    runtime.EmissionTokens leaks control.execution :=
  (runtime.emissionTokensInvariant leaks scheduler).history initial horizon
    (fun _ _ _ _ member => False.elim (List.not_mem_nil member)) trace

/-- At every legal history a present token names the emitted call's event, and
every direct prerequisite of that event had completed in the public view the
sender observed when it emitted the packet. -/
theorem history_emission_token_issued (initial : PMF (State graph)) (horizon : Nat)
    (scheduler : (runtime.reactiveApplication leaks).Scheduler)
    {control : (runtime.reactiveApplication leaks).Control}
    (trace : ((runtime.reactiveApplication leaks).protocol initial horizon scheduler).Trace
      (some control))
    (who : Player) (entry : (runtime.reactiveApplication leaks).PlayerEntry)
    (member : entry ∈ control.execution.recall who)
    (message : Message Player (WitnessedPacket graph)) (emitted : entry.emitted = some message)
    (token : ReadinessToken graph) (attached : message.payload.token = some token) :
    message.payload.call.event? graph = some token.event ∧
      ∀ predecessor ∈ graph.order.predecessors token.event,
        predecessor ∈ entry.beforeView.application.publicView.observation.completionOrder := by
  have carried := runtime.history_emissionTokens leaks initial horizon scheduler trace who entry
    member message emitted
  rw [attached, PublicView.tokenFor] at carried
  cases named : message.payload.call.event? graph with
  | none => simp [named] at carried
  | some event =>
      rw [named, Option.bind_some] at carried
      obtain ⟨rfl, complete⟩ := (PublicView.readinessToken?_eq_some_iff _ event token).mp
        carried.symm
      exact ⟨rfl, complete⟩

/-- Every envelope in the network at a legal history, pending, leaked or
published, is an emission recorded in its author's recall and carries the
token issued by the public view recorded with that emission. -/
theorem history_network_tokens (initial : PMF (State graph)) (horizon : Nat)
    (scheduler : (runtime.reactiveApplication leaks).Scheduler)
    {control : (runtime.reactiveApplication leaks).Control}
    (trace : ((runtime.reactiveApplication leaks).protocol initial horizon scheduler).Trace
      (some control)) :
    control.execution.network.Satisfies fun message =>
      ∃ entry ∈ control.execution.recall message.sender, entry.emitted = some message ∧
        message.payload.token =
          entry.beforeView.application.publicView.tokenFor message.payload.call := by
  have provenance : control.execution.Provenance (runtime.reactiveApplication leaks) :=
    (runtime.reactiveApplication leaks).history_provenance initial horizon scheduler trace
  have tokens := runtime.history_emissionTokens leaks initial horizon scheduler trace
  apply provenance.mono
  rintro message ⟨entry, member, _material, _transmission, emitted, _packet⟩
  exact ⟨entry, member, emitted, tokens message.sender entry member message emitted⟩

end Vegas.EventGraphRuntime
