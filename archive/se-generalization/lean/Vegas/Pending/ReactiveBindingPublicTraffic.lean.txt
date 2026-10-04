/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveBindingRepair
import Vegas.Pending.ReactiveBindingAsyncLikelihood
import Vegas.Pending.PacketNodeKind

/-! # Joint public and foreign traffic during an opaque binding

The readout retains the public scheduler's complete input and recall together
with every nonowner's private view and recall. Commitment inclusion uses only
public acceptance conditions. A sole-ready binding rejects every other packet.
The public coordinate is explicit, including when there are no foreign players.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

/-- Complete jointly retained traffic while one owner's private binding
meaning and private response recall may differ. -/
def bindingPublicTraffic (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (owner : Player) (execution : (runtime.reactiveApplication leaks).Execution) :=
  (execution.network, execution.receipts, execution.environmentRecall,
    execution.application.publicView, fun who => if who = owner then none
      else some (execution.recall who, execution.application.playerView who))

private theorem include_commitment_public_congr (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (left right : (runtime.reactiveApplication leaks).Execution)
    (network : left.network = right.network)
    (publicEq : left.application.publicView = right.application.publicView)
    (id : MessageId Player) (event : graph.EventId) (candidate : Handle graph)
    (evidence : Option (OpeningFact graph)) (token : Option (ReadinessToken graph))
    (found : left.network.lookup id =
      some ⟨id, ⟨.commitment event candidate, evidence, token⟩⟩) :
    (left.includePending (runtime.reactiveApplication leaks) id).application.publicView =
      (right.includePending (runtime.reactiveApplication leaks) id).application.publicView := by
  have rightFound : right.network.lookup id =
      some ⟨id, ⟨.commitment event candidate, evidence, token⟩⟩ := network ▸ found
  by_cases valid :
      (WitnessedPacket.mk (.commitment event candidate) evidence token).tokenValid = true
  · have tokenEq : token = some ⟨event⟩ := by
      obtain ⟨target, named, tokenEq⟩ := (WitnessedPacket.tokenValid_iff _).mp valid
      have same : event = target := Option.some.inj named
      cases same
      exact tokenEq
    subst token
    by_cases allowed : left.application.publicView.BindingIncludable runtime
        ⟨id, .commitment event candidate⟩
    · change left.application.publicView.EventReady event ∧
          left.application.WithinDeadline runtime event ∧ _ at allowed
      obtain ⟨publicReady, timely, checks⟩ := allowed
      have ready := (left.application.publicView_eventReady event).mp publicReady
      cases node : nodeView graph event with
      | resolve owner payload binding checks' outputEq codeEq =>
          simp only [node] at checks
      | sample payload law outputEq codeEq => simp only [node] at checks
      | bind owner payload outputEq codeEq =>
          simp only [node, Message.sender] at checks
          obtain ⟨sender, owned, vacant, unused⟩ := checks
          exact runtime.reactive_include_binding_public_congr leaks left right network publicEq
            owner event payload outputEq codeEq node id candidate evidence sender owned found
            ready timely vacant unused
    · have rejected (state : State graph)
          (same : state.publicView = left.application.publicView) :
          handle runtime state ⟨id, .commitment event candidate⟩ = none := by
        cases handled : handle runtime state ⟨id, .commitment event candidate⟩ with
        | none => rfl
        | some next =>
            have includable := (State.publicView_bindingIncludable runtime state id event
              candidate).mpr (by simp only [handled, Option.isSome_some])
            exact False.elim (allowed (same ▸ includable))
      have leftRejected := rejected left.application rfl
      have rightRejected := rejected right.application publicEq.symm
      simpa only [ReactiveApplication.Execution.includePending, MessageNetwork.includePending,
        found, rightFound, reactiveApplication_handle, WitnessedPacket.tokenValid_commitment,
        ite_true, leftRejected, rightRejected, Option.getD_none] using publicEq
  · have rejected (state : State graph) :
        (runtime.reactiveApplication leaks).handle state
          ⟨id, ⟨.commitment event candidate, evidence, token⟩⟩ = none :=
      reactiveApplication_handle_of_not_tokenValid runtime leaks state _
        (Bool.eq_false_iff.mpr valid)
    simpa only [ReactiveApplication.Execution.includePending, MessageNetwork.includePending,
      found, rightFound, rejected, Option.getD_none] using publicEq

/-- Commitment inclusion couples the full public record and all foreign
inputs jointly, including acceptance or rejection of arbitrary handles. -/
theorem bindingPublicTraffic_include_commitment (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (owner : Player) (left right : (runtime.reactiveApplication leaks).Execution)
    (same : runtime.bindingPublicTraffic leaks owner left =
      runtime.bindingPublicTraffic leaks owner right)
    (id : MessageId Player) (event : graph.EventId) (candidate : Handle graph)
    (evidence : Option (OpeningFact graph)) (token : Option (ReadinessToken graph))
    (found : left.network.lookup id =
      some ⟨id, ⟨.commitment event candidate, evidence, token⟩⟩) :
    runtime.bindingPublicTraffic leaks owner
        (left.includePending (runtime.reactiveApplication leaks) id) =
      runtime.bindingPublicTraffic leaks owner
        (right.includePending (runtime.reactiveApplication leaks) id) := by
  have networks := congrArg Prod.fst same
  have receipts := congrArg (fun read => read.2.1) same
  have environments := congrArg (fun read => read.2.2.1) same
  have publics := congrArg (fun read => read.2.2.2.1) same
  have foreign := congrArg (fun read => read.2.2.2.2) same
  dsimp only [bindingPublicTraffic] at networks receipts environments publics foreign
  have views (who : Player) (different : who ≠ owner) :
      left.application.playerView who = right.application.playerView who := by
    have localEq := congrFun foreign who
    simpa only [different, ite_false, Option.map_some, Option.some.injEq] using congrArg
      (fun value => value.map Prod.snd) localEq
  have recalled (who : Player) (different : who ≠ owner) :
      left.recall who = right.recall who := by
    have localEq := congrFun foreign who
    simpa only [different, ite_false, Option.map_some, Option.some.injEq] using congrArg
      (fun value => value.map Prod.fst) localEq
  obtain ⟨nextNetworks, nextReceipts, nextViews, nextRecall⟩ :=
    runtime.reactive_include_binding_hidden_congr leaks left right owner networks receipts
      publics views recalled id event candidate evidence found
  have nextPublic := include_commitment_public_congr runtime leaks left right networks publics
    id event candidate evidence token found
  have nextEnvironment :
      (left.includePending (runtime.reactiveApplication leaks) id).environmentRecall =
        (right.includePending (runtime.reactiveApplication leaks) id).environmentRecall := by
    have rightFound := networks ▸ found
    simpa only [ReactiveApplication.Execution.includePending, MessageNetwork.includePending,
      found, rightFound] using environments
  refine Prod.ext nextNetworks (Prod.ext nextReceipts (Prod.ext nextEnvironment
    (Prod.ext nextPublic ?_)))
  funext who
  dsimp only [bindingPublicTraffic]
  by_cases different : who ≠ owner
  · simp only [different, ite_false]
    exact congrArg some (Prod.ext (nextRecall who different) (nextViews who different))
  · simp only [not_ne_iff.mp different, ite_true]

private theorem reject_noncommitment_of_sole_binding (runtime : EventGraphRuntime graph)
    (state : State graph) (event : graph.EventId) (owner : Player) (payload : L.Ty)
    (outputEq : graph.outputLayout event = .binding owner payload)
    (codeEq : cast (congrArg (EventGraph.EventCode graph.layout) outputEq)
      (graph.nodes event) = .bind owner payload)
    (node : nodeView graph event = .bind owner payload outputEq codeEq)
    (sole : state.publicView.SoleReady event) (message : Message Player (Payload graph))
    (notCommitment : ∀ target candidate, message.payload ≠ .commitment target candidate) :
    handle runtime state message = none := by
  cases accepted : handle runtime state message with
  | none => rfl
  | some next =>
      obtain ⟨target, named, ready, _, _⟩ :=
        runtime.handle_config_mem_step state next message accepted
      have current := sole.2 target ((state.publicView_eventReady target).mpr ready)
      have matched := runtime.handle_matchesNode state next message accepted
      cases call : message.payload with
      | commitment addressed candidate => exact (notCommitment addressed candidate call).elim
      | malformed raw =>
          simp only [handle, call] at accepted
          cases accepted
      | opening addressed candidate raw | withhold addressed =>
          have addressedEq : addressed = target := by
            simpa only [call, Payload.event?, Option.some.injEq] using named
          subst addressed
          subst target
          simp only [call, Payload.MatchesNode, node] at matched

/-- Every pending inclusion preserves the same joint traffic while the only
ready event is a binding. Stale and malformed packets are included in the law. -/
theorem bindingPublicTraffic_include (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (owner : Player) (left right : (runtime.reactiveApplication leaks).Execution)
    (same : runtime.bindingPublicTraffic leaks owner left =
      runtime.bindingPublicTraffic leaks owner right)
    (event : graph.EventId) (payload : L.Ty)
    (outputEq : graph.outputLayout event = .binding owner payload)
    (codeEq : cast (congrArg (EventGraph.EventCode graph.layout) outputEq)
      (graph.nodes event) = .bind owner payload)
    (node : nodeView graph event = .bind owner payload outputEq codeEq)
    (sole : left.application.publicView.SoleReady event) (id : MessageId Player) :
    runtime.bindingPublicTraffic leaks owner
        (left.includePending (runtime.reactiveApplication leaks) id) =
      runtime.bindingPublicTraffic leaks owner
        (right.includePending (runtime.reactiveApplication leaks) id) := by
  have networks := congrArg Prod.fst same
  have publics := congrArg (fun read => read.2.2.2.1) same
  dsimp only [bindingPublicTraffic] at networks publics
  have rightSole : right.application.publicView.SoleReady event := publics ▸ sole
  cases found : left.network.lookup id with
  | none =>
      have rightFound : right.network.lookup id = none := networks ▸ found
      simpa only [ReactiveApplication.Execution.includePending, MessageNetwork.includePending,
        found, rightFound] using same
  | some message =>
      have rightFound : right.network.lookup id = some message := networks ▸ found
      have identified : message.id = id :=
        of_decide_eq_true (List.find?_eq_some_iff_append.mp found).1
      cases call : message.payload.call with
      | commitment target candidate =>
          rcases message with ⟨messageId, ⟨packet, evidence, token⟩⟩
          dsimp only at call identified
          subst packet
          subst messageId
          exact runtime.bindingPublicTraffic_include_commitment leaks owner left right same
            id target candidate evidence token found
      | opening target candidate raw | withhold target | malformed raw =>
          have rejected (state : State graph) (ready : state.publicView.SoleReady event) :
              (runtime.reactiveApplication leaks).handle state message = none := by
            apply reactiveHandle_none
            apply reject_noncommitment_of_sole_binding runtime state event owner payload
              outputEq codeEq node ready
            intro addressed candidate impossible
            rw [call] at impossible
            cases impossible
          have leftRejected := rejected left.application sole
          have rightRejected := rejected right.application rightSole
          simpa only [bindingPublicTraffic, ReactiveApplication.Execution.includePending,
            MessageNetwork.includePending, found, rightFound, leftRejected, rightRejected,
            Option.getD_none, Option.isSome_none] using congrArg
            (fun read => (read.1.includePending id |>.2, read.2.1 ++ [(id, false)], read.2.2)) same

/-- A common foreign raw response preserves every foreign input and the
public scheduler's data jointly. Evidence requests remain actual emissions. -/
theorem bindingPublicTraffic_respond_foreign (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (owner actor : Player) (foreign : actor ≠ owner)
    (left right : (runtime.reactiveApplication leaks).Execution)
    (same : runtime.bindingPublicTraffic leaks owner left =
      runtime.bindingPublicTraffic leaks owner right)
    (response : (runtime.reactiveApplication leaks).Action) :
    runtime.bindingPublicTraffic leaks owner
        (left.respond (runtime.reactiveApplication leaks) actor response) =
      runtime.bindingPublicTraffic leaks owner
        (right.respond (runtime.reactiveApplication leaks) actor response) := by
  have networks := congrArg Prod.fst same
  have receipts := congrArg (fun read => read.2.1) same
  have environments := congrArg (fun read => read.2.2.1) same
  have publics := congrArg (fun read => read.2.2.2.1) same
  have locals := congrArg (fun read => read.2.2.2.2) same
  dsimp only [bindingPublicTraffic] at networks receipts environments publics locals
  have views (who : Player) (different : who ≠ owner) :
      left.application.playerView who = right.application.playerView who := by
    have localEq := congrFun locals who
    simpa only [different, ite_false, Option.map_some, Option.some.injEq] using congrArg
      (fun value => value.map Prod.snd) localEq
  have recalled (who : Player) (different : who ≠ owner) :
      left.recall who = right.recall who := by
    have localEq := congrFun locals who
    simpa only [different, ite_false, Option.map_some, Option.some.injEq] using congrArg
      (fun value => value.map Prod.fst) localEq
  obtain ⟨nextNetworks, nextReceipts, nextViews, nextRecall⟩ :=
    runtime.reactive_respond_hidden_congr leaks left right owner actor foreign networks receipts
      views recalled response
  let app := runtime.reactiveApplication leaks
  have publicResponse (execution : (runtime.reactiveApplication leaks).Execution) :
      (execution.respond app actor response).application.publicView =
        execution.application.publicView := by
    rcases response with ⟨transmission⟩
    cases transmission with
    | none => rfl
    | some material => exact runtime.reactiveApplication_submit_publicView leaks _ actor material
  refine Prod.ext nextNetworks (Prod.ext nextReceipts (Prod.ext environments
    (Prod.ext ((publicResponse left).trans (publics.trans (publicResponse right).symm)) ?_)))
  funext who
  dsimp only [bindingPublicTraffic]
  by_cases different : who ≠ owner
  · simp only [different, ite_false]
    exact congrArg some (Prod.ext (nextRecall who different) (nextViews who different))
  · simp only [not_ne_iff.mp different, ite_true]

/-- Distinct typed private meanings of one canonical binding packet produce
the same jointly public and foreign traffic immediately after transmission. -/
theorem bindingPublicTraffic_binding_response (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (owner : Player) (left right : (runtime.reactiveApplication leaks).Execution)
    (same : runtime.bindingPublicTraffic leaks owner left =
      runtime.bindingPublicTraffic leaks owner right)
    (event : graph.EventId) (payload : L.Ty)
    (first second : PublicationResult (L.Val payload)) (serial : Nat) :
    runtime.bindingPublicTraffic leaks owner
        (left.respond (runtime.reactiveApplication leaks) owner
          (runtime.reactiveBinding leaks owner event payload first serial)) =
      runtime.bindingPublicTraffic leaks owner
        (right.respond (runtime.reactiveApplication leaks) owner
          (runtime.reactiveBinding leaks owner event payload second serial)) := by
  have networks := congrArg Prod.fst same
  have receipts := congrArg (fun read => read.2.1) same
  have environments := congrArg (fun read => read.2.2.1) same
  have publics := congrArg (fun read => read.2.2.2.1) same
  have locals := congrArg (fun read => read.2.2.2.2) same
  dsimp only [bindingPublicTraffic] at networks receipts environments publics locals
  have views (who : Player) (different : who ≠ owner) :
      left.application.playerView who = right.application.playerView who := by
    have localEq := congrFun locals who
    simpa only [different, ite_false, Option.map_some, Option.some.injEq] using congrArg
      (fun value => value.map Prod.snd) localEq
  have recalled (who : Player) (different : who ≠ owner) :
      left.recall who = right.recall who := by
    have localEq := congrFun locals who
    simpa only [different, ite_false, Option.map_some, Option.some.injEq] using congrArg
      (fun value => value.map Prod.fst) localEq
  obtain ⟨nextNetworks, nextReceipts, nextPublic, nextViews, nextRecall⟩ :=
    runtime.reactiveBinding_submit_hidden_congr leaks left right owner networks receipts publics
      views recalled event payload first second serial
  refine Prod.ext nextNetworks (Prod.ext nextReceipts (Prod.ext environments
    (Prod.ext nextPublic ?_)))
  funext who
  dsimp only [bindingPublicTraffic]
  by_cases different : who ≠ owner
  · simp only [different, ite_false]
    exact congrArg some (Prod.ext (nextRecall who different) (nextViews who different))
  · simp only [not_ne_iff.mp different, ite_true]

end Vegas.EventGraphRuntime
