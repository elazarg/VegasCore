/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveBindingAllocation
import Vegas.Pending.ReactiveStateInvariant

/-! # Joint binding frames for arbitrary private raw material

Private material can be absent or have a different type from the binding
payload. It nevertheless emits the same canonical packet. The real reserved
binding block preserves all opponents' inputs jointly, together with public
state, network, receipts, service recall and remaining fresh slots.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))

theorem rawBinding_reserved_selection
    (execution : (runtime.reactiveApplication leaks).Execution) (owner : Player)
    (event : graph.EventId) (serial : Nat) (opening : Option (Raw L))
    (serials : execution.network.SerialsBeforeNext)
    (players : Player → (runtime.reactiveApplication leaks).Policy)
    (scheduler : runtime.NetworkPolicy leaks) :
    let app := runtime.reactiveApplication leaks
    let response : app.Action :=
      ⟨some ⟨⟨.commitment event (owner, .prepared serial), opening⟩, .none⟩⟩
    let submitted := execution.respond app owner response
    runtime.interactionStep leaks players scheduler (.includeLatest event owner) submitted =
      submitted.environmentStep app (.include (owner, execution.network.nextSerial owner)) := by
  let material : WitnessedSubmission graph :=
    ⟨⟨.commitment event (owner, .prepared serial), opening⟩, .none⟩
  have selected := runtime.reactiveLatest_after_submit leaks owner event execution serials
    material rfl
  dsimp only
  unfold interactionStep
  rw [interactionInstruction, selected, PMF.pure_bind]
  simp only [ReactiveApplication.dispatch, ReactiveApplication.Command.actor?]
  exact PMF.bind_pure _

theorem rawBinding_submit_hidden_congr
    (left right : (runtime.reactiveApplication leaks).Execution) (owner : Player)
    (network : left.network = right.network) (receipts : left.receipts = right.receipts)
    (publicEq : left.application.publicView = right.application.publicView)
    (views : ∀ who, who ≠ owner →
      left.application.playerView who = right.application.playerView who)
    (recall : ∀ who, who ≠ owner → left.recall who = right.recall who)
    (event : graph.EventId) (serial : Nat) (first second : Option (Raw L)) :
    let app := runtime.reactiveApplication leaks
    let before := left.respond app owner
      ⟨some ⟨⟨.commitment event (owner, .prepared serial), first⟩, .none⟩⟩
    let after := right.respond app owner
      ⟨some ⟨⟨.commitment event (owner, .prepared serial), second⟩, .none⟩⟩
    before.network = after.network ∧ before.receipts = after.receipts ∧
      before.application.publicView = after.application.publicView ∧
      (∀ who, who ≠ owner →
        before.application.playerView who = after.application.playerView who) ∧
      (∀ who, who ≠ owner → before.recall who = after.recall who) := by
  let app := runtime.reactiveApplication leaks
  have foreign (execution : app.Execution) (who : Player) (different : who ≠ owner)
      (opening : Option (Raw L)) :
      let response : app.Action :=
        ⟨some ⟨⟨.commitment event (owner, .prepared serial), opening⟩, .none⟩⟩
      (execution.respond app owner response).application.playerView who =
        execution.application.playerView who := by
    exact (submitStep_playerView_other _ owner who different _).trans
      (Submission.register_other _ execution.application owner who different)
  refine ⟨?_, receipts, ?_, ?_, ?_⟩
  · simp only [ReactiveApplication.Execution.respond, reactiveApplication_packet_none,
      network, publicEq]
  · exact (runtime.reactive_respond_application leaks left owner _).2.trans
      (publicEq.trans (runtime.reactive_respond_application leaks right owner _).2.symm)
  · intro who different
    exact (foreign left who different first).trans
      ((views who different).trans (foreign right who different second).symm)
  · intro who different
    exact (app.respond_recall_other left owner who different _).trans
      ((recall who different).trans (app.respond_recall_other right owner who different _).symm)

/-- The coupled block law keeps a single joint readout, not separate marginal
laws for different opponents. No observer or additional player is required. -/
theorem rawBinding_reserved_hidden_congr
    (left right : (runtime.reactiveApplication leaks).Execution) (owner : Player)
    (network : left.network = right.network) (receipts : left.receipts = right.receipts)
    (publicEq : left.application.publicView = right.application.publicView)
    (serviceRecall : left.environmentRecall = right.environmentRecall)
    (views : ∀ who, who ≠ owner →
      left.application.playerView who = right.application.playerView who)
    (recall : ∀ who, who ≠ owner → left.recall who = right.recall who)
    (slots : ∀ query, left.application.candidates.lookup (owner, query) = .fresh ↔
      right.application.candidates.lookup (owner, query) = .fresh)
    (event : graph.EventId) (payload : L.Ty)
    (outputEq : graph.outputLayout event = .binding owner payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .bind owner payload)
    (node : nodeView graph event = .bind owner payload outputEq codeEq)
    (first second : Option (Raw L)) (serial : Nat)
    (ready : left.application.config.cut.Ready event)
    (timely : left.application.WithinDeadline runtime event)
    (vacant : left.application.accepted (.inr event) = none)
    (unused : left.application.HandleUnused (owner, .prepared serial))
    (serials : left.network.SerialsBeforeNext)
    (players : Player → (runtime.reactiveApplication leaks).Policy)
    (scheduler : runtime.NetworkPolicy leaks) :
    let app := runtime.reactiveApplication leaks
    let readout (next : app.Execution) :=
      (next.network, next.receipts, next.application.publicView, next.environmentRecall,
        (fun who => if who = owner then none
          else some (next.recall who, next.application.playerView who)),
        fun query => next.application.candidates.lookup (owner, query) = .fresh)
    (runtime.interactionStep leaks players scheduler (.includeLatest event owner)
      (left.respond app owner
        ⟨some ⟨⟨.commitment event (owner, .prepared serial), first⟩, .none⟩⟩)).map
          readout =
      (runtime.interactionStep leaks players scheduler (.includeLatest event owner)
        (right.respond app owner
          ⟨some ⟨⟨.commitment event (owner, .prepared serial), second⟩, .none⟩⟩)).map
            readout := by
  let app := runtime.reactiveApplication leaks
  let before := left.respond app owner
    ⟨some ⟨⟨.commitment event (owner, .prepared serial), first⟩, .none⟩⟩
  let after := right.respond app owner
    ⟨some ⟨⟨.commitment event (owner, .prepared serial), second⟩, .none⟩⟩
  let id := (owner, left.network.nextSerial owner)
  have submitted := runtime.rawBinding_submit_hidden_congr leaks left right owner network
    receipts publicEq views recall event serial first second
  change before.network = after.network ∧ before.receipts = after.receipts ∧
    before.application.publicView = after.application.publicView ∧
    (∀ who, who ≠ owner → before.application.playerView who = after.application.playerView who) ∧
    (∀ who, who ≠ owner → before.recall who = after.recall who) at submitted
  have found : before.network.lookup id =
      some ⟨id, ⟨.commitment event (owner, .prepared serial), none, some ⟨event⟩⟩⟩ :=
    respond_submit_lookup_of_ready runtime leaks left owner
      ⟨.commitment event (owner, .prepared serial), first⟩ serials event rfl ready
  have configEq : before.application.config = left.application.config :=
    (runtime.reactive_respond_application leaks left owner _).1
  have beforePublic : before.application.publicView = left.application.publicView :=
    (runtime.reactive_respond_application leaks left owner _).2
  have beforeReady : before.application.config.cut.Ready event := by rwa [configEq]
  have beforeTimely : before.application.WithinDeadline runtime event := by
    unfold State.WithinDeadline
    rw [show before.application.clock = left.application.clock from
      congrArg PublicView.clock beforePublic,
      show before.application.activatedAt = left.application.activatedAt from
        congrArg PublicView.activatedAt beforePublic]
    exact timely
  have beforeAccepted : before.application.accepted = left.application.accepted :=
    congrArg PublicView.accepted beforePublic
  have beforeVacant := (congrFun beforeAccepted (.inr event)).trans vacant
  have beforeUnused : before.application.HandleUnused (owner, .prepared serial) := by
    intro field associated
    exact unused field ((congrFun beforeAccepted field).symm.trans associated)
  have included := runtime.reactive_include_binding_hidden_congr leaks before after owner
    submitted.1 submitted.2.1 submitted.2.2.1 submitted.2.2.2.1 submitted.2.2.2.2
    id event (owner, .prepared serial) none found
  have includedPublic := runtime.reactive_include_binding_public_congr leaks before after
    submitted.1 submitted.2.2.1 owner event payload outputEq codeEq node id
    (owner, .prepared serial) none rfl rfl found beforeReady beforeTimely beforeVacant beforeUnused
  have fixedBefore : before.application.candidates.lookup (owner, .prepared serial) ≠ .fresh :=
    submitStep_commitment_fixed _ owner event (.prepared serial)
  have fixedAfter : after.application.candidates.lookup (owner, .prepared serial) ≠ .fresh :=
    submitStep_commitment_fixed _ owner event (.prepared serial)
  have beforeCandidates := runtime.reactive_include_fixed_binding_candidates leaks before id
    event (owner, .prepared serial) none found fixedBefore
  have afterCandidates := runtime.reactive_include_fixed_binding_candidates leaks after id
    event (owner, .prepared serial) none (submitted.1 ▸ found) fixedAfter
  have freshSlots (query : CandidateSlot graph) :
      before.application.candidates.lookup (owner, query) = .fresh ↔
        after.application.candidates.lookup (owner, query) = .fresh := by
    exact (runtime.submitted_binding_fresh_iff leaks left owner event serial first query).trans
      ((and_congr Iff.rfl (slots query)).trans
        (runtime.submitted_binding_fresh_iff leaks right owner event serial second query).symm)
  have beforeService : before.environmentRecall = after.environmentRecall := serviceRecall
  have environment : before.observeEnvironment app = after.observeEnvironment app := by
    change ReactiveApplication.EnvironmentView.mk _ _ _ =
      ReactiveApplication.EnvironmentView.mk _ _ _
    rw [submitted.1, submitted.2.1]
    exact congrArg (fun observed =>
      (⟨after.network.publicView, observed, after.receipts⟩ : app.EnvironmentView)) submitted.2.2.1
  dsimp only
  rw [runtime.rawBinding_reserved_selection leaks left owner event serial first
    serials players scheduler,
    runtime.rawBinding_reserved_selection leaks right owner event serial second
      (network ▸ serials) players scheduler]
  have nonce : right.network.nextSerial owner = left.network.nextSerial owner :=
    congrArg (fun net => net.nextSerial owner) network.symm
  rw [nonce]
  simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map]
  apply congrArg PMF.pure
  change ( (before.includePending app id).network, (before.includePending app id).receipts,
      (before.includePending app id).application.publicView,
      before.environmentRecall ++ [⟨before.observeEnvironment app, .include id⟩], _, _) =
    ( (after.includePending app id).network, (after.includePending app id).receipts,
      (after.includePending app id).application.publicView,
      after.environmentRecall ++ [⟨after.observeEnvironment app, .include id⟩], _, _)
  refine Prod.ext included.1 (Prod.ext included.2.1 (Prod.ext includedPublic
    (Prod.ext (by rw [beforeService, environment]) (Prod.ext ?_ ?_))))
  · funext who
    by_cases own : who = owner
    · simp only [own, ↓reduceIte]
    · simp only [own, ↓reduceIte]
      exact congrArg some (Prod.ext (included.2.2.2 who own) (included.2.2.1 who own))
  · funext query
    apply propext
    rw [beforeCandidates, afterCandidates]
    exact freshSlots query

end Vegas.EventGraphRuntime
