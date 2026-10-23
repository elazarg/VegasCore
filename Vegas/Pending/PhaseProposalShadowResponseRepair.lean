/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Pending.PhaseProposalShadowBindingResponse
import Vegas.Pending.PhaseProposalShadowOpeningResponse
import Vegas.Pending.PhaseBindingResponseDispatcher
import Vegas.Pending.PhaseBindingIdleMenu
import Vegas.Pending.PhaseOpeningMenuShape
import Vegas.Pending.PhaseProposalPreparedResponse

/-! # Every actual counted response has a general recovery repair -/

noncomputable section

namespace Vegas.EventGraphRuntime.BindingShadow

open Interaction EventGraph

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks

/-- The dispatcher covers the actual complete counted menu. It keeps every
other owner's raw response literally, including all past evidence aliases;
only the designated owner's unusable binding preparation is replaced. -/
theorem response_repair (memory : BindingShadow graph) (owner : Player)
    (owned : memory.OwnBindings owner)
    (valid : ∀ slot, memory.candidates slot ≠ some .fresh)
    (left right : (app).Execution)
    (frame : PhaseStateFrame memory owner left.application right.application)
    (supported : memory.CompletedAt right.application.current.native.config)
    (network : left.network = right.network) (receipts : left.receipts = right.receipts)
    (service : left.environmentRecall = right.environmentRecall)
    (recalled : ∀ who, who ≠ owner → left.recall who = right.recall who)
    (prepared : PreparedBindings runtime leaks owner left right)
    (entryRef : left.application.entry.native.config.store.BindingRefines
      right.application.entry.native.config.store)
    (currentRef : left.application.current.native.config.store.BindingRefines
      right.application.current.native.config.store)
    (bounds : MessageBounds graph) (covered : bounds.CoversOutputValues)
    (plan : RuntimePhasePlan graph) (ordered : graph.RevealRelaxedOrdered)
    (inputs : PMF graph.Inputs) (horizon : Nat) (scheduler : (app).Scheduler)
    (remaining : Nat) (actor : Player)
    (leftTrace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace
        (some ⟨remaining, some actor, left⟩))
    (rightTrace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace
        (some ⟨remaining, some actor, right⟩))
    (response : (app).Action)
    (member : response ∈ PhaseCount.onePacketActions runtime leaks bounds actor
      (left.recall actor) (left.observe app actor)) :
    ∃ (target : (app).Action) (nextMemory : BindingShadow graph),
      target ∈ PhaseCount.onePacketActions runtime leaks bounds actor
          (right.recall actor) (right.observe app actor) ∧
      target = PhaseBindingRepair.Frame.responseImage (runtime := runtime) (leaks := leaks)
        owner actor response ∧
      nextMemory.OwnBindings owner ∧
      (∀ slot, nextMemory.candidates slot ≠ some .fresh) ∧
      PhaseStateFrame nextMemory owner (left.respond app actor response).application
        (right.respond app actor target).application ∧
      nextMemory.CompletedAt (right.respond app actor target).application.current.native.config ∧
      (left.respond app actor response).network = (right.respond app actor target).network ∧
      phaseExternalObservation runtime leaks owner (left.respond app actor response) =
        phaseExternalObservation runtime leaks owner (right.respond app actor target) ∧
      PreparedBindings runtime leaks owner (left.respond app actor response)
        (right.respond app actor target) ∧
      (left.respond app actor response).application.entry.native.config.store.BindingRefines
          (right.respond app actor target).application.entry.native.config.store ∧
      (left.respond app actor response).application.current.native.config.store.BindingRefines
          (right.respond app actor target).application.current.native.config.store := by
  classical
  have responseConfig (execution : (app).Execution) (who : Player) (action : (app).Action) :
      (execution.respond app who action).application.current.native.config =
        execution.application.current.native.config := by
    rcases action with ⟨_ | material⟩
    · rfl
    · change (submitStep _ who _).config = _
      rw [submitStep_config, (material.call.register_facts who _).1]
  have responseEntry (execution : (app).Execution) (who : Player) (action : (app).Action) :
      (execution.respond app who action).application.entry = execution.application.entry := by
    rcases action with ⟨_ | material⟩ <;> rfl
  have stores (target : (app).Action) :
      (left.respond app actor response).application.entry.native.config.store.BindingRefines
          (right.respond app actor target).application.entry.native.config.store ∧
      (left.respond app actor response).application.current.native.config.store.BindingRefines
          (right.respond app actor target).application.current.native.config.store := by
    rw [responseEntry, responseEntry, responseConfig, responseConfig]
    exact ⟨entryRef, currentRef⟩
  by_cases foreign : actor ≠ owner
  · have view : left.observe app actor = right.observe app actor := by
      change (⟨left.network.observe actor, left.application.playerView actor, left.receipts⟩ :
        (app).PlayerView) = ⟨_, _, _⟩
      rw [network, receipts, frame.playerView_other owned actor foreign]
      rfl
    have legal : response ∈ PhaseCount.onePacketActions runtime leaks bounds actor
        (right.recall actor) (right.observe app actor) := by
      rw [← recalled actor foreign, ← view]
      exact member
    obtain ⟨paired, nextSupport, nextNetwork, external⟩ :=
      respond_foreign_external runtime leaks memory owner actor foreign owned left right frame
        supported network receipts service recalled response
    refine ⟨response, memory, legal, ?_, owned, valid, paired, nextSupport, nextNetwork,
      external, ?_, (stores response).1, (stores response).2⟩
    · simp only [PhaseBindingRepair.Frame.responseImage, foreign, ↓reduceIte]
    · exact PreparedBindings.respond runtime leaks prepared actor response response (Or.inl foreign)
  · have sameActor : actor = owner := not_ne_iff.mp foreign
    subst actor
    rcases response with ⟨transmission⟩
    cases transmission with
    | none =>
        refine ⟨⟨none⟩, memory, PhaseCount.silence_onePacket runtime leaks bounds owner
          (right.recall owner) (right.observe app owner), ?_, owned, valid, frame, supported,
          network, ?_, ?_, (stores ⟨none⟩).1, (stores ⟨none⟩).2⟩
        · simp only [PhaseBindingRepair.Frame.responseImage, ↓reduceIte]
        · exact respond_wait_external runtime leaks memory owner owned left right frame network
            receipts service recalled
        · exact PreparedBindings.respond runtime leaks prepared owner ⟨none⟩ ⟨none⟩
            (Or.inr (by intro material impossible; cases impossible))
    | some material =>
        obtain ⟨coordinate, request⟩ := PhaseCount.onePacket_request_of_nonsilent runtime leaks
          bounds plan inputs horizon scheduler remaining owner left leftTrace material member
        have named := PhaseCount.onePacket_event_of_request runtime leaks bounds plan ordered inputs
          horizon scheduler remaining owner left leftTrace coordinate request material member
        have permitted : PhaseCount.permits ((app).outputs (left.recall owner))
            (PhaseCount.localEnvelope runtime leaks owner (left.recall owner)
              (left.observe app owner) material) = true := by
          rcases ((PhaseCount.mem_onePacketActions runtime leaks bounds owner _ _ _).mp member).2
            with impossible | ⟨supplied, same, allowed⟩
          · cases impossible
          · cases Option.some.inj same
            exact allowed
        have correct := ((PhaseCount.permits_eq_true_iff _ _).mp permitted).2.1
        have actualCall : (PhaseCount.nativeMessage (PhaseCount.localEnvelope runtime leaks owner
            (left.recall owner) (left.observe app owner) material)).payload.call =
              material.call.packet := PhaseCount.maskPacket_call _ _
        unfold CountCallCorrect at correct
        rw [actualCall] at correct
        rcases material with ⟨⟨packet, preparation⟩, evidence⟩
        cases packet with
        | malformed raw => cases correct
        | commitment event candidate =>
            obtain ⟨bindingOwned, _, candidateOwned, ⟨serial, slot⟩, _⟩ := correct
            change candidate.1 = owner at candidateOwned
            have candidateEq : candidate = (owner, .prepared serial) := Prod.ext candidateOwned slot
            subst candidate
            cases node : nodeView graph event with
            | sample payload law outputEq codeEq =>
                simp only [bindingOwnedBy, outputEq] at bindingOwned
                cases bindingOwned
            | resolve actor payload binding checks outputEq codeEq =>
                simp only [bindingOwnedBy, outputEq] at bindingOwned
                cases bindingOwned
            | bind actor payload outputEq codeEq =>
                change bindingOwnedBy graph owner event = true at bindingOwned
                have actorEq : actor = owner := by
                  simpa only [bindingOwnedBy, outputEq, decide_eq_true_eq] using bindingOwned
                subst actor
                obtain ⟨legal, nextOwned, nextValid, paired, nextSupport, nextNetwork,
                    external, nextPrepared⟩ :=
                  binding_response_repair runtime leaks memory owner owned valid left right frame
                    supported network receipts service recalled prepared bounds covered plan inputs
                      horizon scheduler remaining leftTrace rightTrace event payload outputEq serial
                        preparation evidence member
                refine ⟨_, _, legal, ?_, nextOwned, nextValid, paired, nextSupport, nextNetwork,
                  external, nextPrepared, (stores _).1, (stores _).2⟩
                simp only [PhaseBindingRepair.Frame.responseImage, ↓reduceIte, node]
                rfl
        | opening event candidate raw =>
            have eventEq : coordinate.event = event := Option.some.inj named.symm
            have requestEvent := request
            change left.application.SeedRequest owner
              ⟨coordinate.attempt, coordinate.event⟩ at requestEvent
            rw [request.1, eventEq] at requestEvent
            cases node : nodeView graph event with
            | bind actor payload outputEq codeEq => simp only [node, and_false] at correct
            | sample payload law outputEq codeEq => simp only [node, and_false] at correct
            | resolve actor payload binding checks outputEq codeEq =>
                simp only [node] at correct
                have actorEq : actor = owner := correct.2.1.symm
                subst actor
                let source : (app).Action :=
                  ⟨some ⟨⟨.opening event candidate raw, preparation⟩, evidence⟩⟩
                obtain ⟨legal, paired, nextNetwork, external⟩ :=
                  opening_response_external runtime leaks memory owner owned left right frame
                    currentRef network receipts service recalled bounds plan inputs horizon
                      scheduler remaining leftTrace rightTrace event candidate raw preparation
                        evidence member requestEvent payload binding checks outputEq codeEq node
                have nextSupport : memory.CompletedAt
                    (right.respond app owner source).application.current.native.config := by
                  rw [responseConfig]
                  exact supported
                refine ⟨source, memory, legal, ?_, owned, valid, paired, nextSupport, nextNetwork,
                  external, ?_, (stores source).1, (stores source).2⟩
                · simp only [PhaseBindingRepair.Frame.responseImage, source, ↓reduceIte]
                · exact PreparedBindings.respond runtime leaks prepared owner source source
                    (Or.inr (by
                      intro material same event candidate
                      cases Option.some.inj same
                      intro impossible
                      cases impossible))

end Vegas.EventGraphRuntime.BindingShadow
