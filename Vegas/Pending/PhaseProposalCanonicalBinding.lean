/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Pending.PhaseProposalResponseAliases
import Vegas.Pending.PhasePreparedBinding
import Vegas.Pending.PhaseResponseNormalization

/-! # Every counted binding alias has its actual canonical effective class -/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseProposal

open Interaction EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))
  (bounds : MessageBounds graph)

local notation "app" => phaseApplication runtime leaks

/-- A binding's raw preparation may be absent or mistyped. The effective
source result is evaluated at the current event's declared type; the original
response and its entire private syntax are still retained by alias splitting. -/
theorem responseClass_binding
    (owner : Player) (past : List (app).PlayerEntry) (view : (app).PlayerView)
    (event : graph.EventId) (payload : L.Ty)
    (binding : graph.outputLayout event = .binding owner payload)
    (serial : Nat) (opening : Option (Raw L)) (evidence : EvidenceRequest graph)
    (rawMember : (⟨some ⟨⟨.commitment event (owner, .prepared serial), opening⟩, evidence⟩⟩ :
      (app).Action) ∈ PhaseCount.onePacketActions runtime leaks bounds owner past view)
    (canonicalMember : phaseBindingResponse runtime leaks owner event payload
      ((opening.bind fun raw => raw.as? payload).elim .failure PublicationResult.success) serial ∈
        PhaseCount.onePacketActions runtime leaks bounds owner past view) :
    responseClass runtime leaks bounds owner past view
        ⟨⟨some ⟨⟨.commitment event (owner, .prepared serial), opening⟩, evidence⟩⟩, rawMember⟩ =
      responseClass runtime leaks bounds owner past view
        ⟨phaseBindingResponse runtime leaks owner event payload
          ((opening.bind fun raw => raw.as? payload).elim .failure PublicationResult.success)
          serial, canonicalMember⟩ := by
  let material : WitnessedSubmission graph :=
    ⟨⟨.commitment event (owner, .prepared serial), opening⟩, evidence⟩
  have permitted : PhaseCount.permits ((app).outputs past)
      (PhaseCount.localEnvelope runtime leaks owner past view material) = true := by
    rcases ((PhaseCount.mem_onePacketActions runtime leaks bounds owner past view _).mp rawMember).2
        with impossible | ⟨other, transmitted, allowed⟩
    · cases impossible
    · cases Option.some.inj transmitted
      exact allowed
  have correct := ((PhaseCount.permits_eq_true_iff _ _).mp permitted).2.1
  have call : (PhaseCount.nativeMessage
      (PhaseCount.localEnvelope runtime leaks owner past view material)).payload.call =
        .commitment event (owner, .prepared serial) := PhaseCount.maskPacket_call _ _
  unfold CountCallCorrect at correct
  rw [call] at correct
  have absent := correct.2.1
  have resolved : evidence.resolve owner
      (material.call.candidateAfter owner view.application.1.candidates)
      ((ReactiveApplication.ResponseMenu.knownPackets past view).map PhaseCount.nativeMessage) =
        none := by
    change (PhaseCount.maskPacket view.application.2
      ⟨material.call.packet, _,
        view.application.1.publicView.tokenFor material.call.packet⟩).evidence = none at absent
    unfold PhaseCount.maskPacket at absent
    split at absent <;> split at absent <;> exact absent
  unfold responseClass
  dsimp only
  apply Prod.ext
  · cases decoded : opening.bind (fun raw => raw.as? payload) with
    | none =>
        simp only [bindingPreparation, binding, phaseBindingResponse,
          Option.bind_some, decoded, Option.map_none, Option.elim_none, Option.bind_none]
    | some value =>
        simp only [bindingPreparation, binding, phaseBindingResponse,
          Option.bind_some, decoded, Option.map_some, Option.elim_some, Raw.as?_mk]
  · change some (PhaseCount.localEnvelope runtime leaks owner past view material).payload = _
    cases decoded : opening.bind (fun raw => raw.as? payload) <;>
      simp only [Option.elim_none, Option.elim_some, phaseBindingResponse,
        Option.map_some]
    all_goals
      congr 1
      unfold PhaseCount.localEnvelope
      rw [resolved]
      rfl

end Vegas.EventGraphRuntime.PhaseProposal
