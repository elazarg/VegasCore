/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.OnePacketCompletionCases
import Vegas.Game.OnePacketForced
import Interaction.MessageNetworkIdentity
import Interaction.ReactiveMessageIdentity
import Vegas.Game.ServiceSettledEvidence

/-! # Pending packets at forced one-packet histories

A pending opening carries readiness evidence. If its event already completed,
actual native provenance supplies either another owner-authored packet on the
ledger or a failed public publication. Count permission excludes the former;
the forced source decoding excludes the latter. Thus pending openings concern
only the currently ready event.
-/

noncomputable section

namespace Vegas

open SourceProgram
open GameTheory GameTheory.Protocol Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {runtime : EventGraphRuntime (graph setup)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
  (bounds : MessageBounds (graph setup))

/-- At a forced native history, every pending packet is an evidence-free
commitment or an owned opening carrying its exact certificate for a ready event. -/
theorem onePacket_pending_of_forced (horizon : Nat)
    (scheduler : (application setup runtime leaks).Scheduler) (who : Player)
    (history : ((bounds.onePacketMenu runtime leaks).protocol (initialLaw setup) horizon
      scheduler).History)
    (forced : ForcedState setup runtime leaks who history.state)
    {control : (application setup runtime leaks).Control} (current : history.state = some control)
    (message : Message Player (WitnessedPacket (graph setup)))
    (pending : message ∈ control.execution.network.pending) :
    (∃ event candidate, message.payload.call = .commitment event candidate ∧
        message.payload.evidence = none) ∨
      ∃ event candidate raw, message.payload.call = .opening event candidate raw ∧
        message.payload.evidence = some ⟨candidate, raw⟩ ∧
        control.execution.application.config.cut.Ready event ∧
        (graph setup).actor? event = some message.sender := by
  let app := application setup runtime leaks
  have trace : (app.protocol (initialLaw setup) horizon scheduler).Trace (some control) :=
    current ▸ (bounds.onePacketMenu runtime leaks).toRawTrace (initialLaw setup) horizon
      scheduler history.trace
  have clean := (bounds.onePacketMenu_countClean runtime leaks scheduler).history
    (initialLaw setup) horizon (fun state _ => runtime.countClean_initial leaks state)
    history.trace
  rw [current] at clean forced
  change runtime.CountClean leaks control.execution at clean
  have facts := settledFacts_history (initialLaw setup) horizon scheduler trace
  have distinct := app.idsDistinct_history scheduler (initialLaw setup) horizon trace
  change control.execution.network.IdsDistinct at distinct
  unfold MessageNetwork.IdsDistinct at distinct
  rw [List.map_append, List.nodup_append] at distinct
  have emitted : Emitted setup leaks control.execution message := facts.carried.pending message
    pending
  obtain ⟨tokenValid, correct, first⟩ :=
    (countPermits_eq_true_iff _ _).mp (clean.2 message emitted)
  unfold CountCallCorrect at correct
  cases call : message.payload.call with
  | malformed raw =>
      rw [call] at correct
      exact correct.elim
  | commitment event candidate =>
      rw [call] at correct
      exact Or.inl ⟨event, candidate, rfl, correct.2.1⟩
  | opening event candidate raw =>
      rw [call] at correct
      obtain ⟨certified, owned⟩ := correct
      obtain ⟨certifiedEvent, certifiedCandidate, certifiedRaw, token, shape⟩ :=
        (certifiedOpening_iff _).mp certified
      rw [shape] at call
      cases call
      have evidence : message.payload.evidence = some ⟨candidate, raw⟩ := by rw [shape]
      cases view : nodeView (graph setup) event with
      | bind _ _ _ _ =>
          rw [view] at owned
          exact owned.elim
      | sample _ _ _ _ =>
          rw [view] at owned
          exact owned.elim
      | resolve owner payload binding checks outputEq codeEq =>
          rw [view] at owned
          have actor : (graph setup).actor? event = some message.sender :=
            (nodeView_resolve_actor outputEq codeEq).trans (congrArg some owned.1.symm)
          obtain ⟨tokenEvent, tokenNamed, tokenEq⟩ :=
            (WitnessedPacket.tokenValid_iff _).mp tokenValid
          rw [shape] at tokenNamed
          cases tokenNamed
          have issued := facts.issued message emitted ⟨event⟩ tokenEq
          have open_ : event ∉ control.execution.application.config.cut.completed := by
            intro completed
            obtain ⟨rank, point, ordered, decoded, forcedPoint⟩ := forced
            rcases completed_packet_or_defaulted (runtime := runtime) trace control rfl
                event completed message.sender actor with accepted | ⟨_inactive, failed⟩
            · obtain ⟨other, onLedger, sameSender, otherNamed⟩ := accepted
              have differentIds : message.id ≠ other.id :=
                distinct.2.2 message.id (List.mem_map_of_mem pending) other.id
                  (List.mem_map_of_mem onLedger)
              have differentSerials : message.id.2 ≠ other.id.2 := by
                intro sameSerial
                apply differentIds
                exact Prod.ext sameSender.symm sameSerial
              have otherEmitted : Emitted setup leaks control.execution other :=
                facts.carried.ledger other onLedger
              obtain ⟨_, _, otherFirst⟩ :=
                (countPermits_eq_true_iff _ _).mp (clean.2 other otherEmitted)
              have messageNamed : message.payload.call.event? (graph setup) = some event := by
                rw [shape]
                rfl
              rcases Nat.lt_or_gt_of_ne differentSerials with lower | upper
              · exact otherFirst message ⟨emitted, sameSender.symm, lower⟩
                  (messageNamed.trans otherNamed.symm)
              · exact first other ⟨otherEmitted, sameSender, upper⟩
                  (otherNamed.trans messageNamed.symm)
            · have publicationFailed := failed payload outputEq
              have readOutput : (outputRef setup.program event).get?
                  control.execution.application.config.store =
                    some (cast (congrArg EventGraph.EventField.Value outputEq.symm)
                      (PublicationResult.failure : PublicationResult (L.Val payload))) := by
                change control.execution.application.config.outputs event = _
                change cast (congrArg Option (congrArg EventGraph.EventField.Value outputEq))
                  (control.execution.application.config.outputs event) = some .failure
                    at publicationFailed
                have castSome {A B : Type} (same : A = B) (value : B) :
                    cast (congrArg Option same) (some (cast same.symm value)) = some value := by
                  cases same
                  rfl
                rw [← castSome (congrArg EventGraph.EventField.Value outputEq) .failure]
                  at publicationFailed
                exact (cast_inj _).mp publicationFailed
              have decodedSource := decoded
              unfold sourceServicePrefix? serviceSourcePrefix? at decodedSource
              have sourceFailed := ProtocolState.revealFailed_of_decode_failure setup.program
                event.val rank (ContextRefs.initial setup.context (outputLayout setup.program)) []
                (Revelations.initial setup.context) (outputRef setup.program) _ _ _ point
                event.isLt ((ordered.2 event).mp completed) message.sender payload outputEq
                decodedSource ((eventOwner?_eq_actor setup.program event).trans actor) readOutput
              by_cases same : message.sender = who
              · exact forcedPoint.1 (same ▸ sourceFailed)
              · have valid := publicationsDefaulted_of_decode history control current ordered
                  decoded
                exact (forcedPoint.2 message.sender same).1
                  (ProtocolState.RevealFailed.excluded setup.program point valid sourceFailed)
          exact Or.inr ⟨event, candidate, raw, rfl, evidence,
            ⟨open_, fun predecessor member => issued predecessor member⟩, actor⟩

end Vegas
