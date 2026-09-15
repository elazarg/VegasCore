/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.CommitmentCandidateKnowledge
import Interaction.SealedCandidateResolution
import Interaction.SealedKnowledge
import Interaction.MessageApplicationLaws

/-! # Partial disclosure in the candidate-message host

Related executions have identical public traffic, clocks, events, and
receipts. Catalogs agree only at designated handles; unknown handles may
differ even in whether they can be opened. An authenticated opening may test
only a designated handle. Unauthorized guesses and malformed messages remain
possible and give identical rejection behavior.
-/

noncomputable section

namespace Interaction.SealedProgram

universe uPrincipal uValue

variable {Principal : Type uPrincipal} {Value : Type uValue}
variable [DecidableEq Principal] [DecidableEq Value]

/-- Exact public and designated-private result agreement. In particular,
candidate acceptance does not expose a catalog's hidden openability. -/
theorem candidateMessage?_knowledge
    (program : SealedProgram Principal) (known : CommitmentHandle Principal Nat → Prop)
    (left right : CommitmentCandidates Principal Nat Value)
    (hagrees : ∀ handle, known handle → left.lookup handle = right.lookup handle)
    (events : List (Event Principal Value)) (message : Message Principal (Payload Principal Value))
    (hknown : OpeningKnown known message) :
    (program.candidateMessage? left events message).map
        (fun result => (result.2, fun handle : {h // known h} => result.1.lookup handle.val)) =
      (program.candidateMessage? right events message).map
        (fun result => (result.2, fun handle : {h // known h} => result.1.lookup handle.val)) := by
  have hcatalog : (fun handle : {h // known h} => left.lookup handle.val) =
      (fun handle : {h // known h} => right.lookup handle.val) := by
    funext handle
    exact hagrees handle.val handle.property
  cases message with
  | mk id payload =>
      cases payload with
      | commitment node handle =>
          simp only [candidateMessage?]
          cases hrule : program.rules[node]? with
          | none => rfl
          | some rule =>
              cases hkind : rule.kind <;> simp only [hkind]
              split
              · simp only [Option.map_some]
                congr 2
                funext queried
                exact CommitmentCandidates.accept_lookup_eq_of_known hagrees handle
                  queried.val queried.property
              · rfl
      | opening node handle claimed =>
          by_cases howner : id.1 = handle.1
          · have hvalue := hagrees handle (hknown howner)
            simp only [candidateMessage?, CommitmentCandidates.verify, hvalue]
            cases hrule : program.rules[node]? with
            | none => rfl
            | some rule =>
                cases hkind : rule.kind <;> simp only [hkind]
                split
                · simp only [Option.map_some, hcatalog]
                · rfl
          · rw [program.candidateMessage?_opening_other_owner left events id.1 id.2
              node handle claimed howner,
              program.candidateMessage?_opening_other_owner right events id.1 id.2
                node handle claimed howner]
      | cleartext | malformed => rfl

end Interaction.SealedProgram

namespace Interaction.SealedResolution

open MessageApplication

universe uPrincipal uValue

variable {Principal : Type uPrincipal} {Value : Type uValue}
variable [DecidableEq Principal] [DecidableEq Value]
variable {runtime : SealedResolution Principal Value}

/-- Message admission respects the chosen disclosure boundary. Equal public
state and known candidate meanings give equal rejection or equal visible and
known-private results. Unknown candidates may differ in value or openability. -/
def CandidateHandlerKnowledge
    (applyMessage : ApplicationState Principal Value
      (CommitmentCandidates Principal Nat Value) →
      Message Principal (SealedProgram.Payload Principal Value) →
      Option (ApplicationState Principal Value (CommitmentCandidates Principal Nat Value))) :
    Prop :=
  ∀ (known : CommitmentHandle Principal Nat → Prop)
    (left right : ApplicationState Principal Value (CommitmentCandidates Principal Nat Value)),
    (∀ handle, known handle → left.service.lookup handle = right.service.lookup handle) →
    left.visible = right.visible →
    ∀ message, SealedProgram.OpeningKnown known message →
      (applyMessage left message).map (fun state =>
        (state.visible, fun handle : {h // known h} => state.service.lookup handle.val)) =
      (applyMessage right message).map (fun state =>
        (state.visible, fun handle : {h // known h} => state.service.lookup handle.val))

/-- Candidate-state agreement for a fixed disclosure boundary. The complete
pool is retained, including delivered and pending copies. The carrier is shared
by all candidate hosts; this relation does not depend on their handler. -/
structure CandidateKnowledgeRelated (runtime : SealedResolution Principal Value)
    (known : CommitmentHandle Principal Nat → Prop)
    (left right : runtime.candidateApplication.State) : Prop where
  values : ∀ handle, known handle →
    left.application.service.lookup handle = right.application.service.lookup handle
  publicState : left.application.visible = right.application.visible
  pool : left.pool = right.pool
  receipts : left.receipts = right.receipts
  openings : left.pool.Satisfies (SealedProgram.OpeningKnown known)

variable {known : CommitmentHandle Principal Nat → Prop}
variable {left right : runtime.candidateApplication.State}

theorem CandidateKnowledgeRelated.initial : CandidateKnowledgeRelated runtime known
    (State.initial _ runtime.candidateInitial) (State.initial _ runtime.candidateInitial) :=
  ⟨fun _ _ => rfl, rfl, rfl, rfl, MessagePool.Satisfies.empty⟩

theorem CandidateKnowledgeRelated.observe_eq
    (related : CandidateKnowledgeRelated runtime known left right) (who : Principal) :
    State.observe _ left who = State.observe _ right who := by
  simp only [State.observe, candidateApplication, host,
    related.publicState, related.pool, related.receipts]

theorem CandidateKnowledgeRelated.environmentView_eq
    (related : CandidateKnowledgeRelated runtime known left right) :
    State.environmentView _ left = State.environmentView _ right := by
  simp only [State.environmentView, candidateApplication, host,
    related.publicState, related.pool, related.receipts]

theorem CandidateKnowledgeRelated.prepare
    (related : CandidateKnowledgeRelated runtime known left right)
    (owner : Principal) (slot : Nat) (leftValue rightValue : Value)
    (hvalue : known (owner, slot) → leftValue = rightValue) :
    CandidateKnowledgeRelated runtime known
      { left with application.service := left.application.service.prepare owner slot leftValue }
      { right with application.service :=
        right.application.service.prepare owner slot rightValue } :=
  ⟨CommitmentCandidates.prepare_lookup_eq_of_known related.values owner slot leftValue rightValue
    hvalue, related.publicState, related.pool, related.receipts, related.openings⟩

theorem CandidateKnowledgeRelated.submit
    (related : CandidateKnowledgeRelated runtime known left right)
    (owner : Principal) (payload : SealedProgram.Payload Principal Value)
    (hknown : SealedProgram.OpeningKnown known
      ⟨(owner, left.pool.nextSerial owner), payload⟩) :
    CandidateKnowledgeRelated runtime known
      { left with pool := (left.pool.submit owner payload).2 }
      { right with pool := (right.pool.submit owner payload).2 } :=
  ⟨related.values, related.publicState, by rw [related.pool], related.receipts,
    related.openings.submit owner payload hknown⟩

theorem CandidateKnowledgeRelated.replay
    (related : CandidateKnowledgeRelated runtime known left right)
    (owner : Principal) (id : MessageId Principal) :
    CandidateKnowledgeRelated runtime known
      { left with pool := (left.pool.replay owner id).state }
      { right with pool := (right.pool.replay owner id).state } :=
  ⟨related.values, related.publicState, by rw [related.pool], related.receipts,
    related.openings.replay owner id⟩

theorem CandidateKnowledgeRelated.deliver
    (related : CandidateKnowledgeRelated runtime known left right)
    (owner : Principal) (id : MessageId Principal) :
    CandidateKnowledgeRelated runtime known
      { left with pool := (left.pool.deliver owner id).state }
      { right with pool := (right.pool.deliver owner id).state } :=
  ⟨related.values, related.publicState, by rw [related.pool], related.receipts,
    related.openings.deliver owner id⟩

theorem CandidateKnowledgeRelated.tick
    (related : CandidateKnowledgeRelated runtime known left right) :
    CandidateKnowledgeRelated runtime known
      { left with application := runtime.tick left.application }
      { right with application := runtime.tick right.application } :=
  ⟨related.values, by simp only [SealedResolution.tick, related.publicState],
    related.pool, related.receipts, related.openings⟩

/-- The resolving handler preserves public and designated-private agreement,
including all rejection receipts and timeout-dependent eligibility tests. -/
theorem candidateHandle_knowledge (runtime : SealedResolution Principal Value) :
    CandidateHandlerKnowledge runtime.candidateHandle := by
  intro known left right hvalues hpublic message hknown
  simp only [candidateHandle, hpublic]
  split
  · rfl
  · have hmessage := SealedProgram.candidateMessage?_knowledge
      (runtime.program.discharge right.visible.timeouts)
      known left.service right.service hvalues right.visible.events message hknown
    have hmapped := congrArg (Option.map fun result =>
      (runtime.refresh false { right.visible with
        events := right.visible.events ++ [result.1] }, result.2)) hmessage
    simpa only [Option.map_map, Function.comp_def, Option.bind_eq_bind, Option.map_bind,
      Option.map_some, Option.map_eq_bind, Option.bind_assoc, Option.bind_some] using hmapped

theorem CandidateKnowledgeRelated.includePending
    (related : CandidateKnowledgeRelated runtime known left right)
    {applyMessage : ApplicationState Principal Value
      (CommitmentCandidates Principal Nat Value) →
      Message Principal (SealedProgram.Payload Principal Value) →
      Option (ApplicationState Principal Value (CommitmentCandidates Principal Nat Value))}
    (hknowledge : CandidateHandlerKnowledge applyMessage) (id : MessageId Principal) :
    let app := runtime.candidateHost applyMessage
    CandidateKnowledgeRelated runtime known
      (app.includePending left id) (app.includePending right id) := by
  intro app
  cases hlookup : left.pool.lookup id with
  | none =>
      rw [app.includePending_missing left id hlookup,
        app.includePending_missing right id
          (related.pool ▸ hlookup)]
      exact related
  | some message =>
      have hknown := related.openings.1 message (List.mem_of_find?_eq_some hlookup)
      have hhandler := hknowledge known left.application right.application
        related.values related.publicState message hknown
      cases hl : applyMessage left.application message with
      | none =>
          have hr : applyMessage right.application message = none := by
            cases hr : applyMessage right.application message with
            | none => rfl
            | some result =>
                simp only [hl, hr, Option.map_none, Option.map_some] at hhandler
                contradiction
          rw [app.includePending_reject left id message hlookup hl,
            app.includePending_reject right id message
              (related.pool ▸ hlookup) hr]
          exact ⟨related.values, related.publicState, by rw [related.pool],
            by rw [related.receipts], related.openings.includePending id⟩
      | some nextLeft =>
          cases hr : applyMessage right.application message with
          | none =>
              simp only [hl, hr, Option.map_none, Option.map_some] at hhandler
              contradiction
          | some nextRight =>
              simp only [hl, hr, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hhandler
              rw [app.includePending_accept left id message nextLeft
                hlookup hl, app.includePending_accept right id message
                  nextRight (related.pool ▸ hlookup) hr]
              exact ⟨fun handle hknown => congrFun hhandler.2 ⟨handle, hknown⟩,
                hhandler.1, by rw [related.pool], by rw [related.receipts],
                related.openings.includePending id⟩

end Interaction.SealedResolution
