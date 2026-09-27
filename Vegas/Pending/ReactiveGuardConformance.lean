/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveOpeningConformance
import Vegas.EventGraph.Validation

/-! # Public guard checks for transmitted openings

An audit can evaluate disclosure guards from the claimed opening and the
authenticated public store at transmission. It needs neither the hidden
binding nor the source strategy. Acceptance plus certified format and these
public checks identifies exactly a successful compiled disclosure. Authentic
openings whose deferred guards fail are observable departures, even when the
application accepts the call and records publication failure.
-/

noncomputable section

namespace Vegas.EventGraph

variable {Player : Type} {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}

theorem GuardCheck.allAccepted?_publicStore {payload : L.Ty}
    (checks : List (GuardCheck graph.layout payload)) (store : Store graph.layout)
    (proposal : PublicationResult (L.Val payload)) :
    GuardCheck.allAccepted? checks (graph.publicStore store) proposal =
      GuardCheck.allAccepted? checks store proposal := by
  induction checks with
  | nil => rfl
  | cons check rest ih =>
      simp only [GuardCheck.allAccepted?, check.eval?_publicStore store proposal, ih]

end Vegas.EventGraph

namespace Vegas.EventGraphRuntime

open Interaction EventGraph

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

/-- Guard validity is checked on public data and the transmitted value only.
Phase, sender, binding association and authenticity are separate checks. -/
def PublicView.openingGuardsAccepted (view : PublicView graph)
    (packet : WitnessedPacket graph) : Bool :=
  match packet.call with
  | .opening event _ raw =>
      match nodeView graph event with
      | .resolve _ payload _ checks _ _ =>
          (raw.as? payload).any fun value =>
            GuardCheck.allAccepted? checks view.observation.store (.success value) = some true
      | .bind .. | .sample .. => false
  | .commitment .. | .withhold .. | .malformed .. => false

omit [IExpr.ResultTypes L] in
private theorem raw_eq_of_typed (raw : Raw L) (payload : L.Ty) (value : L.Val payload)
    (typed : raw.as? payload = some value) : raw = ⟨payload, value⟩ := by
  rcases raw with ⟨kind, input⟩
  unfold Raw.as? at typed
  split at typed
  · rename_i same
    change kind = payload at same
    subst kind
    cases Option.some.inj typed
    rfl
  · cases typed

omit [DecidableEq Player] in
theorem PublicView.openingGuardsAccepted_iff
    (view : PublicView graph) (owner : Player) (event : graph.EventId) (payload : L.Ty)
    (binding : FieldRef graph.layout (.binding owner payload))
    (checks : List (GuardCheck graph.layout payload))
    (outputEq : graph.outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .resolve owner payload binding checks)
    (node : nodeView graph event = .resolve owner payload binding checks outputEq codeEq)
    (candidate : Handle graph) (raw : Raw L) (evidence : Option (OpeningFact graph)) :
    view.openingGuardsAccepted ⟨.opening event candidate raw, evidence⟩ = true ↔
      ∃ value, raw = ⟨payload, value⟩ ∧
        GuardCheck.allAccepted? checks view.observation.store (.success value) = some true := by
  simp only [openingGuardsAccepted, node]
  constructor
  · intro passes
    cases typed : raw.as? payload with
    | none => simp only [typed, Option.any_none, Bool.false_eq_true] at passes
    | some value =>
        simp only [typed, Option.any_some, decide_eq_true_eq] at passes
        exact ⟨value, raw_eq_of_typed raw payload value typed, passes⟩
  · rintro ⟨value, rfl, accepted⟩
    simp only [Raw.as?_mk, Option.any_some, accepted, decide_true]

/-- Acceptance certifies the hidden binding's value; public guard evaluation
then distinguishes successful disclosure from accepted publication failure. -/
theorem accepted_guarded_opening_normalization
    (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (state next : State graph) (owner : Player) (event : graph.EventId) (payload : L.Ty)
    (binding : FieldRef graph.layout (.binding owner payload))
    (checks : List (GuardCheck graph.layout payload))
    (outputEq : graph.outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .resolve owner payload binding checks)
    (node : nodeView graph event = .resolve owner payload binding checks outputEq codeEq)
    (known : List (Message Player (WitnessedPacket graph)))
    (submission : WitnessedSubmission graph) (serial : Nat)
    (addressed : submission.call.packet.event? graph = some event)
    (certified : certifiedOpening (submission.emit
      ((runtime.reactiveApplication leaks).submit state owner submission) owner known) = true)
    (guards : state.publicView.openingGuardsAccepted (submission.emit
      ((runtime.reactiveApplication leaks).submit state owner submission) owner known) = true)
    (accepted : (runtime.reactiveApplication leaks).handle
      ((runtime.reactiveApplication leaks).submit state owner submission)
      ⟨(owner, serial), submission.emit
        ((runtime.reactiveApplication leaks).submit state owner submission) owner known⟩ =
      some next) :
    ∃ candidate value, state.accepted binding.field = some candidate ∧ candidate.1 = owner ∧
      binding.get? state.config.store = some (.success value) ∧
      EventCode.resolveOutput? binding checks true state.config.store = some (.success value) ∧
      submission.normalizeReactive owner
          ((runtime.reactiveApplication leaks).observePlayer state owner) known =
        (disclosureSubmission (.opening event candidate ⟨payload, value⟩)).normalizeReactive owner
          ((runtime.reactiveApplication leaks).observePlayer state owner) known := by
  obtain ⟨actual, candidate, raw, emitted⟩ := (certifiedOpening_iff _).mp certified
  have call := congrArg WitnessedPacket.call emitted
  change submission.call.packet = .opening actual candidate raw at call
  rw [call] at addressed
  cases Option.some.inj addressed
  rw [emitted] at guards
  obtain ⟨value, rawEq, publicChecks⟩ :=
    (state.publicView.openingGuardsAccepted_iff owner event payload binding checks outputEq codeEq
      node candidate raw (some ⟨candidate, raw⟩)).mp guards
  subst raw
  have unchanged : (runtime.reactiveApplication leaks).submit state owner submission = state := by
    rcases submission with ⟨⟨packet, material⟩, evidence⟩
    dsimp only at call
    subst packet
    cases material <;> rfl
  have applicationAccepted := accepted
  rw [emitted, unchanged] at applicationAccepted
  change handle runtime state ⟨(owner, serial),
    .opening event candidate ⟨payload, value⟩⟩ = some next at applicationAccepted
  have associated : state.accepted binding.field = some candidate := by
    by_contra absent
    simp [handle, node, absent] at applicationAccepted
  have owned : candidate.1 = owner := by
    by_contra foreign
    simp [handle, node, foreign] at applicationAccepted
  have stored : binding.get? state.config.store = some (.success value) := by
    by_contra absent
    simp only [handle, node, dite_eq_ite, Option.dite_none_right_eq_some,
      Option.ite_none_right_eq_some, exists_and_left] at applicationAccepted
    obtain ⟨_, _, _, _, _, _, applied⟩ := applicationAccepted
    split at applied
    · cases applied
    · rename_i other typed
      have same : other = value := by
        simpa only [Raw.as?_mk, Option.some.injEq] using typed.symm
      subst other
      simp only [absent, ↓reduceIte, reduceCtorEq] at applied
  have fixed := runtime.handle_opening_verified state next (owner, serial) event candidate
    ⟨payload, value⟩ applicationAccepted
  have checksAccepted : GuardCheck.allAccepted? checks state.config.store (.success value) =
      some true := by
    change GuardCheck.allAccepted? checks (graph.publicStore state.config.store)
      (.success value) = some true at publicChecks
    rwa [GuardCheck.allAccepted?_publicStore] at publicChecks
  refine ⟨candidate, value, associated, owned, stored, ?_, ?_⟩
  · simp only [EventCode.resolveOutput?, stored, Option.bind_eq_bind, Option.bind_some,
      ↓reduceIte, checksAccepted, Option.pure_def]
  · exact runtime.accepted_certified_opening_normalization leaks state next owner event payload
      binding checks outputEq codeEq node candidate ⟨payload, value⟩ associated owned fixed known
      submission serial (by rw [call]; rfl) certified accepted

/-- Every submitted current-event call is either the successful canonical
disclosure or has concrete rejection, certificate-format, or public-guard
evidence. This applies even when the hidden binding is unusable. -/
theorem current_guarded_submission_cases
    (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (state : State graph) (owner : Player) (event : graph.EventId) (payload : L.Ty)
    (binding : FieldRef graph.layout (.binding owner payload))
    (checks : List (GuardCheck graph.layout payload))
    (outputEq : graph.outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .resolve owner payload binding checks)
    (node : nodeView graph event = .resolve owner payload binding checks outputEq codeEq)
    (known : List (Message Player (WitnessedPacket graph)))
    (submission : WitnessedSubmission graph) (serial : Nat)
    (addressed : submission.call.packet.event? graph = some event) :
    (∃ candidate value, state.accepted binding.field = some candidate ∧ candidate.1 = owner ∧
      binding.get? state.config.store = some (.success value) ∧
      EventCode.resolveOutput? binding checks true state.config.store = some (.success value) ∧
      submission.normalizeReactive owner
          ((runtime.reactiveApplication leaks).observePlayer state owner) known =
        (disclosureSubmission (.opening event candidate ⟨payload, value⟩)).normalizeReactive owner
          ((runtime.reactiveApplication leaks).observePlayer state owner) known) ∨
    (runtime.reactiveApplication leaks).handle
      ((runtime.reactiveApplication leaks).submit state owner submission)
      ⟨(owner, serial), submission.emit
        ((runtime.reactiveApplication leaks).submit state owner submission) owner known⟩ = none ∨
    certifiedOpening (submission.emit
      ((runtime.reactiveApplication leaks).submit state owner submission) owner known) = false ∨
    state.publicView.openingGuardsAccepted (submission.emit
      ((runtime.reactiveApplication leaks).submit state owner submission) owner known) = false := by
  cases certified : certifiedOpening (submission.emit
      ((runtime.reactiveApplication leaks).submit state owner submission) owner known) with
  | false => exact Or.inr (Or.inr (Or.inl rfl))
  | true =>
      cases guards : state.publicView.openingGuardsAccepted (submission.emit
          ((runtime.reactiveApplication leaks).submit state owner submission) owner known) with
      | false => exact Or.inr (Or.inr (Or.inr rfl))
      | true =>
          cases accepted : (runtime.reactiveApplication leaks).handle
              ((runtime.reactiveApplication leaks).submit state owner submission)
              ⟨(owner, serial), submission.emit
                ((runtime.reactiveApplication leaks).submit state owner submission)
                  owner known⟩ with
          | none => exact Or.inr (Or.inl rfl)
          | some next =>
              exact Or.inl (runtime.accepted_guarded_opening_normalization leaks state next owner
                event payload binding checks outputEq codeEq node known submission serial addressed
                  certified guards accepted)

end Vegas.EventGraphRuntime
