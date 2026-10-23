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
  | .commitment .. | .malformed .. => false

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
    (candidate : Handle graph) (raw : Raw L) (evidence : Option (OpeningFact graph))
    {token : Option (ReadinessToken graph)} :
    view.openingGuardsAccepted ⟨.opening event candidate raw, evidence, token⟩ = true ↔
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

end Vegas.EventGraphRuntime
