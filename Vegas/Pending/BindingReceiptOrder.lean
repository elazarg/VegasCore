/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Pending.PhaseReceiptOrder

/-! # Accepted commitment receipts respect prior owned slots -/

noncomputable section

namespace Vegas.EventGraphRuntime

open EventGraph

variable {Player : Type} {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}

/-- An accepted commitment is active at phase entry and has no earlier owned
omission in that phase. The predicate inspects receipts, not candidate meanings. -/
def BindingReceiptOrder (low : Nat) (inherited : Finset Player)
    (accepted : graph.Field → Option (Handle graph)) : Prop :=
  ∀ event : graph.EventId, ∀ owner : Player, ∀ payload : L.Ty, ∀ candidate : Handle graph,
    low ≤ event.val → graph.outputLayout event = .binding owner payload →
      accepted (.inr event) = some candidate →
        owner ∉ inherited ∧ ∀ prior : graph.EventId, low ≤ prior.val → prior.val < event.val →
          ∀ priorPayload : L.Ty, graph.outputLayout prior = .binding owner priorPayload →
            accepted (.inr prior) ≠ none

namespace BindingReceiptOrder

/-- A saved prefix contains no receipt at a new phase's ranks. -/
theorem of_prefix {low : Nat} {inherited : Finset Player} {native : State graph}
    (receipts : native.ReceiptsComplete) (atPrefix : native.config.cut.IsPrefix low) :
    BindingReceiptOrder low inherited native.accepted := by
  intro event owner payload candidate lower _binding accepted
  have earlier := (atPrefix.2 event).mp (receipts event candidate accepted)
  omega

/-- Exact receipt-table equality preserves the owned-prefix condition. -/
theorem congr {low : Nat} {inherited : Finset Player}
    {before after : graph.Field → Option (Handle graph)}
    (valid : BindingReceiptOrder low inherited before) (same : after = before) :
    BindingReceiptOrder low inherited after := same ▸ valid

/-- Moving the source cursor removes requirements on the slots already consumed. -/
theorem raise_low {low later : Nat} {inherited : Finset Player}
    {accepted : graph.Field → Option (Handle graph)}
    (valid : BindingReceiptOrder low inherited accepted) (advancing : low ≤ later) :
    BindingReceiptOrder later inherited accepted := by
  intro event owner payload candidate lower output installed
  obtain ⟨active, received⟩ := valid event owner payload candidate
    (advancing.trans lower) output installed
  exact ⟨active, fun prior priorLower earlier priorPayload priorOutput =>
    received prior (advancing.trans priorLower) earlier priorPayload priorOutput⟩

/-- A missing current slot excludes its owner from all subsequently received
slots. Earlier accepted slots of that owner are outside the advanced cursor. -/
theorem after_missing [DecidableEq Player] {low : Nat} {inherited : Finset Player}
    {accepted : graph.Field → Option (Handle graph)}
    (valid : BindingReceiptOrder low inherited accepted) (event : graph.EventId)
    (atLow : event.val = low) (owner : Player) (payload : L.Ty)
    (binding : graph.outputLayout event = .binding owner payload)
    (missing : accepted (.inr event) = none) :
    BindingReceiptOrder (low + 1) (insert owner inherited) accepted := by
  intro next actor ty candidate lower output installed
  obtain ⟨active, received⟩ := valid next actor ty candidate (by omega) output installed
  have different : actor ≠ owner := by
    intro same
    subst actor
    exact received event (by omega) (by omega) payload binding missing
  refine ⟨?_, ?_⟩
  · simpa only [Finset.mem_insert, not_or] using And.intro different active
  · intro prior priorLower earlier priorPayload priorOutput
    exact received prior (by omega) earlier priorPayload priorOutput

open scoped Classical in
/-- Installing one active owner's receipt preserves the owned-prefix condition
when readiness has already supplied that owner's preceding receipts. -/
theorem install {low : Nat} {inherited : Finset Player}
    {accepted : graph.Field → Option (Handle graph)}
    (valid : BindingReceiptOrder low inherited accepted) (event : graph.EventId)
    (candidate : Handle graph) (owner : Player) (payload : L.Ty)
    (binding : graph.outputLayout event = .binding owner payload)
    (active : owner ∉ inherited)
    (earlier : ∀ prior : graph.EventId, low ≤ prior.val → prior.val < event.val →
      ∀ priorPayload : L.Ty, graph.outputLayout prior = .binding owner priorPayload →
        accepted (.inr prior) ≠ none) :
    BindingReceiptOrder low inherited
      (Function.update accepted (.inr event) (some candidate)) := by
  have kept : ∀ query : graph.EventId, accepted (.inr query) ≠ none →
      (Function.update accepted (.inr event) (some candidate)) (.inr query) ≠ none := by
    intro query present
    by_cases same : query = event
    · subst query
      rw [Function.update_self]
      exact Option.some_ne_none candidate
    · simpa only [Function.update_of_ne (fun equal => same (Sum.inr.inj equal))] using present
  intro query other ty selected lower output installed
  by_cases same : query = event
  · subst query
    have sameOwner := (EventField.binding.inj (binding.symm.trans output)).1
    subst other
    refine ⟨active, ?_⟩
    intro prior priorLower before priorTy priorOutput
    exact kept prior (earlier prior priorLower before priorTy priorOutput)
  · rw [Function.update_of_ne (fun equal => same (Sum.inr.inj equal))] at installed
    obtain ⟨wasActive, received⟩ := valid query other ty selected lower output installed
    refine ⟨wasActive, ?_⟩
    intro prior priorLower before priorTy priorOutput
    exact kept prior (received prior priorLower before priorTy priorOutput)

end BindingReceiptOrder

end Vegas.EventGraphRuntime
