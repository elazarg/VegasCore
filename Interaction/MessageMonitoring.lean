/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Interaction.MessageNetwork

/-! # Report material in an ordinary network observation

A packet checker can inspect leaked packets and the ledger using the same view
available to a player. Reports retain the offending envelopes; they do not add
access to the input log or delivery timestamps.
Sampling probability, report delivery, and the soundness of an application's
violation predicate are separate obligations.
-/

namespace Interaction.MessageNetwork

variable {Principal Payload : Type}

namespace PlayerView

/-- Potential report material drawn only from the observer's retained packets. -/
def reports (violation : Message Principal Payload → Bool)
    (view : PlayerView Principal Payload) : List (Message Principal Payload) :=
  (view.leaked ++ view.ledger).filter violation

@[simp] theorem mem_reports (violation : Message Principal Payload → Bool)
    (view : PlayerView Principal Payload) (message : Message Principal Payload) :
    message ∈ view.reports violation ↔
      (message ∈ view.leaked ∨ message ∈ view.ledger) ∧ violation message = true := by
  simp only [reports, List.mem_filter, List.mem_append]

end PlayerView

variable [DecidableEq Principal]

/-- A selected, previously unknown foreign pending packet becomes report
material when it satisfies the checker. Selection itself is an assumption. -/
theorem reports_learn_selected (network : MessageNetwork Principal Payload)
    (violation : Message Principal Payload → Bool) (who : Principal)
    (selected : Finset (MessageId Principal)) (id : MessageId Principal)
    (message : Message Principal Payload)
    (found : network.lookup id = some message) (foreign : id.1 ≠ who)
    (chosen : id ∈ selected)
    (unknown : (network.known who).any (fun packet => packet.id = id) = false)
    (offending : violation message = true) :
    message ∈ ((network.learn who selected).observe who).reports violation := by
  apply (PlayerView.mem_reports ..).mpr
  refine ⟨Or.inl ?_, offending⟩
  simp only [observe, learn, ↓reduceIte]
  apply List.mem_append_right
  apply List.mem_filterMap.mpr
  refine ⟨id, ?_, found⟩
  apply List.mem_filter.mpr
  refine ⟨?_, by simp [foreign, chosen, unknown]⟩
  have identified : message.id = id := by
    simpa using (List.find?_eq_some_iff_append.mp found).1
  simp only [List.mem_eraseDups, List.mem_map]
  exact ⟨message, List.mem_of_find?_eq_some found, identified⟩

end Interaction.MessageNetwork
