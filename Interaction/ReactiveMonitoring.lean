/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Interaction.ReactivePublication
import Interaction.ReactivePolicyInvariant
import Interaction.MessageMonitoring
import Interaction.ReactiveReceipts
import Interaction.ReactiveMessageReadout
import GameTheory.Math.Probability.Bounds
import GameTheoryExtensions.Math.Probability.Expectation

/-! # Passive observation by a watcher

A watcher is activated, samples pending packets with the passive observation
rule, and transmits nothing. What it observes stays in its private knowledge;
it reaches settlement as the watcher's report, which carries the signed packets
themselves. The service includes nothing on the watcher's behalf.

An observed packet stays observed under every later response and command, so a
sampling bound at one activation is a lower bound on the packet being in the
watcher's report at every later state.
-/

noncomputable section

namespace Interaction.ReactiveApplication

open GameTheory.Math.Probability

variable {Principal : Type} [DecidableEq Principal] (app : ReactiveApplication Principal)

/-- One observation round: the watcher is activated and responds, then the
round's network slot idles. -/
def observationRound (players : Principal → app.Policy) (watcher : Principal)
    (execution : app.Execution) : PMF app.Execution :=
  (app.dispatch players (.activate watcher) execution).bind (app.dispatch players .wait)

private theorem sampled_leaked (execution : app.Execution) (watcher : Principal)
    (id : MessageId Principal) (message : Message Principal app.Payload)
    (found : execution.network.lookup id = some message) (foreign : id.1 ≠ watcher)
    (unknown : (execution.network.known watcher).any (fun packet => packet.id = id) = false)
    (fresh : id ∉ execution.network.ledger.map Message.id)
    (selected : Finset (MessageId Principal)) (chosen : id ∈ selected) :
    message ∈ (execution.sampledActivation app watcher selected).network.leaked watcher := by
  have reported := execution.network.reports_learn_selected (fun _ => true) watcher selected
    id message found foreign chosen unknown rfl
  have seen := ((MessageNetwork.PlayerView.mem_reports ..).mp reported).1
  rcases seen with seen | published
  · exact seen
  · have identified : message.id = id := by
      simpa using (List.find?_eq_some_iff_append.mp found).1
    exact (fresh (List.mem_map.mpr ⟨message, published, identified⟩)).elim

/-- Observed packets stay observed under every later response and command. -/
theorem leaked_policyInvariant (players : Principal → app.Policy) (watcher : Principal)
    (message : Message Principal app.Payload) :
    app.PolicyInvariant players (fun execution => message ∈ execution.network.leaked watcher)
      where
  respond execution who action observed _ := by
    rcases action with ⟨transmission⟩
    cases transmission with
    | none => exact observed
    | some material => exact observed
  environment execution next command observed reached := by
    cases command with
    | wait =>
        simp only [Execution.environmentStep, PMF.pure_map] at reached
        cases (PMF.mem_support_pure_iff _ _).mp reached
        exact observed
    | activate who =>
        rw [Execution.activation_samples, PMF.support_map] at reached
        obtain ⟨selected, _, rfl⟩ := reached
        change message ∈ (execution.network.learn who selected).leaked watcher
        by_cases same : watcher = who
        · subst watcher
          simp only [MessageNetwork.learn, ↓reduceIte, List.mem_append]
          exact Or.inl observed
        · rw [execution.network.learn_other who watcher selected same]
          exact observed
    | «include» id =>
        simp only [Execution.environmentStep, PMF.pure_map] at reached
        cases (PMF.mem_support_pure_iff _ _).mp reached
        change message ∈ (execution.includePending app id).network.leaked watcher
        rw [app.includePending_network]
        unfold MessageNetwork.includePending
        split <;> exact observed
    | application command =>
        obtain ⟨updated, supported, rfl⟩ := PMF.support_map .. ▸ reached
        obtain ⟨state, _, rfl⟩ := PMF.support_map .. ▸ supported
        exact observed

/-- Receipt evidence persists under every subsequent raw response and command. -/
theorem receipt_policyInvariant (players : Principal → app.Policy)
    (receipt : MessageId Principal × Bool) :
    app.PolicyInvariant players (fun execution => receipt ∈ execution.receipts) where
  respond execution who action present _ := by
    rw [app.respond_receipts]
    exact present
  environment execution next command present reached :=
    (app.environmentStep_receipts_prefix execution next command reached).subset present

/-- A passive sample puts a pending foreign packet into the watcher's report
with at least the sampling probability, after the watcher's own response and
arbitrary later responses and scheduling. -/
theorem sampling_observed_lower (players : Principal → app.Policy) (watcher : Principal)
    (execution : app.Execution) (id : MessageId Principal)
    (message : Message Principal app.Payload)
    (found : execution.network.lookup id = some message) (foreign : id.1 ≠ watcher)
    (unknown : (execution.network.known watcher).any (fun packet => packet.id = id) = false)
    (fresh : id ∉ execution.network.ledger.map Message.id)
    (scheduler : app.Scheduler) (count : Nat) :
    ((app.observePending watcher execution.network.pending).toOuterMeasure
      {selected | id ∈ selected}).toReal ≤
      (((app.observationRound players watcher execution).bind
        (app.runRounds scheduler players count)).toOuterMeasure
          {final | message ∈ final.network.leaked watcher}).toReal := by
  classical
  have persistent := app.leaked_policyInvariant players watcher message
  rw [observationRound, dispatch, Execution.activation_samples, PMF.bind_map, PMF.bind_bind,
    PMF.bind_bind, toReal_toOuterMeasure_bind, ← expect_indicator]
  refine expect_mono ?_ (payoffIntegrable_ite_one_zero _ _)
    (payoffIntegrable_toReal_toOuterMeasure _ _ _)
  intro selected _
  rw [← expect_indicator]
  let law := ((app.resume players (Command.actor? app (.activate watcher))
    (execution.sampledActivation app watcher selected)).bind fun observed =>
      (app.dispatch players .wait observed).bind (app.runRounds scheduler players count))
  by_cases chosen : id ∈ selected
  · have seen := app.sampled_leaked execution watcher id message found foreign unknown fresh
      selected chosen
    simp only [Set.mem_ofPred_eq, chosen, ↓reduceIte]
    calc
      (1 : ℝ) = expect law (fun _ => 1) := (expect_constant law 1).symm
      _ ≤ _ := by
        refine expect_mono ?_ (payoffIntegrable_constant _ _) (payoffIntegrable_ite_one_zero _ _)
        intro final reached
        obtain ⟨observed, responded, continued⟩ :=
          Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
        obtain ⟨idle, waited, rest⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ continued)
        have afterResponse := persistent.resume _ _ observed seen responded
        have afterWait := persistent.dispatch .wait observed idle afterResponse waited
        have persists := persistent.runRounds scheduler count idle final afterWait rest
        simp only [persists, ↓reduceIte, le_refl]
  · simp only [Set.mem_ofPred_eq, chosen, ↓reduceIte]
    calc
      (0 : ℝ) = expect law (fun _ => 0) := (expect_constant law 0).symm
      _ ≤ _ := expect_mono (fun _ _ => by split <;> norm_num)
        (payoffIntegrable_constant _ _) (payoffIntegrable_ite_one_zero _ _)

end Interaction.ReactiveApplication
