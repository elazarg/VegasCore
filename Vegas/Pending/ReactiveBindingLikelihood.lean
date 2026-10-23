/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.ReactivePolicyMixture
import Vegas.Pending.ReactiveService
import Interaction.ReactiveProvenance
import Vegas.Pending.ReactivePolicyFacts
import Vegas.Pending.ReactiveServiceProgress
import Interaction.ReactiveAllocation
import Vegas.Pending.ReactiveContinuationObservation
import Interaction.ReactiveMessageReadout
import GameTheoryExtensions.Math.Probability.Support

/-! # Actual communication likelihood during an opaque binding window

The auxiliary projection retains the complete network, service recall, and
focal private input. Other players' private submission parameters are absent
from this proof projection. They remain in actual runtime recall. A shared
passive sample couples the silent response windows without an assumption
on the observation rule.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

/-- Existing native fields sufficient for the silent window's joint law.
This is a proof readout; it is not a player's observation or extra state. -/
def bindingTraffic (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (focal : Player) (execution : (runtime.reactiveApplication leaks).Execution) :=
  (execution.network, execution.receipts, execution.environmentRecall, execution.recall focal,
    execution.application.playerView focal, execution.application.publicView)

theorem bindingTraffic_include (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (focal : Player) (left right : (runtime.reactiveApplication leaks).Execution)
    (same : runtime.bindingTraffic leaks focal left = runtime.bindingTraffic leaks focal right)
    (id : MessageId Player) (event : graph.EventId) (candidate : Handle graph)
    (evidence : Option (OpeningFact graph)) (token : Option (ReadinessToken graph))
    (found : left.network.lookup id =
      some ⟨id, ⟨.commitment event candidate, evidence, token⟩⟩) :
    runtime.bindingTraffic leaks focal
        (left.includePending (runtime.reactiveApplication leaks) id) =
      runtime.bindingTraffic leaks focal
        (right.includePending (runtime.reactiveApplication leaks) id) := by
  have networks : left.network = right.network := congrArg Prod.fst same
  have receipts : left.receipts = right.receipts := congrArg (fun value => value.2.1) same
  have environments : left.environmentRecall = right.environmentRecall :=
    congrArg (fun value => value.2.2.1) same
  have recalled : left.recall focal = right.recall focal :=
    congrArg (fun value => value.2.2.2.1) same
  have views : left.application.playerView focal = right.application.playerView focal :=
    congrArg (fun value => value.2.2.2.2.1) same
  have publics : left.application.publicView = right.application.publicView :=
    congrArg (fun value => value.2.2.2.2.2) same
  have rightFound : right.network.lookup id =
      some ⟨id, ⟨.commitment event candidate, evidence, token⟩⟩ := networks ▸ found
  have handled : Option.map (fun state => state.playerView focal)
        ((runtime.reactiveApplication leaks).handle left.application
          ⟨id, ⟨.commitment event candidate, evidence, token⟩⟩) =
      Option.map (fun state => state.playerView focal)
        ((runtime.reactiveApplication leaks).handle right.application
          ⟨id, ⟨.commitment event candidate, evidence, token⟩⟩) := by
    simp only [reactiveApplication_handle]
    split
    · exact handle_commitment_playerView_congr runtime left.application right.application
        focal id event candidate views
    · rfl
  simp only [bindingTraffic, ReactiveApplication.Execution.includePending,
    MessageNetwork.includePending, found, rightFound]
  cases first : (runtime.reactiveApplication leaks).handle left.application
      ⟨id, ⟨.commitment event candidate, evidence, token⟩⟩ with
  | none =>
      cases second : (runtime.reactiveApplication leaks).handle right.application
          ⟨id, ⟨.commitment event candidate, evidence, token⟩⟩ with
      | none =>
          simp only [Option.getD_none, Option.isSome_none]
          exact Prod.ext (by rw [networks]) (Prod.ext (by rw [receipts])
            (Prod.ext environments (Prod.ext recalled (Prod.ext views publics))))
      | some after =>
          simp only [first, second, Option.map_none, Option.map_some] at handled
          contradiction
  | some before =>
      cases second : (runtime.reactiveApplication leaks).handle right.application
          ⟨id, ⟨.commitment event candidate, evidence, token⟩⟩ with
      | none =>
          simp only [first, second, Option.map_none, Option.map_some] at handled
          contradiction
      | some after =>
          simp only [first, second, Option.map_some, Option.some.injEq] at handled
          simp only [Option.getD_some, Option.isSome_some]
          exact Prod.ext (by rw [networks]) (Prod.ext (by rw [receipts])
            (Prod.ext environments (Prod.ext recalled
              (Prod.ext handled (congrArg PlayerView.publicView handled)))))

end Vegas.EventGraphRuntime
