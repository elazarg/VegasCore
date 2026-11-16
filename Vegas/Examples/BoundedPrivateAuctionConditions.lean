module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Examples.BoundedPrivateValueAuction
public import Vegas.Game.ClientSpecification

@[expose] public section

noncomputable section

namespace Vegas.Examples.BoundedPrivateValueAuction

open SourceProgram EventGraphRuntime GameTheory GameTheory.Math.Probability
open CommitRevealAuction (Player)

abbrev graph := (setup uniformPrior).informationGraph

def bounds : MessageBounds graph where
  candidateCount := 2
  values := Finset.univ.image fun value : Bid => (⟨.range 0 6, value⟩ : Raw simpleExpr)

theorem outputValues : bounds.CoversOutputValues := by
  intro event
  fin_cases event <;> intro value <;> exact Finset.mem_image.mpr ⟨value, Finset.mem_univ _, rfl⟩

theorem inputValues : bounds.CoversInputValues := by
  intro input
  fin_cases input <;> intro owner payload impossible <;> cases impossible

theorem candidateCapacity : ∀ who, bindingEventCount graph who < bounds.candidateCount := by
  intro who
  cases who <;> decide

end Vegas.Examples.BoundedPrivateValueAuction
