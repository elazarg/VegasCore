/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.MessageNetwork
import GameTheory.Math.Probability.ConditionalObservation
import GameTheory.Math.Probability.ExpectationConditioning
import GameTheoryExtensions.Math.Probability.Expectation
import GameTheoryExtensions.Math.Probability.Uniform
import GameTheoryExtensions.Math.Probability.Support

/-! # Inclusion proposals sampled over distinct pending identifiers

The eligibility predicate identifies the application event and author whose
proposals compete. Selection consults only the current pending packets.
Adding an eligible fresh identifier scales every retained candidate equally.

This is an inclusion rule for investigating continuation preservation. It is
not installed in the reserved service, and supplies neither service liveness
nor the correspondence between native and source subgames.
-/

noncomputable section

namespace Interaction.MessageNetwork

open GameTheory.Math.Probability

variable {Principal Payload : Type} [DecidableEq Principal]

def chooseUniform (candidates : Finset (MessageId Principal)) :
    PMF (Option (MessageId Principal)) :=
  if nonempty : candidates.Nonempty then (PMF.uniformOfFinset candidates nonempty).map some
  else PMF.pure none

omit [DecidableEq Principal] in
theorem chooseUniform_supported (candidates : Finset (MessageId Principal))
    (id : MessageId Principal) (supported : some id ∈ (chooseUniform candidates).support) :
    id ∈ candidates := by
  unfold chooseUniform at supported
  split at supported
  · rename_i nonempty
    obtain ⟨selected, member, same⟩ := PMF.support_map .. ▸ supported
    cases Option.some.inj same
    exact (PMF.mem_support_uniformOfFinset_iff nonempty id).mp member
  · cases (PMF.mem_support_pure_iff _ _).mp supported

omit [DecidableEq Principal] in
theorem chooseUniform_support_finite (candidates : Finset (MessageId Principal)) :
    (chooseUniform candidates).support.Finite := by
  refine ((Set.finite_singleton none).union
    ((Finset.finite_toSet candidates).image some)).subset ?_
  intro selected supported
  cases selected with
  | none => exact Or.inl rfl
  | some id => exact Or.inr ⟨id, chooseUniform_supported candidates id supported, rfl⟩

end Interaction.MessageNetwork
