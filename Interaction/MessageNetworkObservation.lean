module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Interaction.MessageNetwork

@[expose] public section

/-! # Pending-observation kernels -/

namespace Interaction.MessageNetwork

variable {Principal Payload : Type}

/-- Every observer and pending pool yields the empty selected-identifier set
with probability one. This is stronger than learning no fresh packet from a
particular pool. -/
def ObservationRule.DeliversNothing (leaks : ObservationRule Principal Payload) : Prop :=
  ∀ who pending, leaks who pending = PMF.pure ∅

/-- Select every pending identifier. The network learns only fresh foreign messages. -/
noncomputable def ObservationRule.allPending [DecidableEq Principal] :
    ObservationRule Principal Payload :=
  fun _ pending => PMF.pure ((pending.map Message.id).toFinset)

instance [DecidableEq Principal] : ObservationRule.FiniteSupport
    (ObservationRule.allPending (Principal := Principal) (Payload := Payload)) where
  support_finite _ _ := by
    rw [ObservationRule.allPending, PMF.support_pure]
    exact Set.finite_singleton _

end Interaction.MessageNetwork
