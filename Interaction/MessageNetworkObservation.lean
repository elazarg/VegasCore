module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Interaction.MessageNetwork

@[expose] public section

/-! # Empty pending-observation kernels -/

namespace Interaction.MessageNetwork

variable {Principal Payload : Type}

/-- Every observer and pending pool yields the empty selected-identifier set
with probability one. This is stronger than learning no fresh packet from a
particular pool. -/
def ObservationRule.DeliversNothing (leaks : ObservationRule Principal Payload) : Prop :=
  ∀ who pending, leaks who pending = PMF.pure ∅

end Interaction.MessageNetwork
