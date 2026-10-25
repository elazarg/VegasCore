/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Interaction.MessageNetworkMapOperations

/-! # Payload maps preserve physical pending-message sampling -/

namespace Interaction.MessageNetwork

variable {Principal A B : Type} [DecidableEq Principal]

/-- Learning selected physical identities commutes with every payload map. -/
theorem mapPayload_learn (f : A → B) (network : MessageNetwork Principal A) (who : Principal)
    (selected : Finset (MessageId Principal)) :
    (network.mapPayload f).learn who selected = (network.learn who selected).mapPayload f := by
  unfold learn
  simp only [mapPayload_known, mapPayload_lookup]
  simp only [mapPayload, List.map_map, Function.comp_def, Message.mapPayload, List.any_map]
  congr 1
  funext observer
  split
  · simp only [List.map_append, List.map_filterMap]
  · rfl

end Interaction.MessageNetwork
