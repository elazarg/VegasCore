/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.CommitmentCandidates

namespace InteractionTests.CommitmentCandidates

open Interaction

abbrev Catalog := Interaction.CommitmentCandidates Nat Nat Bool

/-- Distinct prepared handles retain independent openings through acceptance. -/
example :
    let prepared :=
      ((Interaction.CommitmentCandidates.empty : Catalog).prepare 0 4 true).prepare 1 4 false
    let accepted := (prepared.freeze (0, 4)).freeze (1, 4)
    accepted.verify (0, 4) true = true ∧
      accepted.verify (1, 4) false = true := by
  decide

/-- Acceptance before preparation permanently records an unopenable candidate. -/
example :
    let accepted := (Interaction.CommitmentCandidates.empty : Catalog).freeze (2, 7)
    let attempted := accepted.prepare 2 7 true
    attempted.lookup (2, 7) = .unopenable ∧
      attempted.verify (2, 7) true = false := by
  decide

end InteractionTests.CommitmentCandidates
