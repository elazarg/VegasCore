/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.CommitmentCandidates
import Interaction.CommitmentCandidateWeight

namespace InteractionTests.CommitmentCandidates

open Interaction

abbrev Catalog := Interaction.CommitmentCandidates Nat Nat Bool

/-- Distinct prepared handles retain independent openings through acceptance. -/
example :
    let prepared :=
      ((Interaction.CommitmentCandidates.empty : Catalog).prepare 0 4 true).prepare 1 4 false
    let accepted := (prepared.accept (0, 4)).accept (1, 4)
    accepted.verify (0, 4) true = true ∧
      accepted.verify (1, 4) false = true := by
  decide

/-- Acceptance before preparation permanently records an unopenable candidate. -/
example :
    let accepted := (Interaction.CommitmentCandidates.empty : Catalog).accept (2, 7)
    let attempted := accepted.prepare 2 7 true
    attempted.lookup (2, 7) = .unopenable ∧
      attempted.verify (2, 7) true = false := by
  decide

/-- Acceptance of an unprepared handle and an unsuccessful later preparation
introduce no draw factor, even when the tracked factor is zero. -/
example :
    let attempted := ((Interaction.CommitmentCandidates.empty : Catalog).accept (2, 7)).prepare
      2 7 true
    attempted.preparationWeight {(2, 7)} (fun _ => 0) = 1 := by
  simp [Interaction.CommitmentCandidates.preparationWeight,
    Interaction.CommitmentCandidates.lookup_prepare_self,
    Interaction.CommitmentCandidates.lookup_accept_self, CommitmentCandidate.opening?]

/-- Retrying a prepared handle and accepting it do not multiply its factor
again; preparing a distinct tracked handle contributes its own factor. -/
example :
    let prepared := (((Interaction.CommitmentCandidates.empty : Catalog).prepare 0 4 true).prepare
      0 4 false).accept (0, 4)
    (prepared.prepare 1 4 false).preparationWeight {(0, 4), (1, 4)} (fun _ => (1 / 2 : ℝ)) =
      1 / 4 := by
  norm_num [Interaction.CommitmentCandidates.preparationWeight,
    Interaction.CommitmentCandidates.lookup_prepare_self,
    Interaction.CommitmentCandidates.lookup_accept_self,
    Interaction.CommitmentCandidates.lookup_prepare_other,
    Interaction.CommitmentCandidates.lookup_accept_other, CommitmentCandidate.opening?]

end InteractionTests.CommitmentCandidates
