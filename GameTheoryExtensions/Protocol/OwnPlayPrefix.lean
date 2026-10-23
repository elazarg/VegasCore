/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import GameTheory.Protocol.Information
import GameTheoryExtensions.Protocol.TracePrefix

/-! # Actual prefix witnesses for recorded own actions -/

namespace GameTheory.Protocol.InformationModel

open ExecutionProtocol

variable {ι : Type*} {E : ExecutionProtocol ι} {M : InformationModel E} {who : ι}

/-- Every recorded own action was selected at an actual prefix of the same
history. The witness retains both the decision information and its realized
transition, rather than only the existence of a matching information site. -/
theorem exists_tracePrefix_of_mem_ownPlay {state : E.State} (trace : E.Trace state)
    {recorded : M.InfoState who × E.Action who} (member : recorded ∈ M.ownPlay who trace) :
    ∃ (before after : E.State) (prior : E.Trace before) (joint : ∀ player, Option (E.Action player))
      (legal : E.Legal before joint) (realized : after ∈ (E.step before ⟨joint, legal⟩).support),
      TracePrefix (prior.extend joint legal realized) trace ∧
        M.infoOf who prior = recorded.1 ∧ joint who = some recorded.2 := by
  induction trace with
  | start => simp only [InfoSignals.ownPlay, List.not_mem_nil] at member
  | @extend source target prior joint legal realized ih =>
      cases acted : joint who with
      | none =>
          simp only [InfoSignals.ownPlay, acted] at member
          obtain ⟨before, after, earlier, choices, permitted, reached, isEarlier, info, selected⟩ :=
            ih member
          exact ⟨before, after, earlier, choices, permitted, reached,
            .extend isEarlier joint legal realized, info, selected⟩
      | some action =>
          simp only [InfoSignals.ownPlay, acted, List.mem_cons] at member
          rcases member with same | previous
          · subst recorded
            exact ⟨source, target, prior, joint, legal, realized, .refl, rfl, acted⟩
          · obtain ⟨before, after, earlier, choices, permitted, reached, isEarlier, info,
                selected⟩ := ih previous
            exact ⟨before, after, earlier, choices, permitted, reached,
              .extend isEarlier joint legal realized, info, selected⟩

end GameTheory.Protocol.InformationModel
