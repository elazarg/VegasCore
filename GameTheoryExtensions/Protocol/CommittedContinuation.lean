/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheoryExtensions.Protocol.SequentialChoices

/-! # A current commitment does not change later behavior

When information states do not recur at decisions, fixing the current response
changes only this response. Every continuation after the selected move uses
the original behavioral strategy.
-/

namespace GameTheory.Protocol.InformationModel

open GameTheory.Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι]
  {E : ExecutionProtocol ι} (M : InformationModel E)

open Classical in
theorem runBehavioralFrom_commit_after
    (once : M.ActsOnceWhereItMatters)
    (profile : ∀ who, M.BehavioralPolicy who) (who : ι)
    (info : M.InfoState who) (choice : M.Choice who info)
    (history : E.History) (information : M.infoOf who history.trace = info)
    (active : E.active history.state who)
    {joint : ∀ player, Option (E.Action player)} (legal : E.Legal history.state joint)
    {state : E.State} (realized : state ∈ (E.step history.state ⟨joint, legal⟩).support)
    (fuel : Nat) :
    M.runBehavioralFrom
        (Profile.update (sig := M.behavioralSignature) profile who
          ((profile who).commit info choice)) fuel (history.extend legal realized) =
      M.runBehavioralFrom profile fuel (history.extend legal realized) := by
  apply M.runBehavioralFrom_congr fuel _
  intro later reached nonterminal player
  by_cases same : player = who
  · subst player
    rw [Profile.update_same]
    have equality := M.withLaw_eq_commit_after_actsOnce once (profile who) info
      (profile who info) choice information active legal realized later reached nonterminal
    rw [BehavioralPolicy.withLaw_eq_self] at equality
    exact equality.symm
  · rw [Profile.update_of_ne _ _ same]

open Classical in
/-- After any positive prefix containing the selected move, subsequent play
uses the unchanged profile. This factors actual supported histories as well
as the law of their final states. -/
theorem runBehavioralFrom_commit_split
    (once : M.ActsOnceWhereItMatters)
    (profile : ∀ who, M.BehavioralPolicy who) (who : ι)
    (info : M.InfoState who) (choice : M.Choice who info)
    (history : E.History) (information : M.infoOf who history.trace = info)
    (active : E.active history.state who) (nonterminal : ¬E.terminal history.state)
    (elapsed fuel : Nat) :
    M.runBehavioralFrom
        (Profile.update (sig := M.behavioralSignature) profile who
          ((profile who).commit info choice)) (elapsed + 1 + fuel) history =
      (M.runBehavioralFrom
        (Profile.update (sig := M.behavioralSignature) profile who
          ((profile who).commit info choice)) (elapsed + 1) history).bind
            (M.runBehavioralFrom profile fuel) := by
  rw [show elapsed + 1 + fuel = (elapsed + fuel) + 1 by omega]
  rw [M.runBehavioralFrom_succ_of_not_terminal _ _ nonterminal,
    M.runBehavioralFrom_succ_of_not_terminal _ _ nonterminal, FinDist.bind_bind]
  apply FinDist.bind_congr
  intro joint _
  rw [FinDist.bind_bindOnSupport]
  apply FinDist.bindOnSupport_congr
  intro state realized
  rw [M.runBehavioralFrom_commit_after once profile who info choice history information active
      joint.2 realized (elapsed + fuel),
    M.runBehavioralFrom_commit_after once profile who info choice history information active
      joint.2 realized elapsed,
    M.runBehavioralFrom_add]

end GameTheory.Protocol.InformationModel
