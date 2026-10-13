/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheory.Protocol.BehavioralTerminal
import GameTheory.Math.Probability.ExpectationComposition

/-! # Bounding terminal expectations at a stopping set

Terminal behavioral play from a history is a mixture, over the histories one
step later, of terminal play from them. So a bound on the expectation of a
terminal payoff transfers from the first histories of a stopping set that play
reaches to every earlier history, provided the payoff vanishes at the terminal
histories play reaches without stopping
(`GameTheory.Protocol.InformationModel.abs_expect_runBehavioralTerminalFrom_le_of_stopped`).
-/

noncomputable section

namespace GameTheory.Protocol

open GameTheory.Math.Probability

universe uι

variable {ι : Type uι} [Fintype ι] {E : ExecutionProtocol ι}

namespace InformationModel

variable (M : InformationModel E)

/-- One step of play from a nonterminal history reaches only its one-step
extensions, and whatever they reach. -/
theorem mem_support_runBehavioralFrom_one (policies : (i : ι) → M.BehavioralPolicy i)
    {history next : E.History} (running : ¬ E.terminal history.state)
    (member : next ∈ (M.runBehavioralFrom policies 1 history).support) :
    E.HistorySuccessor next history ∧
      ∀ later, E.HistoryReaches next later → E.HistoryReaches history later := by
  rw [M.runBehavioralFrom_succ_of_not_terminal policies 0 running,
    PMF.mem_support_bind_iff] at member
  obtain ⟨draw, _, stepped⟩ := member
  rw [PMF.mem_support_bindOnSupport_iff] at stepped
  obtain ⟨target, realized, reached⟩ := stepped
  change next ∈ (PMF.pure _).support at reached
  rw [PMF.mem_support_pure_iff] at reached
  subst reached
  exact ⟨⟨draw.1, draw.2, realized⟩, fun later reached =>
    ExecutionProtocol.HistoryReaches.step E draw.2 realized reached⟩

/-- **Bounding terminal expectations at a stopping set.** Let `reach` hold at
`start`, outside the stopping set, and pass from every unstopped nonterminal
history it holds at to the unstopped histories one step of play reaches. Suppose
a bounded terminal payoff has expectation at most `ε` in absolute value under
terminal play from every stopped history one step of play reaches from such a
history, and vanishes at every unstopped terminal history `reach` holds at.
Then its expectation under terminal play from `start` is at most `ε` in
absolute value. -/
theorem abs_expect_runBehavioralTerminalFrom_le_of_stopped
    (certificate : E.WellFoundedHistories) (policies : (i : ι) → M.BehavioralPolicy i)
    (reach stopped : E.History → Prop) (payoff : E.History → ℝ) {bound ε : ℝ}
    (bounded : ∀ history, |payoff history| ≤ bound) (nonnegative : 0 ≤ ε)
    (extend : ∀ history next, reach history → ¬ stopped history →
      ¬ E.terminal history.state → next ∈ (M.runBehavioralFrom policies 1 history).support →
      ¬ stopped next → reach next)
    (atStop : ∀ history next, reach history → ¬ stopped history →
      ¬ E.terminal history.state → next ∈ (M.runBehavioralFrom policies 1 history).support →
      stopped next →
      |expect (M.runBehavioralTerminalFrom certificate policies next) payoff| ≤ ε)
    (atEnd : ∀ final, reach final → ¬ stopped final → E.terminal final.state →
      payoff final = 0)
    (start : E.History) (reached : reach start) (running : ¬ stopped start) :
    |expect (M.runBehavioralTerminalFrom certificate policies start) payoff| ≤ ε := by
  classical
  induction start using certificate.induction with
  | _ history ih =>
  by_cases ended : E.terminal history.state
  · change |expect (E.randomizedBackwardLaw certificate (M.randomizedChooser policies) history)
      payoff| ≤ ε
    rw [ExecutionProtocol.randomizedBackwardLaw_of_terminal E ended, expect_pure,
      atEnd history reached running ended, abs_zero]
    exact nonnegative
  rw [M.runBehavioralTerminalFrom_eq_bind_runBehavioralFrom certificate policies 1 history,
    expect_bind_tower_bounded _ _ _ bounded]
  rw [expect_congr_on_support (g := fun next =>
    if next ∈ (M.runBehavioralFrom policies 1 history).support then
      expect (M.runBehavioralTerminalFrom certificate policies next) payoff else 0)
    (fun next member => by rw [ite_eq_left member ..])]
  apply expect_abs_le_of_bounded nonnegative
  intro next
  split
  · rename_i member
    by_cases stop : stopped next
    · exact atStop history next reached running ended member stop
    · exact ih next (M.mem_support_runBehavioralFrom_one policies ended member).1
        (extend history next reached running ended member stop) stop
  · rw [abs_zero]
    exact nonnegative

end InformationModel

end GameTheory.Protocol
