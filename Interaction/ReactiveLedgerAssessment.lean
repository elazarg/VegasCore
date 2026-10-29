/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Interaction.ReactiveLedgerRealization
import Interaction.ReactiveResponseEvaluation
import Interaction.ReactiveRestrictedContinuation

/-! # Uniform ledger-client realization of bounded behavioral profiles

Every finite-menu behavioral profile has the same physical continuation law
as its decoded ledger clients when the application delivers no pending data.
Agreement holds at every legal history, including opponents' deviations.
The translation is independent of game syntax and utilities.
-/

noncomputable section

namespace Interaction.ReactiveApplication.ResponseMenu

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Principal : Type} [DecidableEq Principal] {app : ReactiveApplication Principal}
  (menu : app.ResponseMenu) (initial : PMF app.State) (horizon : Nat) (scheduler : app.Scheduler)

/-- Decode all response laws and erase pending observations throughout recall. -/
def ledgerProfile
    (profile : ∀ who, (menu.information initial horizon scheduler).BehavioralPolicy who) :
    Principal → app.Policy := fun who =>
  app.ledgerPolicy (menu.decodeProfile initial horizon scheduler profile who)

/-- The translated policy ignores pending observations throughout its recall. -/
theorem ledgerProfile_usesLedgerOnly
    (profile : ∀ who, (menu.information initial horizon scheduler).BehavioralPolicy who)
    (who : Principal) : Policy.UsesLedgerOnly app
      (menu.ledgerProfile initial horizon scheduler profile who) :=
  app.ledgerPolicy_usesLedgerOnly _

variable (unobserved : app.observePending.DeliversNothing)

include unobserved

/-- Ledger and decoded callbacks agree at every initialized raw history. -/
theorem ledgerProfile_agrees
    (profile : ∀ who, (menu.information initial horizon scheduler).BehavioralPolicy who)
    (control : app.Control)
    (trace : (app.protocol initial horizon scheduler).Trace (some control)) (who : Principal) :
    menu.ledgerProfile initial horizon scheduler profile who
      (control.execution.recall who) (control.execution.observe app who) =
    menu.decodeProfile initial horizon scheduler profile who
      (control.execution.recall who) (control.execution.observe app who) :=
  app.ledgerPolicy_eq_at_history unobserved initial horizon scheduler control trace who _

/-- Restricting ledger callbacks recovers the profile at every bounded-menu decision. -/
theorem restrict_ledgerProfile_history
    (profile : ∀ who, (menu.information initial horizon scheduler).BehavioralPolicy who)
    (history : (menu.protocol initial horizon scheduler).History) (who : Principal) :
    menu.restrictPolicy initial horizon scheduler who
      (menu.ledgerProfile initial horizon scheduler profile who)
      ((menu.information initial horizon scheduler).infoOf who history.trace) =
    profile who ((menu.information initial horizon scheduler).infoOf who history.trace) := by
  suffices pointwise : ∀ info : app.Info, info = app.observe who history.state →
      menu.restrictPolicy initial horizon scheduler who
        (menu.ledgerProfile initial horizon scheduler profile who) info = profile who info by
    exact pointwise _ (menu.info initial horizon scheduler who history.trace)
  intro info observed
  have decoded := congrFun
    (menu.restrict_decode_embedPolicy initial horizon scheduler who (profile who))
  cases info with
  | none => exact decoded none
  | some data =>
      rcases history with ⟨state, trace⟩
      cases state with
      | none => cases observed
      | some control =>
          change some data = (if control.actor = some who then
            some (control.execution.recall who, control.execution.observe app who) else none)
            at observed
          split at observed
          · cases Option.some.inj observed
            rw [menu.restrictPolicy_congr_at initial horizon scheduler who _ _ _ _
              (menu.ledgerProfile_agrees initial horizon scheduler unobserved profile control
                (menu.toRawTrace initial horizon scheduler trace) who)]
            exact decoded (some (control.execution.recall who, control.execution.observe app who))
          · cases observed

/-- Ledger callbacks stay within the menu at every legal bounded-menu decision. -/
theorem ledgerProfile_admissible
    (profile : ∀ who, (menu.information initial horizon scheduler).BehavioralPolicy who)
    (who : Principal) :
    menu.Admissible initial horizon scheduler who
      (menu.ledgerProfile initial horizon scheduler profile who) := by
  intro control trace _active response supported
  rw [menu.ledgerProfile_agrees initial horizon scheduler unobserved profile control
    (menu.toRawTrace initial horizon scheduler trace) who] at supported
  exact menu.decode_embedPolicy_covered initial horizon scheduler who (profile who) _ _ _ supported

variable [Fintype Principal]

/-- The actual ledger clients realize every complete behavioral continuation. -/
theorem run_ledgerProfile_eq_finish
    (profile : ∀ who, (menu.information initial horizon scheduler).BehavioralPolicy who)
    (fuel : Nat) (history : (menu.protocol initial horizon scheduler).History)
    (enough : app.rank horizon history.state ≤ fuel) :
    ((menu.information initial horizon scheduler).runBehavioralFrom profile fuel history).map
        History.state =
      app.finish initial horizon scheduler
        (menu.ledgerProfile initial horizon scheduler profile) history.state := by
  have same := (menu.information initial horizon scheduler).runBehavioralFrom_congr
    (first := fun who => menu.restrictPolicy initial horizon scheduler who
      (menu.ledgerProfile initial horizon scheduler profile who))
    (second := profile) fuel history
    (fun later _ _ who =>
      menu.restrict_ledgerProfile_history initial horizon scheduler unobserved profile later who)
  rw [← same]
  exact menu.run_restrict_eq_finish initial horizon scheduler _
    (menu.ledgerProfile_admissible initial horizon scheduler unobserved profile) fuel history enough

end Interaction.ReactiveApplication.ResponseMenu
