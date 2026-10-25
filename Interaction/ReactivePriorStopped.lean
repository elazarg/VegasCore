/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Interaction.ReactiveResponseStopped

/-! # Stopped state laws under equal initialization measures -/

noncomputable section

namespace Interaction.ReactiveApplication.ResponseMenu

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol

/-- Changing an equal initialization law preserves the complete stopped state distribution. -/
theorem run_until_map_state_prior_eq {Player : Type} [DecidableEq Player] [Fintype Player]
    {app : ReactiveApplication Player} (menu : app.ResponseMenu)
    {first second : PMF app.State} (same : first = second) (horizon : Nat)
    (scheduler : app.Scheduler)
    (firstCertificate : (menu.protocol first horizon scheduler).WellFoundedHistories)
    (secondCertificate : (menu.protocol second horizon scheduler).WellFoundedHistories)
    (profile : ∀ who, (menu.information first horizon scheduler).BehavioralPolicy who)
    (stop : app.ProtocolState → Prop)
    (history : (menu.protocol first horizon scheduler).History) :
    ((menu.information first horizon scheduler).runBehavioralUntil firstCertificate profile
      (fun next => stop next.state) history).map History.state =
      ((menu.information second horizon scheduler).runBehavioralUntil secondCertificate
        (fun who input => (profile who input).map (Equiv.cast (congrArg
          (fun initial => (menu.information initial horizon scheduler).Choice who input) same)))
        (fun next => stop next.state)
        (Equiv.cast (congrArg (fun initial => (menu.protocol initial horizon scheduler).History)
          same) history)).map History.state := by
  subst second
  simp only [Equiv.cast_refl, Equiv.coe_refl, PMF.map_id]
  rfl

end Interaction.ReactiveApplication.ResponseMenu
