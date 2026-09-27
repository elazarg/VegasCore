/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.RevealServiceWatcher
import GameTheoryExtensions.Analysis.FinitePayoffBounds

/-! # Fixed deposits from the actual bounded backend's payoff range

The carrier used for the extrema is the finite set of all legal watched-game
histories, including every off-path continuation. The ambient source state and
native packet carriers need not be finite. Bounds and deposits therefore depend
only on the chosen game, utility and observation coverage, before choosing any
source equilibrium.

These real-valued extrema give a mathematical synthesis certificate. They are
not claimed to be an executable optimizer for arbitrary real-valued utilities,
nor to give the least deposit for the actual incentive comparisons.
-/

noncomputable section

namespace Vegas.SourceProgram.RevealService

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
open GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
  (bounds : MessageBounds (graph setup)) (watcher : Player)
  (base : (application setup leaks).ProtocolState → Player → ℝ)

local instance : Nonempty ((watchedMenu setup leaks bounds watcher).protocol
    (initialLaw setup) (horizon setup watcher) (scheduler setup leaks watcher)).History :=
  ⟨((watchedMenu setup leaks bounds watcher).protocol (initialLaw setup) (horizon setup watcher)
    (scheduler setup leaks watcher)).initHistory⟩

open Classical in
def historyPayoffLower (who : Player) : ℝ :=
  FinitePayoffBounds.lower (fun history : ((watchedMenu setup leaks bounds watcher).protocol
    (initialLaw setup) (horizon setup watcher) (scheduler setup leaks watcher)).History =>
      base history.state who)

open Classical in
def historyPayoffUpper (who : Player) : ℝ :=
  FinitePayoffBounds.upper (fun history : ((watchedMenu setup leaks bounds watcher).protocol
    (initialLaw setup) (horizon setup watcher) (scheduler setup leaks watcher)).History =>
      base history.state who)

theorem historyPayoffLower_le
    (history : ((watchedMenu setup leaks bounds watcher).protocol
      (initialLaw setup) (horizon setup watcher) (scheduler setup leaks watcher)).History)
    (who : Player) :
    historyPayoffLower setup leaks bounds watcher base who ≤ base history.state who := by
  classical
  exact FinitePayoffBounds.lower_le (Value := ℝ) _ history

theorem le_historyPayoffUpper
    (history : ((watchedMenu setup leaks bounds watcher).protocol
      (initialLaw setup) (horizon setup watcher) (scheduler setup leaks watcher)).History)
    (who : Player) :
    base history.state who ≤ historyPayoffUpper setup leaks bounds watcher base who := by
  classical
  exact FinitePayoffBounds.le_upper (fun next => base next.state who) history

/-- Every retained history is an actual watched history with unchanged state. -/
theorem retained_historyPayoffLower_le
    (history : (protocol setup leaks bounds watcher).History) (who : Player) :
    historyPayoffLower setup leaks bounds watcher base who ≤ base history.state who :=
  historyPayoffLower_le setup leaks bounds watcher base
    ((ordinaryRestriction setup leaks bounds watcher).history history) who

theorem historyPayoffLower_le_upper (who : Player) :
    historyPayoffLower setup leaks bounds watcher base who ≤
      historyPayoffUpper setup leaks bounds watcher base who := by
  classical
  exact FinitePayoffBounds.lower_le_upper (Value := ℝ) _

open Classical in
/-- One deposit per ordinary player; the reporting player posts none. -/
def rangeDeposit (probability : Player → ℝ) (who : Player) : ℝ :=
  if who = watcher then 0 else
    (historyPayoffUpper setup leaks bounds watcher base who -
      historyPayoffLower setup leaks bounds watcher base who) / probability who

theorem rangeDeposit_watcher (probability : Player → ℝ) :
    rangeDeposit setup leaks bounds watcher base probability watcher = 0 := by
  simp only [rangeDeposit, ↓reduceIte]

theorem rangeDeposit_nonnegative (probability : Player → ℝ)
    (positive : ∀ who, who ≠ watcher → 0 < probability who) (who : Player) :
    0 ≤ rangeDeposit setup leaks bounds watcher base probability who := by
  unfold rangeDeposit
  split
  · exact le_rfl
  · rename_i ordinary
    exact div_nonneg (sub_nonneg.mpr
      (historyPayoffLower_le_upper setup leaks bounds watcher base who))
        (positive who ordinary).le

/-- Equality at the threshold suffices for non-strict sequential optimality.
The input rate must bound actual additional collection for the deviation. -/
theorem rangeDeposit_sufficient (probability : Player → ℝ)
    (positive : ∀ who, who ≠ watcher → 0 < probability who)
    (who : Player) (ordinary : who ≠ watcher) :
    historyPayoffUpper setup leaks bounds watcher base who -
        historyPayoffLower setup leaks bounds watcher base who ≤
      probability who * rangeDeposit setup leaks bounds watcher base probability who := by
  rw [rangeDeposit, ite_eq_right ordinary,
    mul_div_cancel₀ _ (positive who ordinary).ne']

end Vegas.SourceProgram.RevealService
