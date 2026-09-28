/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.RevealServiceWatcher
import GameTheoryExtensions.Analysis.FinitePayoffBounds

/-! # All-player deposit bounds for terminal traffic audits

The bounds range over every legal effective native history, including arbitrary
owner and watcher responses. No player is assigned zero utility or exempted
from the deposit. The retained game embeds into this same carrier, so its
continuations satisfy the lower bound as well.

These real-valued extrema are a mathematical certificate fixed before choosing
an equilibrium. A positive conditional collection rate remains a separate
assumption about the actual audit and collection service.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
open Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
  (bounds : MessageBounds (graph setup)) (watcher : Player)
  (base : (application setup leaks).ProtocolState → Player → ℝ)

local instance : Nonempty ((bounds.menu (runtime setup) leaks).protocol
    (initialLaw setup) (horizon setup watcher) (scheduler setup leaks watcher)).History :=
  ⟨((bounds.menu (runtime setup) leaks).protocol (initialLaw setup) (horizon setup watcher)
    (scheduler setup leaks watcher)).initHistory⟩

open Classical in
def auditPayoffLower (who : Player) : ℝ :=
  FinitePayoffBounds.lower (fun history : ((bounds.menu (runtime setup) leaks).protocol
    (initialLaw setup) (horizon setup watcher) (scheduler setup leaks watcher)).History =>
      base history.state who)

open Classical in
def auditPayoffUpper (who : Player) : ℝ :=
  FinitePayoffBounds.upper (fun history : ((bounds.menu (runtime setup) leaks).protocol
    (initialLaw setup) (horizon setup watcher) (scheduler setup leaks watcher)).History =>
      base history.state who)

theorem auditPayoffLower_le
    (history : ((bounds.menu (runtime setup) leaks).protocol
      (initialLaw setup) (horizon setup watcher) (scheduler setup leaks watcher)).History)
    (who : Player) :
    auditPayoffLower setup leaks bounds watcher base who ≤ base history.state who := by
  classical
  exact FinitePayoffBounds.lower_le (Value := ℝ) _ history

theorem le_auditPayoffUpper
    (history : ((bounds.menu (runtime setup) leaks).protocol
      (initialLaw setup) (horizon setup watcher) (scheduler setup leaks watcher)).History)
    (who : Player) :
    base history.state who ≤ auditPayoffUpper setup leaks bounds watcher base who := by
  classical
  exact FinitePayoffBounds.le_upper (fun next => base next.state who) history

/-- Every retained legal continuation lies in the same bounded native carrier. -/
theorem retained_auditPayoffLower_le
    (history : (protocol setup leaks bounds watcher).History) (who : Player) :
    auditPayoffLower setup leaks bounds watcher base who ≤ base history.state who := by
  let restriction := (menu_in_effective setup leaks bounds watcher).actionRestriction
    (initialLaw setup) (horizon setup watcher) (scheduler setup leaks watcher)
  exact auditPayoffLower_le setup leaks bounds watcher base (restriction.history history) who

theorem auditPayoffLower_le_upper (who : Player) :
    auditPayoffLower setup leaks bounds watcher base who ≤
      auditPayoffUpper setup leaks bounds watcher base who := by
  classical
  exact FinitePayoffBounds.lower_le_upper (Value := ℝ) _

/-- Every player posts the same range/rate form, including the watcher. -/
def auditRangeDeposit (probability : Player → ℝ) (who : Player) : ℝ :=
  (auditPayoffUpper setup leaks bounds watcher base who -
    auditPayoffLower setup leaks bounds watcher base who) / probability who

theorem auditRangeDeposit_nonnegative (probability : Player → ℝ)
    (positive : ∀ who, 0 < probability who) (who : Player) :
    0 ≤ auditRangeDeposit setup leaks bounds watcher base probability who :=
  div_nonneg (sub_nonneg.mpr (auditPayoffLower_le_upper setup leaks bounds watcher base who))
    (positive who).le

/-- The conditional expected collectible loss covers every base-payoff range. -/
theorem auditRangeDeposit_sufficient (probability : Player → ℝ)
    (positive : ∀ who, 0 < probability who) (who : Player) :
    auditPayoffUpper setup leaks bounds watcher base who -
        auditPayoffLower setup leaks bounds watcher base who ≤
      probability who * auditRangeDeposit setup leaks bounds watcher base probability who := by
  rw [auditRangeDeposit, mul_div_cancel₀ _ (positive who).ne']

end Vegas
