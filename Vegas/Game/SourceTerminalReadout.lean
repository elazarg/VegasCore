/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.SourceServiceCompletion
import Vegas.Game.RevealServiceRosterContinuation
import GameTheoryExtensions.Analysis.Protocol.StoppedReadout
import GameTheoryExtensions.Protocol.ContinuationHorizon

/-! # Completed native source cuts freeze the typed source readout

The native configuration cannot change once every graph event has completed.
Callbacks, traffic, recall, clocks and receipts may continue changing. The exact
law below concerns the typed source readout and functions of that readout only;
it does not identify complete histories or audit charges.
-/

noncomputable section

namespace Vegas

open SourceProgram GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {setup : Setup (Player := Player) (L := L)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}

/-- Source completion is a predicate on the actual current native cut. -/
def NativeSourceTerminal : (application setup leaks).ProtocolState → Prop
  | none => False
  | some control => control.execution.application.config.cut.Terminal

/-- Every actual native transition after source completion fixes the entire
configuration. This does not require honesty, inclusion, service, or completion
of the scheduler horizon. -/
theorem sourceTerminal_transition {initial : PMF (application setup leaks).State}
    {horizon : Nat} {scheduler : (application setup leaks).Scheduler}
    (control : (application setup leaks).Control)
    (terminal : control.execution.application.config.cut.Terminal)
    (joint : Player → Option (application setup leaks).Action)
    {after : (application setup leaks).ProtocolState}
    (reached : after ∈ ((application setup leaks).transition initial horizon scheduler
      (some control) joint).support) :
    ∃ next : (application setup leaks).Control, after = some next ∧
      next.execution.application.config = control.execution.application.config := by
  rcases control with ⟨remaining, actor, execution⟩
  cases actor with
  | some who =>
      cases (PMF.mem_support_pure_iff _ _).mp reached
      exact ⟨_, rfl, ((runtime setup).reactive_respond_application leaks execution who _).1⟩
  | none =>
      cases remaining with
      | zero =>
          cases (PMF.mem_support_pure_iff _ _).mp reached
          exact ⟨_, rfl, rfl⟩
      | succ remaining =>
          obtain ⟨command, _, moved⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
          obtain ⟨next, stepped, rfl⟩ := PMF.support_map .. ▸ moved
          refine ⟨_, rfl, ?_⟩
          rcases environmentStep_configStep setup leaks execution next command stepped with
            same | ⟨event, ready, action, _member⟩
          · exact same
          · exact (ready.1 (by rw [terminal]; exact Finset.mem_univ event)).elim

variable [Fintype Player]

/-- The native typed readout stays fixed under every continuation profile once
the source cut has completed, even while callbacks and network effects continue. -/
theorem sourceTerminal_readout_stable (menu : (application setup leaks).ResponseMenu)
    (initial : PMF (application setup leaks).State) (horizon : Nat)
    (scheduler : (application setup leaks).Scheduler)
    (certificate : (menu.protocol initial horizon scheduler).WellFoundedHistories)
    (players : ∀ who, (menu.information initial horizon scheduler).BehavioralPolicy who)
    (start : (menu.protocol initial horizon scheduler).History)
    (terminal : NativeSourceTerminal (setup := setup) (leaks := leaks) start.state) :
    ∀ final ∈ ((menu.information initial horizon scheduler).runBehavioralTerminalFrom certificate
        players start).support,
      sourceReadout setup leaks final.state = sourceReadout setup leaks start.state := by
  cases current : start.state with
  | none => simp only [NativeSourceTerminal, current] at terminal
  | some control =>
      simp only [NativeSourceTerminal, current] at terminal
      let closed := fun state : (application setup leaks).ProtocolState =>
        ∃ found : (application setup leaks).Control, state = some found ∧
          found.execution.application.config = control.execution.application.config
      have preserved := InformationModel.runBehavioralTerminalFrom_support_closed
        (menu.information initial horizon scheduler) certificate players closed
        (fun before joint _legal after holds member => by
          obtain ⟨found, rfl, same⟩ := holds
          obtain ⟨next, nextState, nextConfig⟩ := sourceTerminal_transition found
            (initial := initial) (horizon := horizon) (scheduler := scheduler)
            (same.symm ▸ terminal) joint member
          exact ⟨next, nextState, nextConfig.trans same⟩)
        start ⟨control, current, rfl⟩
      intro final member
      obtain ⟨found, finalState, same⟩ := preserved final member
      rw [finalState, sourceReadout_eq_decode, sourceReadout_eq_decode, same]

/-- Stopping at actual source completion preserves the exact terminal law of
the typed readout. Every legal profile is covered; no final-law equality is
assumed, and ancillary histories or receipts are not projected into this law. -/
theorem sourceTerminal_readout_law (menu : (application setup leaks).ResponseMenu)
    (initial : PMF (application setup leaks).State) (horizon : Nat)
    (scheduler : (application setup leaks).Scheduler)
    (certificate : (menu.protocol initial horizon scheduler).WellFoundedHistories)
    (players : ∀ who, (menu.information initial horizon scheduler).BehavioralPolicy who)
    (start : (menu.protocol initial horizon scheduler).History) :
    (((menu.information initial horizon scheduler).runBehavioralTerminalFrom certificate players
        start).map (fun final => sourceReadout setup leaks final.state)) =
      (((menu.information initial horizon scheduler).runBehavioralUntil certificate players
        (fun history => NativeSourceTerminal (setup := setup) (leaks := leaks) history.state)
        start).map (fun final => sourceReadout setup leaks final.state)) := by
  apply InformationModel.runBehavioralTerminalFrom_map_eq_until_of_stable_readout
    (menu.information initial horizon scheduler) certificate players _ _ _ start
  exact sourceTerminal_readout_stable menu initial horizon scheduler certificate players

end Vegas
