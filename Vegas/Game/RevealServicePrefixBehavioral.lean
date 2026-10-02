/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.RevealServiceFocalLaw
import Vegas.Game.RevealServicePrefixHistory

/-! # Prefix correspondence for the actual native behavioral game

Both sides below are the standard history runners. The readout forgets native
service progress and retains the complete existing source protocol state.
Different physical alias histories remain different native histories.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
open GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]

/-- Read the existing source position at a fixed public event rank. The
uninitialized native position maps to the uninitialized source position. -/
def prefixReadout (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (count : Nat) : (application setup leaks).ProtocolState → setup.ProtocolState
  | none => none
  | some control => sourcePrefix? setup count control.execution.application.config

/-- Forgetting native control at a service boundary exposes its actual prefix
execution. The equality holds for every menu and every behavioral profile. -/
theorem menu_prefix_readout (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (responses : (application setup leaks).ResponseMenu) (watcher : Player)
    (reveals : setup.program.RevealOnly)
    (profile : Profile (responses.information (initialLaw setup) (horizon setup watcher)
      (scheduler setup leaks watcher)).behavioralSignature)
    (count : Nat) (within : count ≤ (graph setup).order.eventCount) :
    ((responses.information (initialLaw setup) (horizon setup watcher)
      (scheduler setup leaks watcher)).runBehavioral profile
        (blockOffset count + 2 * count + 1)).map
          (fun history => prefixReadout setup leaks count history.state) =
      ((initialLaw setup).bind fun state =>
        (runtime setup).runInteractionPlan leaks
          (responses.decodeProfile (initialLaw setup) (horizon setup watcher)
            (scheduler setup leaks watcher) profile)
          ((runtime setup).idleNetwork leaks) (planPrefix setup watcher count)
          (ReactiveApplication.Execution.initial (application setup leaks) state)).map
            (fun final => sourcePrefix? setup count final.application.config) := by
  change ((responses.information (initialLaw setup) (horizon setup watcher)
    (scheduler setup leaks watcher)).runBehavioral profile _).map
      (prefixReadout setup leaks count ∘ History.state) = _
  rw [← PMF.map_comp, menu_prefix_state setup leaks responses watcher reveals profile
    count within, PMF.map_bind, PMF.map_bind]
  apply bind_congr_on_support _
  intro state _supported
  rw [PMF.map_comp]
  rfl

/-- The actual finite C-game compiler preserves the complete source-state
law at every source boundary, for every legal source behavioral profile. -/
theorem compiled_behavioral_prefix_law
    (setup : Setup (Player := Player) (L := L)) [setup.FiniteInitialLaw]
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (bounds : MessageBounds (graph setup)) (watcher : Player)
    (reveals : setup.program.RevealOnly)
    (observer : ∀ event, (graph setup).actor? event ≠ some watcher)
    (openable : ∀ initial ∈ setup.initialLaw.support, initial.BindingsOpenable)
    (admission : CommitmentInterface setup.program)
    (profile : Profile (setup.informationModel admission).behavioralSignature)
    (weight : ℝ) (nonnegative : 0 ≤ weight) (atMostOne : weight ≤ 1)
    (count : Nat) (within : count ≤ (graph setup).order.eventCount) :
    ((information setup leaks (bounds.withInitialValues (initialLaw setup)) watcher).runBehavioral
      (compiledProfile setup leaks (bounds.withInitialValues (initialLaw setup)) watcher
        (setup.decodeBehavioralProfile admission profile) weight nonnegative atMostOne)
      (blockOffset count + 2 * count + 1)).map
        (fun history => prefixReadout setup leaks count history.state) =
      ((setup.informationModel admission).runBehavioral profile (count + 1)).map History.state := by
  rw [menu_prefix_readout setup leaks _ watcher reveals _ count within, decoded_compiledProfile]
  exact compiled_plan_prefix_law setup leaks bounds watcher reveals observer openable admission
    profile weight nonnegative atMostOne count within

/-- The focal alias selector also preserves actual source-state prefix laws.
This is the distributional premise used by the belief projection theorem. -/
theorem focal_behavioral_prefix_law
    (setup : Setup (Player := Player) (L := L)) [setup.FiniteInitialLaw]
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (bounds : MessageBounds (graph setup)) (watcher : Player)
    (reveals : setup.program.RevealOnly)
    (observer : ∀ event, (graph setup).actor? event ≠ some watcher)
    (openable : ∀ initial ∈ setup.initialLaw.support, initial.BindingsOpenable)
    (admission : CommitmentInterface setup.program)
    (profile : BehavioralProfile setup.program)
    (permitted : ∀ who, (profile who).Admitted setup.program admission)
    (weight : ℝ) (nonnegative : 0 ≤ weight) (atMostOne : weight ≤ 1)
    (who : Player) (ordinary : who ≠ watcher)
    (reference : List (application setup leaks).PlayerEntry)
    (count : Nat) (within : count ≤ (graph setup).order.eventCount) :
    ((information setup leaks (bounds.withInitialValues (initialLaw setup)) watcher).runBehavioral
      (focalProfile setup leaks (bounds.withInitialValues (initialLaw setup)) watcher profile
        weight nonnegative atMostOne who reference)
      (blockOffset count + 2 * count + 1)).map
        (fun history => prefixReadout setup leaks count history.state) =
      ((setup.informationModel admission).runBehavioral
        (fun actor => setup.toProtocolBehavioralPolicy admission actor (profile actor)
          (permitted actor)) (count + 1)).map History.state := by
  rw [menu_prefix_readout setup leaks _ watcher reveals _ count within]
  exact focal_plan_prefix_law setup leaks bounds watcher reveals observer openable admission
    profile permitted weight nonnegative atMostOne who ordinary reference count within

end Vegas
