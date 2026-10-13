/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.OnePacketKeyedRecords
import Vegas.Game.OnePacketSwapRecord

/-! # Record fibers from a correspondence of site histories

A bijection between the histories of two sites that keeps regularity, the
operational record and the base weight makes every record fiber of the two
sites carry the same base weight (`Vegas.fiber_of_equiv`), so the sites' base
laws agree (`Vegas.baseLawAgrees_of_equiv`). For two sites of the same owner
with the same late-delivery key, the intended correspondence swaps the owner's
committed value at its unrevealed binding.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
open GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
  [Fintype Player] {bounds : MessageBounds (graph setup)} {horizon : Nat}
  {scheduler : (application setup leaks).Scheduler}

open Classical in
/-- **Fibers from a correspondence.** A bijection between the histories of two
sites keeping regularity, the operational record and the base weight gives each
record the same regular base weight at both sites. -/
theorem fiber_of_equiv {who : Player}
    [Finite (onePacketProtocol setup leaks bounds horizon scheduler).History]
    (base : (onePacketProtocol setup leaks bounds horizon scheduler).History → ℝ)
    (regular : (onePacketProtocol setup leaks bounds horizon scheduler).History → Prop)
    (first second : (onePacketInformation setup leaks bounds horizon scheduler).InformationSite who)
    (swap : (onePacketInformation setup leaks bounds horizon scheduler).InformationHistory who
        first.1 ≃
      (onePacketInformation setup leaks bounds horizon scheduler).InformationHistory who
        second.1)
    (regularEq : ∀ history, regular (swap history).1 ↔ regular history.1)
    (recordEq : ∀ history, operationalRecord setup leaks bounds horizon scheduler
      (swap history).1.trace = operationalRecord setup leaks bounds horizon scheduler
        history.1.trace)
    (baseEq : ∀ history, base (swap history).1 = base history.1)
    (record : List (Option (OperationalState setup leaks))) :
    ∑' b : (onePacketInformation setup leaks bounds horizon scheduler).InformationHistory who
        second.1, (if regular b.1 ∧
          operationalRecord setup leaks bounds horizon scheduler b.1.trace = record then
        base b.1 else 0) =
      1 * ∑' a : (onePacketInformation setup leaks bounds horizon
        scheduler).InformationHistory who first.1, (if regular a.1 ∧
          operationalRecord setup leaks bounds horizon scheduler a.1.trace = record then
        base a.1 else 0) := by
  rw [one_mul, ← swap.tsum_eq]
  apply tsum_congr
  intro history
  simp only [regularEq, recordEq, baseEq]

open Classical in
/-- **Base agreement from a correspondence.** -/
theorem baseLawAgrees_of_equiv {who : Player}
    [Finite (onePacketProtocol setup leaks bounds horizon scheduler).History]
    (base : (onePacketProtocol setup leaks bounds horizon scheduler).History → ℝ)
    (regular : (onePacketProtocol setup leaks bounds horizon scheduler).History → Prop)
    (first second : (onePacketInformation setup leaks bounds horizon scheduler).InformationSite who)
    (swap : (onePacketInformation setup leaks bounds horizon scheduler).InformationHistory who
        first.1 ≃
      (onePacketInformation setup leaks bounds horizon scheduler).InformationHistory who
        second.1)
    (regularEq : ∀ history, regular (swap history).1 ↔ regular history.1)
    (recordEq : ∀ history, operationalRecord setup leaks bounds horizon scheduler
      (swap history).1.trace = operationalRecord setup leaks bounds horizon scheduler
        history.1.trace)
    (baseEq : ∀ history, base (swap history).1 = base history.1)
    (payoff : List (Option (OperationalState setup leaks)) → ℝ) :
    BaseLawAgrees base regular first second payoff :=
  baseLawAgrees_of_fibers base regular first second 1 one_ne_zero
    (fiber_of_equiv base regular first second swap regularEq recordEq baseEq) payoff

open Classical in
/-- **Base agreement from a hidden swap.** For an involutive hidden swap that
guards the histories of two sites and exchanges them, the swap keeps every
operational record, so if it also keeps regularity and the base weight of the
first site's histories, the two sites' base laws agree on every payoff of the
record. -/
theorem baseLawAgrees_of_swap {who : Player}
    [Finite (onePacketProtocol setup leaks bounds horizon scheduler).History]
    (base : (onePacketProtocol setup leaks bounds horizon scheduler).History → ℝ)
    (regular : (onePacketProtocol setup leaks bounds horizon scheduler).History → Prop)
    (first second : (onePacketInformation setup leaks bounds horizon scheduler).InformationSite who)
    (swap : HiddenSwap (graph setup)) (allowed : Set (graph setup).Inputs)
    (initialClosed : ∀ state ∈ (initialLaw setup).support, state.config.inputs ∈ allowed →
      state.swap swap ∈ (initialLaw setup).support)
    (bounded : ∀ handle raw, raw ∈ bounds.values → swap.raw handle raw ∈ bounds.values)
    (allowedClosed : ∀ inputs ∈ allowed,
      (fun input => swap.values.value (.inl input) (inputs input)) ∈ allowed)
    (guardedFirst : ∀ history : (onePacketProtocol setup leaks bounds horizon scheduler).History,
      (onePacketInformation setup leaks bounds horizon scheduler).infoOf who history.trace =
        first.1 → SwapGuardState setup swap allowed history.state)
    (guardedSecond : ∀ history : (onePacketProtocol setup leaks bounds horizon scheduler).History,
      (onePacketInformation setup leaks bounds horizon scheduler).infoOf who history.trace =
        second.1 → SwapGuardState setup swap allowed history.state)
    (toSecond : ∀ (history : (onePacketProtocol setup leaks bounds horizon scheduler).History)
      (member : (onePacketInformation setup leaks bounds horizon scheduler).infoOf who
        history.trace = first.1),
      (onePacketInformation setup leaks bounds horizon scheduler).infoOf who
        ((onePacketSwapSymmetry bounds (initialLaw setup) horizon scheduler swap initialClosed
          bounded).mapHistory history (guardedFirst history member)).trace = second.1)
    (toFirst : ∀ (history : (onePacketProtocol setup leaks bounds horizon scheduler).History)
      (member : (onePacketInformation setup leaks bounds horizon scheduler).infoOf who
        history.trace = second.1),
      (onePacketInformation setup leaks bounds horizon scheduler).infoOf who
        ((onePacketSwapSymmetry bounds (initialLaw setup) horizon scheduler swap initialClosed
          bounded).mapHistory history (guardedSecond history member)).trace = first.1)
    (regularEq : ∀ (history : (onePacketProtocol setup leaks bounds horizon scheduler).History)
      (member : (onePacketInformation setup leaks bounds horizon scheduler).infoOf who
        history.trace = first.1),
      regular ((onePacketSwapSymmetry bounds (initialLaw setup) horizon scheduler swap
        initialClosed bounded).mapHistory history (guardedFirst history member)) ↔
        regular history)
    (baseEq : ∀ (history : (onePacketProtocol setup leaks bounds horizon scheduler).History)
      (member : (onePacketInformation setup leaks bounds horizon scheduler).infoOf who
        history.trace = first.1),
      base ((onePacketSwapSymmetry bounds (initialLaw setup) horizon scheduler swap
        initialClosed bounded).mapHistory history (guardedFirst history member)) = base history)
    (payoff : List (Option (OperationalState setup leaks)) → ℝ) :
    BaseLawAgrees base regular first second payoff :=
  baseLawAgrees_of_equiv base regular first second
    (StateSymmetry.exchange (onePacketSwapSymmetry_involutive bounds (initialLaw setup) horizon
      scheduler swap initialClosed bounded allowedClosed) _ _ guardedFirst guardedSecond toSecond
      toFirst)
    (fun history => regularEq history.1 history.2)
    (fun history => operationalRecord_mapTrace swap initialClosed bounded history.1.trace
      (guardedFirst history.1 history.2))
    (fun history => baseEq history.1 history.2) payoff

end Vegas
