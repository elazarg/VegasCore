/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.OnePacketKeyedRecords
import Vegas.Game.OnePacketSwapRecord

/-! # Record fibers from a correspondence scaling the base weight

A bijection between the histories of two sites that keeps regularity and the
operational record, and multiplies the base weight by a common nonzero factor,
makes every record fiber of the second site that multiple of the first's
(`Vegas.fiber_of_equiv_scaled`), so the sites' normalized base laws agree
(`Vegas.baseLawAgrees_of_equiv_scaled`). An exchange of the owner's hidden
initial values scales the prior by such a common factor when hidden initial
cells are independent, so a hidden swap scaling the base weight by a common
factor gives agreeing base laws (`Vegas.baseLawAgrees_of_swap_scaled`).
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
open GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {runtime : EventGraphRuntime (graph setup)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
  [Fintype Player] {bounds : MessageBounds (graph setup)} {horizon : Nat}
  {scheduler : (application setup runtime leaks).Scheduler}

open Classical in
/-- **Scaled fibers from a correspondence.** A bijection between the histories
of two sites keeping regularity and the operational record, and multiplying the
base weight by `factor`, multiplies each record's regular base weight by
`factor`. -/
theorem fiber_of_equiv_scaled {who : Player}
    [Finite (onePacketProtocol setup runtime leaks bounds horizon scheduler).History]
    (base : (onePacketProtocol setup runtime leaks bounds horizon scheduler).History → ℝ)
    (regular : (onePacketProtocol setup runtime leaks bounds horizon scheduler).History → Prop)
    (first second : (onePacketInformation setup runtime leaks bounds horizon
      scheduler).InformationSite who)
    (swap : (onePacketInformation setup runtime leaks bounds horizon scheduler).InformationHistory
      who
        first.1 ≃
      (onePacketInformation setup runtime leaks bounds horizon scheduler).InformationHistory who
        second.1)
    (regularEq : ∀ history, regular (swap history).1 ↔ regular history.1)
    (recordEq : ∀ history, operationalRecord setup runtime leaks bounds horizon scheduler
      (swap history).1.trace = operationalRecord setup runtime leaks bounds horizon scheduler
        history.1.trace)
    (factor : ℝ) (baseEq : ∀ history, base (swap history).1 = factor * base history.1)
    (record : List (Option (OperationalState setup runtime leaks))) :
    ∑' b : (onePacketInformation setup runtime leaks bounds horizon scheduler).InformationHistory
      who
        second.1, (if regular b.1 ∧
          operationalRecord setup runtime leaks bounds horizon scheduler b.1.trace = record then
        base b.1 else 0) =
      factor * ∑' a : (onePacketInformation setup runtime leaks bounds horizon
        scheduler).InformationHistory who first.1, (if regular a.1 ∧
          operationalRecord setup runtime leaks bounds horizon scheduler a.1.trace = record then
        base a.1 else 0) := by
  rw [← swap.tsum_eq, ← tsum_mul_left]
  apply tsum_congr
  intro history
  simp only [regularEq, recordEq, baseEq, mul_ite, mul_zero]

open Classical in
/-- **Base agreement from a scaling correspondence.** -/
theorem baseLawAgrees_of_equiv_scaled {who : Player}
    [Finite (onePacketProtocol setup runtime leaks bounds horizon scheduler).History]
    (base : (onePacketProtocol setup runtime leaks bounds horizon scheduler).History → ℝ)
    (regular : (onePacketProtocol setup runtime leaks bounds horizon scheduler).History → Prop)
    (first second : (onePacketInformation setup runtime leaks bounds horizon
      scheduler).InformationSite who)
    (swap : (onePacketInformation setup runtime leaks bounds horizon scheduler).InformationHistory
      who
        first.1 ≃
      (onePacketInformation setup runtime leaks bounds horizon scheduler).InformationHistory who
        second.1)
    (regularEq : ∀ history, regular (swap history).1 ↔ regular history.1)
    (recordEq : ∀ history, operationalRecord setup runtime leaks bounds horizon scheduler
      (swap history).1.trace = operationalRecord setup runtime leaks bounds horizon scheduler
        history.1.trace)
    (factor : ℝ) (factor_ne : factor ≠ 0)
    (baseEq : ∀ history, base (swap history).1 = factor * base history.1)
    (payoff : List (Option (OperationalState setup runtime leaks)) → ℝ) :
    BaseLawAgrees (runtime := runtime) base regular first second payoff :=
  baseLawAgrees_of_fibers (runtime := runtime) base regular first second factor factor_ne
    (fiber_of_equiv_scaled (runtime := runtime) base regular first second swap regularEq recordEq
      factor baseEq)
    payoff

/-- **Base agreement from a scaling hidden swap.** For an involutive hidden swap
that guards the histories of two sites and exchanges them, the swap keeps every
operational record, so if it also keeps regularity and multiplies the base
weight of the first site's histories by a common nonzero factor, the two sites'
base laws agree on every payoff of the record. -/
theorem baseLawAgrees_of_swap_scaled {who : Player}
    [Finite (onePacketProtocol setup runtime leaks bounds horizon scheduler).History]
    (base : (onePacketProtocol setup runtime leaks bounds horizon scheduler).History → ℝ)
    (regular : (onePacketProtocol setup runtime leaks bounds horizon scheduler).History → Prop)
    (first second : (onePacketInformation setup runtime leaks bounds horizon
      scheduler).InformationSite who)
    (swap : HiddenSwap (graph setup)) (allowed : Set (graph setup).Inputs)
    (initialClosed : ∀ state ∈ (initialLaw setup).support, state.config.inputs ∈ allowed →
      state.swap swap ∈ (initialLaw setup).support)
    (bounded : ∀ handle raw, raw ∈ bounds.values → swap.raw handle raw ∈ bounds.values)
    (allowedClosed : ∀ inputs ∈ allowed,
      (fun input => swap.values.value (.inl input) (inputs input)) ∈ allowed)
    (guardedFirst : ∀ history : (onePacketProtocol setup runtime leaks bounds horizon
      scheduler).History,
      (onePacketInformation setup runtime leaks bounds horizon scheduler).infoOf who history.trace =
        first.1 → SwapGuardState setup runtime swap allowed history.state)
    (guardedSecond : ∀ history : (onePacketProtocol setup runtime leaks bounds horizon
      scheduler).History,
      (onePacketInformation setup runtime leaks bounds horizon scheduler).infoOf who history.trace =
        second.1 → SwapGuardState setup runtime swap allowed history.state)
    (toSecond : ∀ (history : (onePacketProtocol setup runtime leaks bounds horizon
      scheduler).History)
      (member : (onePacketInformation setup runtime leaks bounds horizon scheduler).infoOf who
        history.trace = first.1),
      (onePacketInformation setup runtime leaks bounds horizon scheduler).infoOf who
        ((onePacketSwapSymmetry (runtime := runtime) bounds (initialLaw setup) horizon scheduler
          swap initialClosed
          bounded).mapHistory history (guardedFirst history member)).trace = second.1)
    (toFirst : ∀ (history : (onePacketProtocol setup runtime leaks bounds horizon
      scheduler).History)
      (member : (onePacketInformation setup runtime leaks bounds horizon scheduler).infoOf who
        history.trace = second.1),
      (onePacketInformation setup runtime leaks bounds horizon scheduler).infoOf who
        ((onePacketSwapSymmetry (runtime := runtime) bounds (initialLaw setup) horizon scheduler
          swap initialClosed
          bounded).mapHistory history (guardedSecond history member)).trace = first.1)
    (regularEq : ∀ (history : (onePacketProtocol setup runtime leaks bounds horizon
      scheduler).History)
      (member : (onePacketInformation setup runtime leaks bounds horizon scheduler).infoOf who
        history.trace = first.1),
      regular ((onePacketSwapSymmetry (runtime := runtime) bounds (initialLaw setup) horizon
        scheduler swap
        initialClosed bounded).mapHistory history (guardedFirst history member)) ↔
        regular history)
    (factor : ℝ) (factor_ne : factor ≠ 0)
    (baseEq : ∀ (history : (onePacketProtocol setup runtime leaks bounds horizon scheduler).History)
      (member : (onePacketInformation setup runtime leaks bounds horizon scheduler).infoOf who
        history.trace = first.1),
      base ((onePacketSwapSymmetry (runtime := runtime) bounds (initialLaw setup) horizon
        scheduler swap
        initialClosed bounded).mapHistory history (guardedFirst history member)) =
        factor * base history)
    (payoff : List (Option (OperationalState setup runtime leaks)) → ℝ) :
    BaseLawAgrees (runtime := runtime) base regular first second payoff :=
  baseLawAgrees_of_equiv_scaled (runtime := runtime) base regular first second
    (StateSymmetry.exchange (onePacketSwapSymmetry_involutive (runtime := runtime) bounds
      (initialLaw setup) horizon
      scheduler swap initialClosed bounded allowedClosed) _ _ guardedFirst guardedSecond toSecond
      toFirst)
    (fun history => regularEq history.1 history.2)
    (fun history => operationalRecord_mapTrace (runtime := runtime) swap initialClosed bounded
      history.1.trace
      (guardedFirst history.1 history.2))
    factor factor_ne (fun history => baseEq history.1 history.2) payoff

end Vegas
