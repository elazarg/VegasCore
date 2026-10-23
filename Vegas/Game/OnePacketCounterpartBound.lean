/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.OnePacketCounterpartImage
import Vegas.Game.OnePacketCounterpartSteps
import Vegas.Game.OnePacketOwnIntended
import Vegas.Game.OnePacketDisclosureAlong

/-! # Response bounds along swaps toward a forced witness

Along a history and its swap toward a forced witness
(`Vegas.counterpart_of_witness`), the response masses of players acting at
forced information are at most `K₁` times those of their images
(`Vegas.SwapResponseBound`), and at most `ε` times at the first irregular
response (`Vegas.SwapFirstBound`). With independent hidden initial cells, every
player responding along the history acts at forced information
(`Vegas.forcedAgent_of_splice`), and its pending reveals resolve
(`Vegas.disclosureResolves_along`). Own completions are intended and the public
record holds along every prefix of a history where they hold
(`Vegas.ownCompletionsIntended_and_publicRecord_of_tracePrefix`).
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol Interaction
  EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player] {L : IExpr}
  [IExpr.ResultTypes L] {setup : Setup (Player := Player) (L := L)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
  {bounds : MessageBounds (graph setup)} {horizon : Nat}
  {scheduler : (application setup leaks).Scheduler}
  {sequence : ℕ → setup.intendedModel.BehavioralAssessment}
  {profiles : ℕ → ∀ player,
    (onePacketInformation setup leaks bounds horizon scheduler).BehavioralPolicy player}

variable (setup leaks bounds horizon scheduler sequence profiles) in
/-- **Response masses compared under hidden swaps.** At stage `n`, every
response of a player other than `who`, acting at an information state forced for
it with a canonical disclosure, along a history ending at a state guarded for a
hidden swap, whose image under the swap is regular, has response mass at most
`K₁` times that of its image. -/
def SwapResponseBound (n : ℕ) (who : Player) (K₁ : ℝ) : Prop :=
  ∀ (swap : HiddenSwap (graph setup)) (allowed : Set (graph setup).Inputs) {before after}
    (_ : (onePacketProtocol setup leaks bounds horizon scheduler).Trace before) joint
    (legal : (onePacketProtocol setup leaks bounds horizon scheduler).Legal before joint)
    (_ : after ∈ ((onePacketProtocol setup leaks bounds horizon scheduler).step before
      ⟨joint, legal⟩).support) (_ : SwapGuardState setup swap allowed after)
    (_ : (onePacketProtocol setup leaks bounds horizon scheduler).Trace
      (swap.protocolState before))
    (imageLegal : (onePacketProtocol setup leaks bounds horizon scheduler).Legal
      (swap.protocolState before) (swap.joint joint))
    (_ : swap.protocolState after ∈ ((onePacketProtocol setup leaks bounds horizon scheduler).step
      (swap.protocolState before) ⟨swap.joint joint, imageLegal⟩).support)
    (control next : (application setup leaks).Control) (actor : Player),
    before = some control → after = some next → control.actor = some actor → actor ≠ who →
    forcedAgent (bounds.onePacketMenu (runtime setup) leaks) (initialLaw setup) horizon scheduler
      actor ((application setup leaks).observe actor (some control)) →
    DisclosureCanonical setup leaks bounds actor (control.execution.recall actor)
      (control.execution.observe (application setup leaks) actor) →
    RegularStep setup leaks bounds horizon scheduler (sequence n) who
      (swap.protocolState before) (swap.joint joint) (swap.protocolState after) →
    responseMass setup leaks bounds horizon scheduler (profiles n) control joint ≤
      K₁ * responseMass setup leaks bounds horizon scheduler (profiles n) (swap.control control)
        (swap.joint joint)

variable (setup leaks bounds horizon scheduler sequence profiles) in
/-- **The first irregular response compared under hidden swaps.** At stage `n`,
an irregular response of a forced player other than `who` from a state forced
for `who`, after a regular history, whose image under a hidden swap is regular,
has response mass at most `ε` times that of its image. -/
def SwapFirstBound (n : ℕ) (who : Player) (ε : ℝ) : Prop :=
  ∀ (swap : HiddenSwap (graph setup)) (allowed : Set (graph setup).Inputs) {before after}
    (prior : (onePacketProtocol setup leaks bounds horizon scheduler).Trace before) joint
    (legal : (onePacketProtocol setup leaks bounds horizon scheduler).Legal before joint)
    (_ : after ∈ ((onePacketProtocol setup leaks bounds horizon scheduler).step before
      ⟨joint, legal⟩).support) (_ : SwapGuardState setup swap allowed after)
    (_ : (onePacketProtocol setup leaks bounds horizon scheduler).Trace
      (swap.protocolState before))
    (imageLegal : (onePacketProtocol setup leaks bounds horizon scheduler).Legal
      (swap.protocolState before) (swap.joint joint))
    (_ : swap.protocolState after ∈ ((onePacketProtocol setup leaks bounds horizon scheduler).step
      (swap.protocolState before) ⟨swap.joint joint, imageLegal⟩).support)
    (control next : (application setup leaks).Control) (actor : Player),
    before = some control → after = some next → control.actor = some actor → actor ≠ who →
    ForcedState setup leaks who (some control) →
    forcedAgent (bounds.onePacketMenu (runtime setup) leaks) (initialLaw setup) horizon scheduler
      actor ((application setup leaks).observe actor (some control)) →
    RegularStep setup leaks bounds horizon scheduler (sequence n) who
      (swap.protocolState before) (swap.joint joint) (swap.protocolState after) →
    RegularTrace setup leaks bounds horizon scheduler (sequence n) who prior →
    ¬ RegularStep setup leaks bounds horizon scheduler (sequence n) who before joint after →
    responseMass setup leaks bounds horizon scheduler (profiles n) control joint ≤
      ε * responseMass setup leaks bounds horizon scheduler (profiles n) (swap.control control)
        (swap.joint joint)

variable [DecidableEq (CellTy Player L)]
  [Finite (onePacketProtocol setup leaks bounds horizon scheduler).History]

omit [DecidableEq (CellTy Player L)]
  [Finite (onePacketProtocol setup leaks bounds horizon scheduler).History] in
private theorem observe_of_infoOf'' {who : Player}
    {past : List (application setup leaks).PlayerEntry}
    {view : (application setup leaks).PlayerView}
    (native : (onePacketProtocol setup leaks bounds horizon scheduler).History)
    (seen : (onePacketInformation setup leaks bounds horizon scheduler).infoOf who native.trace =
      some (past, view)) {control : (application setup leaks).Control}
    (current : native.state = some control) :
    control.execution.observe (application setup leaks) who = view := by
  obtain ⟨state, trace⟩ := native
  change state = some control at current
  subst current
  rw [onePacket_infoOf] at seen
  by_cases active : control.actor = some who
  · simp only [ReactiveApplication.observe, active, ↓reduceIte] at seen
    exact (Prod.mk.inj (Option.some.inj seen)).2
  · simp [ReactiveApplication.observe, active] at seen

omit [DecidableEq (CellTy Player L)]
  [Finite (onePacketProtocol setup leaks bounds horizon scheduler).History] in
/-- Own completions are intended and the public record holds along every prefix
of a history where they hold. -/
theorem ownCompletionsIntended_and_publicRecord_of_tracePrefix
    {who : Player} {first : (application setup leaks).ProtocolState}
    (prefixTrace : (onePacketProtocol setup leaks bounds horizon scheduler).Trace first) :
    ∀ {final} {trace : (onePacketProtocol setup leaks bounds horizon scheduler).Trace final},
      TracePrefix prefixTrace trace →
      OwnCompletionsIntended (bounds := bounds) (horizon := horizon) (scheduler := scheduler)
        who trace →
      (∀ control, final = some control → PublicRecord setup who control) →
      OwnCompletionsIntended (bounds := bounds) (horizon := horizon) (scheduler := scheduler)
          who prefixTrace ∧
        ∀ control, first = some control → PublicRecord setup who control := by
  intro final trace isPrefix
  induction isPrefix with
  | refl => exact fun own record => ⟨own, record⟩
  | @extend source target prior _ joint legal realized ih =>
      intro own record
      refine ih own.1 fun control same => ?_
      subst same
      obtain ⟨next, rfl, _⟩ := (application setup leaks).transition_recall_prefix (initialLaw setup)
        horizon scheduler control target joint realized
      exact publicRecord_of_transition prior joint realized (record next rfl)

end Vegas
