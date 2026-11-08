/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.OnePacketForcedRegular

/-! # Intended own prefixes and public records persist backward

Own intended-completion invariants restrict to every earlier actual trace.
Foreign activity persists backward because public defaults are monotone.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol Interaction
  EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player] {L : IExpr}
  [IExpr.ResultTypes L] {setup : Setup (Player := Player) (L := L)}
  {timeouts : EventTimeouts (graph setup)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
  {bounds : MessageBounds (graph setup)} {horizon : Nat}
  {scheduler : (application setup timeouts leaks).Scheduler}

/-- Own completions are intended and the public record holds along every prefix
of a history where they hold. -/
theorem ownCompletionsIntended_and_publicRecord_of_tracePrefix
    {who : Player} {first : (application setup timeouts leaks).ProtocolState}
    (prefixTrace : (onePacketProtocol setup timeouts leaks bounds horizon scheduler).Trace first) :
    ∀ {final} {trace : (onePacketProtocol setup timeouts leaks bounds horizon scheduler).Trace
      final},
      TracePrefix prefixTrace trace →
      OwnCompletionsIntended (timeouts := timeouts) (bounds := bounds) (horizon := horizon)
        (scheduler := scheduler)
        who trace →
      (∀ control, final = some control → PublicRecord setup timeouts who control) →
      OwnCompletionsIntended (timeouts := timeouts) (bounds := bounds) (horizon := horizon)
        (scheduler := scheduler)
          who prefixTrace ∧
        ∀ control, first = some control → PublicRecord setup timeouts who control := by
  intro final trace isPrefix
  induction isPrefix with
  | refl => exact fun own record => ⟨own, record⟩
  | @extend source target prior _ joint legal realized ih =>
      intro own record
      refine ih own.1 fun control same => ?_
      subst same
      obtain ⟨next, rfl, _⟩ := (application setup timeouts leaks).transition_recall_prefix
        (initialLaw setup)
        horizon scheduler control target joint realized
      exact publicRecord_of_transition (timeouts := timeouts) (horizon := horizon)
        joint realized (record next rfl)

end Vegas
