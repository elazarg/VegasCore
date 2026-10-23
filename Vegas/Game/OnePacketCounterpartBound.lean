/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.OnePacketCounterpartImage

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

variable [DecidableEq (CellTy Player L)]
  [Finite (onePacketProtocol setup leaks bounds horizon scheduler).History]

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
