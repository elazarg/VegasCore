/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.OnePacketForcedRegular

/-! # Public default evidence at forced information sets

The source decoder retains authoritative public defaults. A forced witness has
no foreign default, and equal public views carry that record to every history
of the same information set, independently of private binding regularity.
-/

noncomputable section

namespace Vegas

open SourceProgram Interaction EventGraphRuntime
open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol

variable {Player : Type} [DecidableEq Player] [Fintype Player] {L : IExpr}
  [IExpr.ResultTypes L] {setup : Setup (Player := Player) (L := L)}
  {timeouts : EventTimeouts (graph setup)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
  {bounds : MessageBounds (graph setup)} {horizon : Nat}
  {scheduler : (application setup timeouts leaks).Scheduler}

/-- The public record of a forced information set holds at every history in
that set, including histories whose hidden bindings are irregular. -/
theorem publicRecord_of_forced_information {who : Player}
    {site : (onePacketInformation setup timeouts leaks bounds horizon scheduler).InformationSite
      who}
    {past : List (application setup timeouts leaks).PlayerEntry}
    {view : (application setup timeouts leaks).PlayerView} (decision : site.1 = some (past, view))
    (forced : forcedAgent (timeouts := timeouts) (bounds.onePacketMenu timeouts leaks) (initialLaw
      setup) horizon
      scheduler who site.1)
    (history : (onePacketInformation setup timeouts leaks bounds horizon
      scheduler).InformationHistory who
      site.1)
    {control : (application setup timeouts leaks).Control} (current : history.1.state = some
      control) :
    PublicRecord setup timeouts who control := by
  obtain ⟨witness, witnessInfo, witnessForced⟩ := forced
  obtain ⟨found, foundState, viewEq⟩ := state_of_decision (timeouts := timeouts) history decision
  rw [current, Option.some.injEq] at foundState
  subst found
  obtain ⟨witnessControl, witnessStateEq, witnessViewEq⟩ :=
    state_of_decision (timeouts := timeouts) (site := site) ⟨witness, witnessInfo⟩ decision
  obtain ⟨⟨state, trace⟩, info⟩ := history
  change state = some control at current
  subst current
  obtain ⟨witnessState, witnessTrace⟩ := witness
  change witnessState = some witnessControl at witnessStateEq
  subst witnessStateEq
  have record := publicRecord_of_forced (timeouts := timeouts) who witnessControl witnessForced
  have sameView := viewEq.trans witnessViewEq.symm
  have samePublic : control.execution.application.publicView =
      witnessControl.execution.application.publicView := congrArg
    (fun observed : (application setup timeouts leaks).PlayerView =>
      observed.application.publicView)
    sameView
  have sameDefaulted : control.execution.application.config.defaulted =
      witnessControl.execution.application.config.defaulted :=
    congrArg (fun publicView : PublicView (graph setup) => publicView.observation.defaulted)
      samePublic
  intro other different excluded
  exact record other different (sameDefaulted ▸ excluded)

end Vegas
