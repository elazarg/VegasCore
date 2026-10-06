/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceDecodedDebt
import Vegas.Pending.ReactiveRiskMenu

/-! # Native histories that correspond to the intended game

A native state is *intended-clean* when its configuration decodes, at its
completed prefix, to a point of the intended game
(`Vegas.SourceProgram.ProtocolState.Intended`), and every response every player
has recorded was a canonical action at its own recall and view: silence, or the
first canonical decision of the player's own ready event within its deadline
(`Vegas.EventGraphRuntime.MessageBounds.canonicalActions`). Timing is not
constrained: deferrals, late but accepted decisions and every scheduler choice
are allowed.

A native history *corresponds* to the intended game when every state along it
is intended-clean (`Vegas.CorrespondsIntended`). Correspondence is prefix-closed
by construction (`Vegas.CorrespondsIntended.prior`). An information agent of a
response menu's model *corresponds* when some history at which it decides
corresponds (`Vegas.correspondingAgents`); this is a function of the agent's
information state.
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
  (bounds : MessageBounds (graph setup))

/-- Every response `who` recorded was a canonical action at the recall prefix
preceding it and the view it saw. -/
def CanonicalRecall (who : Player) (entries : List (application setup leaks).PlayerEntry) :
    Prop :=
  ∀ earlier entry later, entries = earlier ++ entry :: later →
    entry.action ∈ bounds.canonicalActions (runtime setup) leaks who earlier entry.beforeView

/-- A native state is intended-clean: its configuration decodes at its completed
prefix to a point of the intended game, and every recorded response of every
player was canonical. The uninitialized state is clean. -/
def IntendedClean : (application setup leaks).ProtocolState → Prop
  | none => True
  | some control =>
      (∃ rank point, control.execution.application.config.cut.IsPrefix rank ∧
        sourceServicePrefix? setup rank control.execution.application.config = some point ∧
        ProtocolState.Intended setup.program point) ∧
      ∀ who, CanonicalRecall setup leaks bounds who (control.execution.recall who)

variable {setup leaks}

/-- **Correspondence with the intended game.** Every state along the native
history is intended-clean. -/
def CorrespondsIntended (menu : (application setup leaks).ResponseMenu)
    (initial : PMF (application setup leaks).State) (horizon : Nat)
    (scheduler : (application setup leaks).Scheduler) :
    ∀ {state}, (menu.protocol initial horizon scheduler).Trace state → Prop
  | _, .start => True
  | state, .extend prior _ _ _ =>
      CorrespondsIntended menu initial horizon scheduler prior ∧
        IntendedClean setup leaks bounds state

/-- Correspondence holds of every earlier history. -/
theorem CorrespondsIntended.prior {menu : (application setup leaks).ResponseMenu}
    {initial : PMF (application setup leaks).State} {horizon : Nat}
    {scheduler : (application setup leaks).Scheduler}
    {before after : (application setup leaks).ProtocolState}
    {prior : (menu.protocol initial horizon scheduler).Trace before}
    {joint : Player → Option (application setup leaks).Action}
    {legal : (menu.protocol initial horizon scheduler).Legal before joint}
    {realized : after ∈ ((menu.protocol initial horizon scheduler).step before
      ⟨joint, legal⟩).support}
    (corresponds : CorrespondsIntended bounds menu initial horizon scheduler
      (.extend prior joint legal realized)) :
    CorrespondsIntended bounds menu initial horizon scheduler prior :=
  corresponds.1

/-- A corresponding history ends in an intended-clean state. -/
theorem CorrespondsIntended.clean {menu : (application setup leaks).ResponseMenu}
    {initial : PMF (application setup leaks).State} {horizon : Nat}
    {scheduler : (application setup leaks).Scheduler}
    {state : (application setup leaks).ProtocolState}
    {trace : (menu.protocol initial horizon scheduler).Trace state}
    (corresponds : CorrespondsIntended bounds menu initial horizon scheduler trace) :
    IntendedClean setup leaks bounds state :=
  match trace, corresponds with
  | .start, _ => trivial
  | .extend _ _ _ _, corresponds => corresponds.2

open Classical in
/-- The information agents of a response menu's model at which some
corresponding history decides. Membership depends only on the agent, that is,
on its player and information state. -/
def correspondingAgents (menu : (application setup leaks).ResponseMenu)
    (initial : PMF (application setup leaks).State) (horizon : Nat)
    (scheduler : (application setup leaks).Scheduler)
    [Fintype (menu.protocol initial horizon scheduler).History]
    [∀ who, DecidableEq ((menu.information initial horizon scheduler).InfoState who)] :
    Finset ((menu.information initial horizon scheduler).InformationAgent
      (menu.information initial horizon scheduler).playedInformation) :=
  Finset.univ.filter fun agent =>
    ∃ history : (menu.protocol initial horizon scheduler).History,
      CorrespondsIntended bounds menu initial horizon scheduler history.trace ∧
        (menu.protocol initial horizon scheduler).active history.state agent.1 ∧
        (menu.information initial horizon scheduler).infoOf agent.1 history.trace = agent.2.1

theorem mem_correspondingAgents {menu : (application setup leaks).ResponseMenu}
    {initial : PMF (application setup leaks).State} {horizon : Nat}
    {scheduler : (application setup leaks).Scheduler}
    [Fintype (menu.protocol initial horizon scheduler).History]
    [∀ who, DecidableEq ((menu.information initial horizon scheduler).InfoState who)]
    {agent : (menu.information initial horizon scheduler).InformationAgent
      (menu.information initial horizon scheduler).playedInformation} :
    agent ∈ correspondingAgents bounds menu initial horizon scheduler ↔
      ∃ history : (menu.protocol initial horizon scheduler).History,
        CorrespondsIntended bounds menu initial horizon scheduler history.trace ∧
          (menu.protocol initial horizon scheduler).active history.state agent.1 ∧
          (menu.information initial horizon scheduler).infoOf agent.1 history.trace =
            agent.2.1 := by
  classical
  simp only [correspondingAgents, Finset.mem_filter, Finset.mem_univ, true_and]

/-- A corresponding decision history makes its agent corresponding. -/
theorem agentAt_mem_correspondingAgents {menu : (application setup leaks).ResponseMenu}
    {initial : PMF (application setup leaks).State} {horizon : Nat}
    {scheduler : (application setup leaks).Scheduler}
    [Fintype (menu.protocol initial horizon scheduler).History]
    [∀ who, DecidableEq ((menu.information initial horizon scheduler).InfoState who)] {who : Player}
    (site : (menu.information initial horizon scheduler).InformationSite who)
    (history : (menu.information initial horizon scheduler).InformationHistory who site.1)
    (corresponds : CorrespondsIntended bounds menu initial horizon scheduler history.1.trace) :
    (menu.information initial horizon scheduler).agentAt site ∈
      correspondingAgents bounds menu initial horizon scheduler :=
  (mem_correspondingAgents bounds).mpr ⟨history.1, corresponds,
    InformationModel.InformationSite.active
      (M := menu.information initial horizon scheduler) site history, history.2⟩

end Vegas
