/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.ServiceInformation
import Vegas.Pending.ReactivePolicy

/-! # Source decisions in the sequential native service

The physical policy reads the compiler's policy table at the player's
turn, its ready event. Binding choices are atomic submissions; unopenable disclosures and
withholding are settled by silence and expiry. The correspondence below permits
arbitrary outstanding source guards and does not freeze the candidate catalogue
or accepted handles at initialization.

These are actual response-law equalities. Finite-menu coverage, complete service
execution, and sequential rationality require separate proofs. Excluded players
make no source decision and transmit nothing.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))

/-- The source compiler's decision at the player's turn, represented by one
actual native response. This definition introduces neither strategy memory nor
an additional runtime step. -/
def sourceServicePolicy (profile : BehavioralProfile setup.program) (who : Player) :
    (application setup (Vegas.runtime setup) leaks).Policy := fun past view =>
  if identity : view.application.who = who then
    match view.application.publicView.ownTurn? who with
    | none => PMF.pure ⟨none⟩
    | some event =>
        if owned : (graph setup).actor? event = some who then
          let observed := setup.eventGraph.fromModeObservation .sequential who
            (identity ▸ view.application.observation)
          if active : who ∉ observed.defaulted then
            ((compileEventProfile setup.program profile) who event owned observed active).map
              ((runtime setup).serviceDecision leaks who past view event)
          else PMF.pure ⟨none⟩
        else PMF.pure ⟨none⟩
  else PMF.pure ⟨none⟩

end Vegas
