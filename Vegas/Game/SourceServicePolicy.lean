/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.ServiceInformation
import Vegas.Pending.ReactiveCompiledMenu
import GameTheory.Math.Probability.ConditionalObservation
import GameTheory.Math.Probability.ExpectationConditioning

/-! # Source decisions in the existing sequential native service

The physical policy reads the existing compiler's policy table at the player's
turn, its ready event. Binding choices are atomic submissions; ineffective disclosures and
withholding are settled by silence and expiry. The correspondence below permits
arbitrary outstanding source guards and does not freeze the candidate catalogue
or accepted handles at initialization.

These are actual response-law equalities. Finite-menu coverage, complete service
execution, and sequential rationality require separate proofs. In particular,
erasing an ineffective private disclosure intention uses the checked source
normalization argument, not an equality of private action histories.
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
          ((compileEventProfile setup.program profile) who event owned
            (setup.eventGraph.fromModeObservation .sequential who
              (identity ▸ view.application.observation))).map
            ((runtime setup).serviceDecision leaks who past view event)
        else PMF.pure ⟨none⟩
  else PMF.pure ⟨none⟩

end Vegas
