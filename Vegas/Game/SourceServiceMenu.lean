/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.RevealService
import Vegas.Pending.ReactiveCompiledMenu

/-! # Finite source-service choices

Every binding opportunity admits omission, opaque admission and covered typed
values. Resolution admits withholding and authentic opening. The menu uses own
response recall to permit at most one fresh call per event.
-/

noncomputable section

namespace Vegas

open SourceProgram Interaction EventGraphRuntime

variable {Player : Type} [Fintype Player] [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]

def sourceServiceMenu (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (bounds : MessageBounds (graph setup)) :
    (application setup (Vegas.runtime setup) leaks).ResponseMenu where
  actions := bounds.compiledActions (runtime setup) leaks
  nonempty := bounds.compiledActions_nonempty (runtime setup) leaks

end Vegas
