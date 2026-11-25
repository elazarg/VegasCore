module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Game.RevealService

@[expose] public section

/-! # Sample readout from graph configurations and service traffic -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

def sampledValue {compiled : Vegas.EventGraph Player L}
    (event : compiled.EventId) {payload : L.Ty}
    (outputEq : compiled.outputLayout event = .publicData payload)
    (config : compiled.Config) : L.Val payload :=
  ((config.outputs event).map (cast (congrArg EventField.Value outputEq))).getD
    (L.someValue payload)

def sampledTrafficValue
    (setup : Setup (Player := Player) (L := L)) {deps : setup.dataflowGraph.Dependencies}
    {duration : (serviceGraph setup deps).EventId → Nat}
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup deps)))
    (event : (serviceGraph setup deps).EventId) {payload : L.Ty}
    (outputEq : (serviceGraph setup deps).outputLayout event = .publicData payload)
    (traffic : MessageNetwork Player (serviceApplication setup deps duration leaks).Payload ×
      List (MessageId Player × Bool) ×
      List (serviceApplication setup deps duration leaks).EnvironmentEntry ×
      List (serviceApplication setup deps duration leaks).PlayerEntry ×
      PlayerView (serviceGraph setup deps) × PublicView (serviceGraph setup deps)) :
    L.Val payload :=
  ((traffic.2.2.2.2.2.observation.store (.inr event)).map
    (cast (congrArg EventField.Value outputEq))).getD (L.someValue payload)

end Vegas
