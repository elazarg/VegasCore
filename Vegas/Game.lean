/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PurificationEdge
import Vegas.Game.ValueBindingEdge
import Vegas.Game.EventScheduling
import Vegas.Game.EventCompilation
import Vegas.Game.EventServiceEdge
import Vegas.Game.EventMessages
import Vegas.Game.EventMessageStrategic
import Vegas.Game.PendingCompositions
import Vegas.Game.ParameterOutcomes
import Vegas.Game.SetupSubgame
import Vegas.Game.BehavioralSubgame

/-! Strategic source-to-graph and graph-to-message correspondence. -/

-- OPEN OBLIGATION: Native subgame-perfect preservation
-- Source pure and behavioral policy correspondence, private setup, continuation
-- laws, and conditional SPE transfer and reflection are checked. The native
-- multiplayer protocol, atomic response integration, arbitrary-prefix recovery,
-- and coverage of every proper native root remain to be proved.
-- The initial-play Nash/Bayesian theorem does not discharge these obligations.
