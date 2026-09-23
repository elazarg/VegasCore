/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PurificationEdge
import Vegas.Game.ValueBindingEdge
import Vegas.Game.EventScheduling
import Vegas.Game.EventCompilation
import Vegas.Game.EventServiceEdge
import Vegas.Game.EventMessages
import Vegas.Game.ReactiveCompilation
import Vegas.Game.EventMessageStrategic
import Vegas.Game.PendingCompositions
import Vegas.Game.ParameterOutcomes
import Vegas.Game.SetupSubgame
import Vegas.Game.BehavioralSubgame

/-! Strategic source-to-graph and graph-to-message correspondence. -/

-- OPEN OBLIGATION: Native subgame-perfect preservation
-- Source continuation laws and conditional SPE transfer and reflection are checked.
-- The reactive protocol has canonical policy correspondence and bounded play.
-- The source policy compiler is defined. Canonical service completion is proved
-- for arbitrary player policies and adaptive network choices.
-- Packet protection, compiler outcome/deviation laws, full policy recovery,
-- continuation laws, and proper-root coverage remain open.
-- The fixed-service pending-menu impossibility has its own scheduling assumptions;
-- it does not establish an impossibility for the reactive protocol.
-- The initial-play Nash/Bayesian theorem does not discharge these obligations.
