/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import VegasTests.MonitoredGuessingRestricted
import VegasTests.MonitoredGuessingNativeClock
import GameTheoryExtensions.Protocol.RestrictionExecution

/-! # The native clock certificate descends through the actual menu restrictions

Every restricted history is a legal raw history with exactly the same states,
responses, observations and trace length. The effective, watched and restricted
games therefore inherit the full native game's common decision depths.
-/

noncomputable section

namespace VegasTests.MonitoredGuessing.Restricted

open Vegas Vegas.EventGraphRuntime Interaction GameTheory.Protocol

theorem effective_in_raw : effectiveMenu.IncludedIn nativeMenu := by
  intro who past view response member
  exact ((normalization.menu_mem_iff_of_closed nativeMenu who past view
    (nativeBounds.rawMenu_closed nativeRuntime nativeLeaks who past view) response).mp member).1

def effectiveRawRestriction : effectiveModel.ActionRestriction nativeModel :=
  effective_in_raw.actionRestriction nativeInitialLaw nativeHorizon nativeScheduler

def effectiveDepth (who : Player) (site : effectiveModel.InformationSite who) : Nat :=
  nativeDecisionDepth who (effectiveRawRestriction.site who site)

theorem effective_common_depth (who : Player) (site : effectiveModel.InformationSite who) :
    InformationModel.InformationSite.CommonDepth effectiveModel site (effectiveDepth who site) :=
  effectiveRawRestriction.source_commonDepth who site (effectiveDepth who site)
    (native_common_decision_depth who (effectiveRawRestriction.site who site))

def watchedDepth (who : Player) (site : watchedModel.InformationSite who) : Nat :=
  effectiveDepth who (watcherRestriction.site who site)

theorem watched_common_depth (who : Player) (site : watchedModel.InformationSite who) :
    InformationModel.InformationSite.CommonDepth watchedModel site (watchedDepth who site) :=
  watcherRestriction.source_commonDepth who site (watchedDepth who site)
    (effective_common_depth who (watcherRestriction.site who site))

def restrictedDepth (who : Player) (site : restrictedModel.InformationSite who) : Nat :=
  watchedDepth who (ordinaryRestriction.site who site)

theorem restricted_common_depth (who : Player) (site : restrictedModel.InformationSite who) :
    InformationModel.InformationSite.CommonDepth restrictedModel site (restrictedDepth who site) :=
  ordinaryRestriction.source_commonDepth who site (restrictedDepth who site)
    (watched_common_depth who (ordinaryRestriction.site who site))

end VegasTests.MonitoredGuessing.Restricted
