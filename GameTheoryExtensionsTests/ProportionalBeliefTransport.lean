/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheoryExtensions.Analysis.Protocol.ProportionalBeliefTransport

/-! # The exact Bayes projection is the multiplier-one proportional transport -/

noncomputable section

namespace GameTheoryExtensionsTests.ProportionalBeliefTransport

open GameTheory.Protocol GameTheory.Protocol.InformationModel

variable {ι : Type*} [Fintype ι] {E T : ExecutionProtocol ι}
  (M : InformationModel E) (N : InformationModel T)
  (raw : (i : ι) → M.BehavioralPolicy i) (source : (i : ι) → N.BehavioralPolicy i)
  (project : E.History → T.History) [DecidableEq T.History]
  (who : ι) (rawSite : M.InformationSite who) (sourceSite : N.InformationSite who)

theorem exact_projection_of_proportional
    (maps : ∀ history, M.infoOf who history.trace = rawSite.1 →
      N.infoOf who (project history).trace = sourceSite.1)
    (fiber : ∀ history : N.InformationHistory who sourceSite.1,
      N.historyReachWeight source history.1 =
        ∑' original : M.InformationHistory who rawSite.1,
          if project original.1 = history.1 then M.historyReachWeight raw original.1 else 0)
    (rawAntichain : rawSite.IsHistoryAntichain)
    (sourceAntichain : sourceSite.IsHistoryAntichain)
    (rawPositive : 0 < M.informationMass raw who rawSite)
    (sourcePositive : 0 < N.informationMass source who sourceSite) :
    (M.bayesBelief raw who rawSite rawAntichain rawPositive).map
      (fun original : M.InformationHistory who rawSite.1 =>
        (⟨project original.1, maps original.1 original.2⟩ :
          N.InformationHistory who sourceSite.1)) =
      N.bayesBelief source who sourceSite sourceAntichain sourcePositive :=
  M.bayesBelief_projection_of_proportional_reach N raw source project who rawSite sourceSite
    maps 1 (fun history => by rw [one_mul]; exact fiber history) one_ne_zero ENNReal.one_ne_top
    rawAntichain sourceAntichain rawPositive sourcePositive

end GameTheoryExtensionsTests.ProportionalBeliefTransport
