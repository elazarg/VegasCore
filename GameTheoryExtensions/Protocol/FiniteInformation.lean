/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheory.Protocol.BehavioralAssessment

/-! # Finite decision information

Finite legal histories imply finite decision sites. The ambient information
carrier may remain infinite: unreachable information values are irrelevant.
-/

noncomputable section

namespace GameTheory.Protocol.InformationModel

variable {ι : Type*} {E : ExecutionProtocol ι} {M : InformationModel E}

instance InformationSite.finite [Finite E.History] (who : ι) :
    Finite (M.InformationSite who) := by
  let witness (site : M.InformationSite who) : E.History := site.2.choose.1
  apply Finite.of_injective witness
  intro first second same
  apply Subtype.ext
  exact first.2.choose.2.symm.trans
    ((congrArg (fun history : E.History => M.infoOf who history.trace) same).trans
      second.2.choose.2)

end GameTheory.Protocol.InformationModel
