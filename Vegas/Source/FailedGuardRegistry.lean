/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.Semantics

/-! # Failed subjects make additional compiled guard obligations inert -/

namespace Vegas.SourceProgram

variable {Player : Type} {L : IExpr} {Γ : SourceCtx Player L}

/-- A failed published subject discharges its retained obligation for every
choice of the other guard inputs. -/
theorem Obligation.accepts_of_subject_failure (obligation : Obligation Γ)
    (revelations : Revelations Γ) (state : State L Γ)
    (failed : (revelations obligation.source).result state = .failure) :
    obligation.accepts revelations state = true := by
  unfold Obligation.accepts
  rw [failed]
  exact GuardCode.accepts_subject_failure _ _

end Vegas.SourceProgram
