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

/-- Adding the compiled obligation of an automatic failed slot does not change
any reveal decision when its subject's published result is failure. -/
theorem Registry.completedBy_cons_all_of_subject_failure (obligation : Obligation Γ)
    (registry : Registry Γ) (revelations : Revelations Γ)
    {published name : VarId} {owner : Player} {payload : L.Ty}
    (source : HasVar Γ name (.commitment owner payload))
    (state : State L ((published, .publication payload) :: Γ))
    (failed : ((revelations.reveal (published := published) source)
      (obligation.weaken (x := published)).source).result state = .failure) :
    (Registry.completedBy (published := published) (obligation :: registry)
      revelations source).all
        (·.accepts (revelations.reveal (published := published) source) state) =
      (registry.completedBy (published := published) revelations source).all
        (·.accepts (revelations.reveal (published := published) source) state) := by
  have accepted := (obligation.weaken (x := published)).accepts_of_subject_failure
    (revelations.reveal (published := published) source) state failed
  simp [Registry.completedBy, accepted]

end Vegas.SourceProgram
