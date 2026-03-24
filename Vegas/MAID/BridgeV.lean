import Vegas.MAID.DefsV
import Vegas.PureStrategic
import GameTheory.Languages.MAID.SOS

/-!
# Bridge Theorems for VegasMAID

**Status: sorry'd interfaces — proofs to be filled in later.**

Reverse bridge: any MAID policy reflects to a Vegas behavioral profile with same outcome.
Pure bridge: compiled pure profile → MAID evaluation = Vegas pure evaluation.
-/

namespace Vegas

open MAID

variable {Player : Type} [DecidableEq Player] {L : IExpr} {B : MAIDBackend Player L}

/-! ## Reverse bridge -/

/-- **Reverse bridge**: any MAID policy can be reflected to a Vegas PMF behavioral
profile that produces the same outcome distribution via `frontierEval`. -/
theorem vegasMAID_reverse_bridge
    (B : MAIDBackend Player L) {Γ : VCtx Player L}
    (p : VegasCore Player L Γ) (env : VEnv (Player := Player) L Γ)
    (hl : Legal p) (hd : NormalizedDists p)
    (hfresh : FreshBindings p)
    (hpub : ∀ y who b, VHasVar (L := L) Γ y (.hidden who b) → False)
    (pol : Policy (fp := B.fintypePlayer) (compiledStruct B p env hl hd hfresh hpub)) :
    let S := compiledStruct B p env hl hd hfresh hpub
    let sem := vegasMAIDSem B p env hl hd hfresh hpub
    let σ := reflectPolicyV B p env hl hd hfresh hpub pol
    PMF.map (extractOutcomeV B p env hl hd hfresh hpub)
      (frontierEval (fp := B.fintypePlayer) S sem pol) =
    outcomeDistBehavioralPMF p hd σ env := by
  sorry

/-! ## Pure bridge -/

/-- **Pure bridge**: compiling a Vegas pure profile to a MAID pure policy and
evaluating gives the same outcome distribution as Vegas pure evaluation. -/
theorem vegasMAID_pure_bridge
    (B : MAIDBackend Player L) {Γ : VCtx Player L}
    (p : VegasCore Player L Γ) (env : VEnv (Player := Player) L Γ)
    (hl : Legal p) (hd : NormalizedDists p)
    (hfresh : FreshBindings p)
    (hpub : ∀ y who b, VHasVar (L := L) Γ y (.hidden who b) → False)
    (π : ProgramPureProfile (P := Player) (L := L) p) :
    let S := compiledStruct B p env hl hd hfresh hpub
    let sem := vegasMAIDSem B p env hl hd hfresh hpub
    PMF.map (extractOutcomeV B p env hl hd hfresh hpub)
      (frontierEval (fp := B.fintypePlayer) S sem
        (pureToPolicy (fp := B.fintypePlayer)
          (compilePureProfileV B p env hl hd hfresh hpub π))) =
    (outcomeDistPure p π env).toPMF (outcomeDistPure_totalWeight_eq_one hd) := by
  sorry

end Vegas
