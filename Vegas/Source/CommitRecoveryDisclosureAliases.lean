/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Source.DisclosureAliases
import Vegas.Source.CommitRecoveryStep

/-! # Effective disclosure aliases in the recovery source -/

noncomputable section

namespace Vegas.SourceProgram

open GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr}

/-- Replacing an intention by its effective disclosure preserves the entire
typed successor and every other player's complete observation. The owner's
private action history is retained as a distinct record. -/
theorem effective_reveal_observations
    {Γ : SourceCtx Player L} {published name : VarId} {owner : Player} {payload : L.Ty}
    (selected : HasVar Γ name (.commitment owner payload)) (config : Config Player L Γ)
    (disclose : Bool) :
    (revealSuccessor published selected config
        (effectiveDisclosure published selected config disclose)).state =
        (revealSuccessor published selected config disclose).state ∧
      ∀ who, who ≠ owner →
        (revealSuccessor published selected config
            (effectiveDisclosure published selected config disclose)).view who =
          (revealSuccessor published selected config disclose).view who := by
  have same : (revealSuccessor published selected config
      (effectiveDisclosure published selected config disclose)).state =
        (revealSuccessor published selected config disclose).state := by
    change Env.cons (Val := CellVal (Player := Player) L) (x := published)
        (τ := .publication payload)
        (disclosureResult published selected config
          (effectiveDisclosure published selected config disclose)) config.state =
      Env.cons (Val := CellVal (Player := Player) L) (x := published) (τ := .publication payload)
        (disclosureResult published selected config disclose) config.state
    rw [disclosureResult_effectiveDisclosure]
  refine ⟨same, ?_⟩
  intro who other
  apply Prod.ext
  · exact congrArg (sourceObserve who) same
  · simp only [Config.view, revealSuccessor, Function.update_of_ne other]

variable [IExpr.ResultTypes L]

/-- Both an ineffective disclosure and withholding exclude the owner in the
actual original source kernel, before its install/close operation. This covers
rejected guards and failed bindings without equating the owner's intention. -/
theorem ineffective_reveal_excludes
    {Γ : SourceCtx Player L} {O : Finset VarId} {published name : VarId}
    {owner : Player} {payload : L.Ty}
    (fresh : published ∉ Γ.map Prod.fst)
    (selected : HasVar Γ name (.commitment owner payload)) (unresolved : name ∈ O)
    (suffix : SourceProgram Player L ((published, .publication payload) :: Γ) (O.erase name))
    (config : Config Player L Γ)
    (rejected : disclosureResult published selected config true = .failure)
    (excluded : Finset Player) (joint : Player → Option (CommitRecoveryMove Player L))
    (result : ProtocolState (.reveal published owner name fresh selected unresolved suffix) ×
      Finset Player)
    (supported : result ∈ (ProtocolState.recoveryStep
      (.reveal published owner name fresh selected unresolved suffix) (.inl config) excluded
        joint).support) : owner ∈ result.2 := by
  have failed (disclose : Bool) :
      (revealSuccessor published selected config disclose).state.get .here = .failure := by
    cases disclose with
    | false => exact disclosureResult_false published selected config
    | true => exact rejected
  simp only [ProtocolState.recoveryStep, Sum.elim_inl, failed, PMF.mem_support_pure_iff]
    at supported
  cases supported
  exact Finset.mem_insert_self ..

end Vegas.SourceProgram
