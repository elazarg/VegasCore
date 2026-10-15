/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.ProtocolSuffix
import Vegas.Source.ProtocolBehavioralPolicy

/-! # The actual structural policy at a syntactic recovery suffix -/

noncomputable section

namespace Vegas.SourceProgram.ProtocolSuffix

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {wholeΓ Γ : SourceCtx Player L} {wholeO O : Finset VarId}
  {whole : SourceProgram Player L wholeΓ wholeO} {program : SourceProgram Player L Γ O}
  {lift : ProtocolState program → ProtocolState whole}

/-- Following actual source constructors restricts the existing whole policy.
The residual kernel is evaluated at the lifted whole view at every source point. -/
theorem exists_behavioralProfile (origin : ProtocolSuffix whole program lift)
    (profile : BehavioralProfile whole) :
    ∃ residual : BehavioralProfile program, ∀ who point,
      (residual who).protocolAction program (ProtocolState.observe who program point) =
        (profile who).protocolAction whole (ProtocolState.observe who whole (lift point)) := by
  induction origin with
  | initial => exact ⟨profile, fun _ _ => rfl⟩
  | sampleTail fresh law next _origin ih =>
      obtain ⟨prior, same⟩ := ih
      exact ⟨afterSample prior, fun who point => same who (.inr point)⟩
  | commitTail fresh guard next _origin ih =>
      obtain ⟨prior, same⟩ := ih
      exact ⟨afterCommit prior, fun who point => same who (.inr point)⟩
  | revealTail fresh selected unresolved next _origin ih =>
      obtain ⟨prior, same⟩ := ih
      exact ⟨afterReveal prior, fun who point => same who (.inr point)⟩

end Vegas.SourceProgram.ProtocolSuffix
