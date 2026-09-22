/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.Basic

/-! # Commitment admission at source sites

Admission describes the source game. It is independent of which preservation
theorem an analysis requests. A site that admits forfeiture lets its owner
irrevocably surrender disclosure; the existing failure-aware core carries that
choice as a failed binding. Publication timing and visibility are unchanged.
-/

namespace Vegas.SourceProgram

inductive CommitmentAdmission where
  | values
  | forfeiture
  deriving DecidableEq

/-- Both interfaces admit every ordinary payload; only the full interface
admits an irrevocably failed binding. -/
def CommitmentAdmission.Admits {α : Type} : CommitmentAdmission → PublicationResult α → Prop
  | _, .success _ => True
  | admission, .failure => admission = .forfeiture

@[simp] theorem CommitmentAdmission.admits_success {α : Type}
    (admission : CommitmentAdmission) (value : α) : admission.Admits (.success value) :=
  trivial

@[simp] theorem CommitmentAdmission.admits_failure {α : Type}
    (admission : CommitmentAdmission) :
    admission.Admits (PublicationResult.failure (α := α)) ↔ admission = .forfeiture :=
  Iff.rfl

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

/-- Structural identities for exactly the commitment sites of a program.
At a commit, `none` is the current site and `some site` belongs to its suffix. -/
abbrev CommitSite : {Γ : SourceCtx Player L} → {O : Finset VarId} →
    SourceProgram Player L Γ O → Type
  | _, _, .ret _ => Empty
  | _, _, .sample _ _ _ next => CommitSite next
  | _, _, .commit _ _ _ _ next => Option (CommitSite next)
  | _, _, .reveal _ _ _ _ _ _ next => CommitSite next

/-- A semantic interface over actual sites, with no runtime handles or
equilibrium-selection flags. -/
abbrev CommitmentInterface {Γ : SourceCtx Player L} {O : Finset VarId}
    (program : SourceProgram Player L Γ O) := CommitSite program → CommitmentAdmission

/-- A structural site has a source name for diagnostics. Looking up arbitrary
strings is not part of the semantic admission interface. -/
def CommitSite.name : {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (program : SourceProgram Player L Γ O) → CommitSite program → VarId
  | _, _, .ret _, impossible => nomatch impossible
  | _, _, .sample _ _ _ next, site => name next site
  | _, _, .commit binding _ _ _ next, site =>
      match site with
      | none => binding
      | some later => name next later
  | _, _, .reveal _ _ _ _ _ _ next, site => name next site

def CommitmentInterface.values {Γ : SourceCtx Player L} {O : Finset VarId}
    (program : SourceProgram Player L Γ O) : CommitmentInterface program := fun _ => .values

def CommitmentInterface.forfeiture {Γ : SourceCtx Player L} {O : Finset VarId}
    (program : SourceProgram Player L Γ O) : CommitmentInterface program := fun _ => .forfeiture

end Vegas.SourceProgram
