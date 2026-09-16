/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Mathlib.Data.Fintype.Pi

/-! # Deferred relational guards and write-once publications

An ordinary value, a resolved failure, and an unresolved obligation are distinct.
Guards consume only ordinary values. A failed dependency discharges a guard
vacuously. Publishing a value checks the relations it closes; a rejected check
fails the current publication, never a previously published dependency.

This is a finite-obligation source-semantics component, not a byte-level protocol
or compiler theorem. Guard functions here are semantic; an executable target
must retain and implement their code and authenticate publication inputs.
-/

namespace Interaction

universe u v w

/-- Resolution status of one typed publication. Failure is outside `A`. -/
inductive Publication (A : Type v) where
  | pending
  | failed
  | value (data : A)
  deriving DecidableEq

namespace Publication

variable {A : Type v}

def isPending : Publication A → Bool
  | .pending => true
  | .failed | .value _ => false

def isFailed : Publication A → Bool
  | .failed => true
  | .pending | .value _ => false

def hasValue : Publication A → Bool
  | .value _ => true
  | .pending | .failed => false

def get : (publication : Publication A) → publication.hasValue = true → A
  | .value data, _ => data
  | .pending, impossible => False.elim (Bool.false_ne_true impossible)
  | .failed, impossible => False.elim (Bool.false_ne_true impossible)

/-- `none` is a resolved failure, not an unresolved obligation. -/
def ofOption : Option A → Publication A
  | none => .failed
  | some data => .value data

@[simp] theorem isPending_eq_true (publication : Publication A) :
    publication.isPending = true ↔ publication = .pending := by
  cases publication <;> simp [isPending]

@[simp] theorem ofOption_ne_pending (data : Option A) :
    ofOption data ≠ .pending := by
  cases data <;> simp [ofOption]

end Publication

/-- Values may have a different type at each publication site. -/
abbrev PublicationStore {Slot : Type u} (Value : Slot → Type v) :=
  (slot : Slot) → Publication (Value slot)

namespace PublicationStore

variable {Slot : Type u} {Value : Slot → Type v}

def empty : PublicationStore Value := fun _ => .pending

def write [DecidableEq Slot] (state : PublicationStore Value)
    (site : Slot) (result : Publication (Value site)) : PublicationStore Value :=
  fun slot => if equal : site = slot then equal ▸ result else state slot

@[simp] theorem write_self [DecidableEq Slot] (state : PublicationStore Value)
    (site : Slot) (result : Publication (Value site)) :
    state.write site result site = result := by
  simp [write]

@[simp] theorem write_other [DecidableEq Slot] (state : PublicationStore Value)
    (site slot : Slot) (result : Publication (Value site)) (different : site ≠ slot) :
    state.write site result slot = state slot := by
  simp [write, different]

/-- Final values and failures are preserved; only pending sites may change. -/
def Extends (before after : PublicationStore Value) : Prop :=
  ∀ site, before site ≠ .pending → after site = before site

theorem Extends.refl (state : PublicationStore Value) : state.Extends state :=
  fun _ _ => rfl

theorem Extends.trans {first second third : PublicationStore Value}
    (left : first.Extends second) (right : second.Extends third) : first.Extends third := by
  intro site resolved
  rw [right site (by rw [left site resolved]; exact resolved), left site resolved]

theorem extends_write [DecidableEq Slot] (state : PublicationStore Value)
    (site : Slot) (result : Publication (Value site)) (pending : state site = .pending) :
    state.Extends (state.write site result) := by
  intro other resolved
  have different : site ≠ other := by
    intro equal
    subst other
    exact resolved pending
  exact write_other state site other result different

/-- A partial publication of one ordinary assignment, with no failures. -/
def Compatible (state : PublicationStore Value) (values : (site : Slot) → Value site) : Prop :=
  ∀ site, state site = .pending ∨ state site = .value (values site)

theorem compatible_empty (values : (site : Slot) → Value site) :
    Compatible empty values := fun _ => Or.inl rfl

theorem Compatible.write [DecidableEq Slot] {state : PublicationStore Value}
    {values : (site : Slot) → Value site} (compatible : state.Compatible values) (site : Slot) :
    (state.write site (.value (values site))).Compatible values := by
  intro other
  by_cases same : site = other
  · subst other
    exact Or.inr (write_self _ _ _)
  · rw [write_other _ _ _ _ same]
    exact compatible other

end PublicationStore

/-- A retained relation over ordinary typed values. The declared subject is
included even for a constant guard, so its failure always discharges the guard. -/
structure PublicationGuard {Slot : Type u} (Value : Slot → Type v) where
  subject : Slot
  dependencies : Finset Slot
  subject_mem : subject ∈ dependencies
  test : ((slot : dependencies) → Value slot) → Bool

namespace PublicationGuard

variable {Slot : Type u} {Value : Slot → Type v}

inductive Verdict where
  | pending
  | satisfied
  | rejected
  deriving DecidableEq

/-- No ordinary guard is called on pending or failed data. -/
def checkReads (guard : PublicationGuard Value)
    (reads : (slot : guard.dependencies) → Publication (Value slot)) : Verdict :=
  if ∃ slot, (reads slot).isFailed = true then .satisfied
  else if ready : ∀ slot, (reads slot).hasValue = true then
    if guard.test (fun slot => (reads slot).get (ready slot)) then .satisfied else .rejected
  else .pending

def check (guard : PublicationGuard Value) (state : PublicationStore Value) : Verdict :=
  guard.checkReads fun slot => state slot

theorem check_congr (guard : PublicationGuard Value) (left right : PublicationStore Value)
    (agree : ∀ site ∈ guard.dependencies, left site = right site) :
    guard.check left = guard.check right := by
  apply congrArg guard.checkReads
  funext site
  exact agree site site.property

theorem check_of_failed (guard : PublicationGuard Value) (state : PublicationStore Value)
    (site : Slot) (member : site ∈ guard.dependencies) (failed : state site = .failed) :
    guard.check state = .satisfied := by
  have witness : ∃ slot : guard.dependencies, (state slot).isFailed = true :=
    ⟨⟨site, member⟩, by simp [failed, Publication.isFailed]⟩
  simp [check, checkReads, witness]

theorem check_empty (guard : PublicationGuard Value) :
    guard.check PublicationStore.empty = .pending := by
  have notReady : ¬ ∀ slot : guard.dependencies,
      (PublicationStore.empty (Value := Value) slot).hasValue = true := by
    intro ready
    simpa [PublicationStore.empty, Publication.hasValue] using
      ready ⟨guard.subject, guard.subject_mem⟩
  unfold check checkReads
  rw [if_neg (by simp [PublicationStore.empty, Publication.isFailed]), dif_neg notReady]

/-- A guard cannot reject before its own subject has resolved. A failed
dependency may already discharge it; otherwise the pending subject keeps the
guard waiting. -/
theorem check_ne_rejected_of_subject_pending (guard : PublicationGuard Value)
    (state : PublicationStore Value) (pending : state guard.subject = .pending) :
    guard.check state ≠ .rejected := by
  unfold check checkReads
  split
  · decide
  · next noFailure =>
      split
      · next ready =>
          have subjectReady := ready ⟨guard.subject, guard.subject_mem⟩
          simp [pending, Publication.hasValue] at subjectReady
      · decide

/-- A fully ordinary publication evaluates precisely the ordinary relation. -/
theorem check_values (guard : PublicationGuard Value) (values : (site : Slot) → Value site) :
    guard.check (fun site => .value (values site)) =
      if guard.test (fun site => values site) then .satisfied else .rejected := by
  simp [check, checkReads, Publication.isFailed, Publication.hasValue, Publication.get]

/-- Once every declared dependency has resolved, the guard no longer waits.
An invalid dependency discharges the relation without providing a value. -/
theorem check_ne_pending_of_resolved (guard : PublicationGuard Value)
    (state : PublicationStore Value)
    (resolved : ∀ site ∈ guard.dependencies, state site ≠ .pending) :
    guard.check state ≠ .pending := by
  unfold check checkReads
  split
  · decide
  · next noFailure =>
      have ordinary : ∀ site : guard.dependencies, (state site).hasValue = true := by
        intro site
        cases current : state site with
        | pending => exact False.elim (resolved site site.property current)
        | failed =>
            exact False.elim (noFailure ⟨site, by simp [current, Publication.isFailed]⟩)
        | value value => rfl
      rw [dif_pos ordinary]
      split <;> decide

/-- A partial disclosure of a satisfying assignment cannot reject its guard. -/
theorem check_compatible (guard : PublicationGuard Value) (state : PublicationStore Value)
    (values : (site : Slot) → Value site) (compatible : state.Compatible values)
    (valid : guard.test (fun site => values site) = true) : guard.check state ≠ .rejected := by
  have noFailure : ¬ ∃ slot : guard.dependencies, (state slot).isFailed = true := by
    rintro ⟨slot, failed⟩
    rcases compatible slot with pending | ordinary
    · simp [pending, Publication.isFailed] at failed
    · simp [ordinary, Publication.isFailed] at failed
  by_cases ready : ∀ slot : guard.dependencies, (state slot).hasValue = true
  · have agree : ∀ site ∈ guard.dependencies, state site = .value (values site) := by
      intro site member
      rcases compatible site with pending | ordinary
      · have impossible := ready ⟨site, member⟩
        simp [pending, Publication.hasValue] at impossible
      · exact ordinary
    rw [guard.check_congr state (fun site => .value (values site)) agree,
      guard.check_values, valid]
    decide
  · unfold check checkReads
    rw [if_neg noFailure, dif_neg ready]
    decide

theorem check_write_of_not_mem [DecidableEq Slot] (guard : PublicationGuard Value)
    (state : PublicationStore Value) (site : Slot) (result : Publication (Value site))
    (outside : site ∉ guard.dependencies) :
    guard.check (state.write site result) = guard.check state := by
  apply guard.check_congr
  intro other member
  exact PublicationStore.write_other state site other result
    (fun equal => outside (equal ▸ member))

/-- Once satisfied, a guard remains satisfied as write-once publication state
extends. This covers both an immutable failed dependency and a fully resolved
ordinary satisfying tuple. -/
theorem check_satisfied_of_extends (guard : PublicationGuard Value)
    (before after : PublicationStore Value) (extension : before.Extends after)
    (satisfied : guard.check before = .satisfied) : guard.check after = .satisfied := by
  by_cases failed : ∃ slot : guard.dependencies, (before slot).isFailed = true
  · obtain ⟨slot, hfailed⟩ := failed
    have hstate : before slot = .failed := by
      cases hpublication : before slot <;> simp_all [Publication.isFailed]
    have hafter := extension slot (by simp [hstate])
    exact guard.check_of_failed after slot slot.property (hafter.trans hstate)
  · have ready : ∀ slot : guard.dependencies, (before slot).hasValue = true := by
      unfold check checkReads at satisfied
      rw [if_neg failed] at satisfied
      split at satisfied
      · assumption
      · contradiction
    apply (guard.check_congr before after ?_).symm.trans satisfied
    intro site member
    apply (extension site ?_).symm
    have := ready ⟨site, member⟩
    cases hpublication : before site <;> simp_all [Publication.hasValue]

/-- A guard can only newly reject a publication in its own declared support. -/
theorem mem_of_new_rejection [DecidableEq Slot] (guard : PublicationGuard Value)
    (state : PublicationStore Value) (site : Slot) (result : Publication (Value site))
    (previous : guard.check state ≠ .rejected)
    (rejected : guard.check (state.write site result) = .rejected) :
    site ∈ guard.dependencies := by
  by_contra outside
  rw [guard.check_write_of_not_mem state site result outside] at rejected
  exact previous rejected

/-- Source visibility can establish this at guard creation: all unresolved
inputs belong to the guard author; foreign inputs are already public. -/
def OwnedPending {Player : Type w} (guard : PublicationGuard Value)
    (owner : Slot → Player) (state : PublicationStore Value) : Prop :=
  ∀ site ∈ guard.dependencies, state site = .pending → owner site = owner guard.subject

theorem OwnedPending.mono {Player : Type w} {guard : PublicationGuard Value}
    {owner : Slot → Player} {before after : PublicationStore Value}
    (owned : guard.OwnedPending owner before) (extension : before.Extends after) :
    guard.OwnedPending owner after := by
  intro site member pending
  apply owned site member
  by_contra resolved
  rw [extension site resolved] at pending
  exact resolved pending

theorem rejection_owner [DecidableEq Slot] {Player : Type w}
    (guard : PublicationGuard Value) (owner : Slot → Player) (state : PublicationStore Value)
    (site : Slot) (result : Publication (Value site))
    (owned : guard.OwnedPending owner state) (pending : state site = .pending)
    (previous : guard.check state ≠ .rejected)
    (rejected : guard.check (state.write site result) = .rejected) :
    owner site = owner guard.subject :=
  owned site (guard.mem_of_new_rejection state site result previous rejected) pending

end PublicationGuard

/-- A finite family of deferred relational obligations. -/
structure GuardedPublication {Slot : Type u} (Value : Slot → Type v) where
  guards : List (PublicationGuard Value)

namespace GuardedPublication

variable {Slot : Type u} {Value : Slot → Type v}

def Consistent (protocol : GuardedPublication Value) (state : PublicationStore Value) : Prop :=
  ∀ guard ∈ protocol.guards, guard.check state ≠ .rejected

/-- Add one deferred obligation at its source declaration point. -/
def register (protocol : GuardedPublication Value) (guard : PublicationGuard Value) :
    GuardedPublication Value :=
  ⟨protocol.guards ++ [guard]⟩

/-- Registering an obligation whose subject is still pending preserves an
already consistent publication prefix. -/
theorem register_consistent_of_subject_pending (protocol : GuardedPublication Value)
    (guard : PublicationGuard Value) (state : PublicationStore Value)
    (consistent : protocol.Consistent state) (pending : state guard.subject = .pending) :
    (protocol.register guard).Consistent state := by
  intro candidate member
  simp only [register, List.mem_append, List.mem_singleton] at member
  rcases member with old | added
  · exact consistent candidate old
  · subst candidate
    exact guard.check_ne_rejected_of_subject_pending state pending

def consistent? (protocol : GuardedPublication Value) (state : PublicationStore Value) : Bool :=
  protocol.guards.all fun guard => guard.check state != .rejected

@[simp] theorem consistent?_eq_true (protocol : GuardedPublication Value)
    (state : PublicationStore Value) : protocol.consistent? state = true ↔
      protocol.Consistent state := by
  simp [consistent?, Consistent, List.all_eq_true]

theorem consistent_empty (protocol : GuardedPublication Value) :
    protocol.Consistent PublicationStore.empty := by
  intro guard _member
  simp [guard.check_empty]

/-- Nonvacuous feasibility: an ordinary assignment satisfies all relations. -/
def Satisfies (protocol : GuardedPublication Value) (values : (site : Slot) → Value site) : Prop :=
  ∀ guard ∈ protocol.guards, guard.test (fun site => values site) = true

/-- Complete publication accounting strengthens consistency to discharge of
every registered obligation. Discharge includes null-vacuous satisfaction;
it does not assert an ordinary satisfying assignment. -/
theorem satisfied_of_resolved (protocol : GuardedPublication Value)
    (state : PublicationStore Value) (consistent : protocol.Consistent state)
    (resolved : ∀ guard ∈ protocol.guards,
      ∀ site ∈ guard.dependencies, state site ≠ .pending) :
    ∀ guard ∈ protocol.guards, guard.check state = .satisfied := by
  intro guard member
  have notRejected := consistent guard member
  have notPending := guard.check_ne_pending_of_resolved state (resolved guard member)
  cases verdict : guard.check state with
  | pending => exact False.elim (notPending verdict)
  | satisfied => rfl
  | rejected => exact False.elim (notRejected verdict)

theorem consistent_of_compatible (protocol : GuardedPublication Value)
    (state : PublicationStore Value) (values : (site : Slot) → Value site)
    (compatible : state.Compatible values) (valid : protocol.Satisfies values) :
    protocol.Consistent state := by
  intro guard member
  exact guard.check_compatible state values compatible (valid guard member)

/-- Resolve the current site. A failed check fails this site, without revising
earlier values. Calls at an already resolved site are idempotent. -/
def resolve [DecidableEq Slot] (protocol : GuardedPublication Value)
    (state : PublicationStore Value) (site : Slot) (candidate : Option (Value site)) :
    PublicationStore Value :=
  if (state site).isPending then
    let proposed := state.write site (Publication.ofOption candidate)
    if protocol.consistent? proposed then proposed else state.write site .failed
  else state

theorem consistent_failed [DecidableEq Slot] (protocol : GuardedPublication Value)
    (state : PublicationStore Value) (site : Slot) (consistent : protocol.Consistent state) :
    protocol.Consistent (state.write site .failed) := by
  intro guard member
  by_cases depends : site ∈ guard.dependencies
  · rw [guard.check_of_failed _ site depends (PublicationStore.write_self _ _ _)]
    decide
  · rw [guard.check_write_of_not_mem state site .failed depends]
    exact consistent guard member

theorem resolve_consistent [DecidableEq Slot] (protocol : GuardedPublication Value)
    (state : PublicationStore Value) (site : Slot) (candidate : Option (Value site))
    (consistent : protocol.Consistent state) :
    protocol.Consistent (protocol.resolve state site candidate) := by
  unfold resolve
  split
  · dsimp only
    split
    · exact (protocol.consistent?_eq_true _).mp (by assumption)
    · exact protocol.consistent_failed state site consistent
  · exact consistent

theorem resolve_extends [DecidableEq Slot] (protocol : GuardedPublication Value)
    (state : PublicationStore Value) (site : Slot) (candidate : Option (Value site)) :
    state.Extends (protocol.resolve state site candidate) := by
  unfold resolve
  split
  · next pending =>
      have pending' : state site = .pending := (Publication.isPending_eq_true _).mp pending
      dsimp only
      split <;> exact state.extends_write site _ pending'
  · exact PublicationStore.Extends.refl state

theorem resolve_of_resolved [DecidableEq Slot] (protocol : GuardedPublication Value)
    (state : PublicationStore Value) (site : Slot) (candidate : Option (Value site))
    (resolved : state site ≠ .pending) : protocol.resolve state site candidate = state := by
  simp [resolve, resolved]

theorem resolve_other [DecidableEq Slot] (protocol : GuardedPublication Value)
    (state : PublicationStore Value) (site other : Slot) (candidate : Option (Value site))
    (different : site ≠ other) : protocol.resolve state site candidate other = state other := by
  unfold resolve
  split
  · dsimp only
    split <;> exact state.write_other site other _ different
  · rfl

/-- Explicit failure always resolves a pending site, regardless of its payload domain. -/
theorem resolve_none [DecidableEq Slot] (protocol : GuardedPublication Value)
    (state : PublicationStore Value) (site : Slot) (pending : state site = .pending) :
    protocol.resolve state site none = state.write site .failed := by
  simp [resolve, pending, Publication.isPending, Publication.ofOption]

/-- An opening which resolves as failure has the same logical state effect as
non-disclosing failure. This does not identify their message observations. -/
theorem resolve_eq_none_of_failed [DecidableEq Slot] (protocol : GuardedPublication Value)
    (state : PublicationStore Value) (site : Slot) (candidate : Option (Value site))
    (failed : protocol.resolve state site candidate site = .failed) :
    protocol.resolve state site candidate = protocol.resolve state site none := by
  cases candidate with
  | none => rfl
  | some value =>
      by_cases pending : state site = .pending
      · rw [protocol.resolve_none state site pending]
        by_cases accepted : protocol.consistent? (state.write site (.value value)) = true
        · simp [resolve, pending, Publication.isPending, Publication.ofOption, accepted] at failed
        · simp [resolve, pending, Publication.isPending, Publication.ofOption, accepted]
      · rw [protocol.resolve_of_resolved state site _ pending,
          protocol.resolve_of_resolved state site _ pending]

theorem resolve_site_resolved [DecidableEq Slot] (protocol : GuardedPublication Value)
    (state : PublicationStore Value) (site : Slot) (candidate : Option (Value site)) :
    protocol.resolve state site candidate site ≠ .pending := by
  unfold resolve
  split
  · dsimp only
    split <;> simp
  · next resolved =>
      simpa using resolved

theorem resolve_idempotent [DecidableEq Slot] (protocol : GuardedPublication Value)
    (state : PublicationStore Value) (site : Slot) (first second : Option (Value site)) :
    protocol.resolve (protocol.resolve state site first) site second =
      protocol.resolve state site first :=
  protocol.resolve_of_resolved _ site second (protocol.resolve_site_resolved state site first)

/-- An honestly feasible ordinary disclosure is accepted as that same value. -/
theorem resolve_compatible [DecidableEq Slot] (protocol : GuardedPublication Value)
    (state : PublicationStore Value) (values : (site : Slot) → Value site) (site : Slot)
    (compatible : state.Compatible values) (valid : protocol.Satisfies values) :
    protocol.resolve state site (some (values site)) = state.write site (.value (values site)) := by
  have accepted := protocol.consistent_of_compatible _ values (compatible.write site) valid
  rcases compatible site with pending | ordinary
  · simp [resolve, pending, Publication.isPending, Publication.ofOption, accepted]
  · rw [protocol.resolve_of_resolved state site _ (by simp [ordinary])]
    funext other
    by_cases same : site = other
    · subst other
      simpa using ordinary
    · simp [PublicationStore.write_other _ _ _ _ same]

/-- Resolve a finite list of fixed publication inputs. This is a deterministic
state transformer, not a separate strategy or message runner. -/
def run [DecidableEq Slot] (protocol : GuardedPublication Value) (state : PublicationStore Value) :
    List ((site : Slot) × Option (Value site)) → PublicationStore Value
  | [] => state
  | input :: rest => protocol.run (protocol.resolve state input.1 input.2) rest

theorem run_consistent [DecidableEq Slot] (protocol : GuardedPublication Value)
    (inputs : List ((site : Slot) × Option (Value site))) (state : PublicationStore Value)
    (consistent : protocol.Consistent state) : protocol.Consistent (protocol.run state inputs) := by
  induction inputs generalizing state with
  | nil => exact consistent
  | cons input rest induction =>
      exact induction _ (protocol.resolve_consistent state input.1 input.2 consistent)

theorem run_extends [DecidableEq Slot] (protocol : GuardedPublication Value)
    (inputs : List ((site : Slot) × Option (Value site))) (state : PublicationStore Value) :
    state.Extends (protocol.run state inputs) := by
  induction inputs generalizing state with
  | nil => exact PublicationStore.Extends.refl state
  | cons input rest induction =>
      exact (protocol.resolve_extends state input.1 input.2).trans (induction _)

theorem run_site_resolved [DecidableEq Slot] (protocol : GuardedPublication Value)
    (inputs : List ((site : Slot) × Option (Value site))) (state : PublicationStore Value)
    (input : (site : Slot) × Option (Value site)) (member : input ∈ inputs) :
    protocol.run state inputs input.1 ≠ .pending := by
  induction inputs generalizing state with
  | nil => simp at member
  | cons first rest induction =>
      rcases List.mem_cons.mp member with same | later
      · subst first
        have resolved := protocol.resolve_site_resolved state input.1 input.2
        exact fun pending => resolved
          ((protocol.run_extends rest _ input.1 resolved).symm.trans pending)
      · exact induction _ later

/-- Publishing any prefix of a satisfying assignment never introduces failure. -/
theorem run_compatible [DecidableEq Slot] (protocol : GuardedPublication Value)
    (sites : List Slot) (state : PublicationStore Value) (values : (site : Slot) → Value site)
    (compatible : state.Compatible values) (valid : protocol.Satisfies values) :
    (protocol.run state (sites.map fun site => ⟨site, some (values site)⟩)).Compatible values := by
  induction sites generalizing state with
  | nil => exact compatible
  | cons site rest induction =>
      simp only [List.map_cons, run, protocol.resolve_compatible state values site compatible valid]
      exact induction _ (compatible.write site)

/-- A complete ordinary satisfying assignment is published in any prescribed
order, without failures. No arbitrary-order equivalence is asserted for invalid inputs. -/
theorem run_honest_complete [DecidableEq Slot] (protocol : GuardedPublication Value)
    (sites : List Slot) (covers : ∀ site, site ∈ sites) (values : (site : Slot) → Value site)
    (valid : protocol.Satisfies values) :
    protocol.run PublicationStore.empty (sites.map fun site => ⟨site, some (values site)⟩) =
      fun site => .value (values site) := by
  have compatible := protocol.run_compatible sites _ values
    (PublicationStore.compatible_empty values) valid
  funext site
  rcases compatible site with pending | ordinary
  · exact False.elim (protocol.run_site_resolved _ _ ⟨site, some (values site)⟩
      (List.mem_map.mpr ⟨site, covers site, rfl⟩) pending)
  · exact ordinary

end GuardedPublication

end Interaction
