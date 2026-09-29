/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheoryExtensions.Analysis.Enforcement

/-! # Undetectable signaling through an allowed public field

Alice and Bob initially share a fair private bit, independently of the secret.
The allowed message has a free Boolean field. Honest use samples that field
independently; signaling writes the secret XOR the shared bit. Every message
is public and uses the same allowed alphabet.

For each secret, both uses induce exactly the same public-message law. Any
randomized monitor seeing the message and even the eventual secret therefore
has the same output law. Bob, who additionally knows the shared bit, recovers
the secret perfectly from the signaling message.

After Bob's guess becomes public the transcript laws differ. Nevertheless,
every signaling transcript also occurs under honest independent guessing. A
randomized monitor with zero false positives on honest complete transcripts
therefore cannot sanction the signaling transcripts either.

The matched observation excludes the shared bit. This is an observation-bound
counterexample for shared initial information and allowed message variation,
not an impossibility of every disclosure policy or conformance mechanism. It
uses no cryptographic computation, private channel, or commitment ownership
restriction. A common public authentication wrapper preserves the law equality.
-/

noncomputable section

namespace GameTheoryExtensionsTests.MonitoredSignaling

open GameTheory.Math.Probability

def fairBit : PMF Bool :=
  mix (1 / 2) (by norm_num) (by norm_num) (PMF.pure false) (PMF.pure true)

/-- The pair records the private shared bit and the public message field. -/
def honest : PMF (Bool × Bool) := bindPairLaw fairBit (fun _ => fairBit)

def signaling (secret : Bool) : PMF (Bool × Bool) :=
  fairBit.map fun pad => (pad, xor secret pad)

def decode (packet : Bool × Bool) : Bool := xor packet.2 packet.1

theorem honest_public_law : honest.map Prod.snd = fairBit := by
  simp only [honest, FinDist.product, PMF.map_bind, PMF.map_comp]
  simp

theorem signaling_public_law (secret : Bool) :
    (signaling secret).map Prod.snd = fairBit := by
  apply pmf_ext_toReal
  intro message
  cases secret <;> cases message <;>
    norm_num [signaling, fairBit, ← PMF.bind_pure_comp, Function.comp_def, mix_bind,
      mix_apply_toReal, toReal_pure_apply]

def honestTranscript (prior : PMF Bool) : PMF (Bool × Bool) :=
  prior.bind fun secret => honest.map fun packet => (secret, packet.2)

def signalingTranscript (prior : PMF Bool) : PMF (Bool × Bool) :=
  prior.bind fun secret => (signaling secret).map fun packet => (secret, packet.2)

/-- The public law agrees jointly with any prior on the eventual disclosed
secret, not merely after forgetting that secret. The shared bit stays private. -/
theorem public_transcript_law (prior : PMF Bool) :
    signalingTranscript prior = honestTranscript prior := by
  apply bind_congr_on_support _
  intro secret _
  change (signaling secret).map ((fun message => (secret, message)) ∘ Prod.snd) =
    honest.map ((fun message => (secret, message)) ∘ Prod.snd)
  rw [← PMF.map_comp, ← PMF.map_comp, signaling_public_law, honest_public_law]

/-- Any randomized monitor of the entire matched observation has the same
output distribution, including monitors that wait until the secret is public. -/
theorem monitor_law {Report : Type*} (prior : PMF Bool)
    (monitor : Bool × Bool → PMF Report) :
    (signalingTranscript prior).bind monitor = (honestTranscript prior).bind monitor := by
  rw [public_transcript_law]

theorem monitor_expectation {Report : Type*} (prior : PMF Bool)
    (monitor : Bool × Bool → PMF Report) (sanction : Report → ℝ) :
    expect ((signalingTranscript prior).bind monitor) sanction =
      expect ((honestTranscript prior).bind monitor) sanction := by
  rw [monitor_law]

/-- A zero-false-positive monitor cannot impose positive expected sanctions
on this signaling use through the specified public observation. -/
theorem sanction_expectation_zero {Report : Type*} (prior : PMF Bool)
    (monitor : Bool × Bool → PMF Report) (sanction : Report → ℝ)
    (honest_zero : expect ((honestTranscript prior).bind monitor) sanction = 0) :
    expect ((signalingTranscript prior).bind monitor) sanction = 0 := by
  rw [monitor_expectation, honest_zero]

theorem decode_signaling (secret pad : Bool) : decode (pad, xor secret pad) = secret := by
  cases secret <;> cases pad <;> rfl

/-- Knowledge of the shared bit changes the receiver's information even though
the monitor's complete observation law is unchanged. -/
theorem signaling_decoded_law (secret : Bool) :
    (signaling secret).map decode = PMF.pure secret := by
  rw [signaling, PMF.map_comp]
  change fairBit.map (fun pad => decode (pad, xor secret pad)) = PMF.pure secret
  simp_rw [decode_signaling]
  exact FinDist.map_const _ _

theorem honest_decoded_law : honest.map decode = fairBit := by
  apply pmf_ext_toReal
  intro guess
  cases guess <;>
    norm_num [honest, decode, fairBit, FinDist.product, ← PMF.bind_pure_comp, Function.comp_def,
      mix_bind, mix_apply_toReal, toReal_pure_apply]

theorem signaling_correct (secret : Bool) :
    expect (signaling secret) (fun packet => if decode packet = secret then (1 : ℝ) else 0) =
      1 := by
  have decoded := congrArg (fun law : PMF Bool =>
    expect law (fun guess => if guess = secret then (1 : ℝ) else 0))
    (signaling_decoded_law secret)
  simpa only [expect_map, expect_pure, ite_true] using decoded

theorem honest_correct (secret : Bool) :
    expect honest (fun packet => if decode packet = secret then (1 : ℝ) else 0) = 1 / 2 := by
  have decoded := congrArg (fun law : PMF Bool =>
    expect law (fun guess => if guess = secret then (1 : ℝ) else 0)) honest_decoded_law
  rw [expect_map] at decoded
  rw [decoded]
  cases secret <;> norm_num [fairBit, FinDist.expect_mix]

/-- Public secret, allowed message field, and Bob's independent honest guess. -/
def honestInteraction (secret : Bool) : PMF (Bool × Bool × Bool) :=
  (bindPairLaw fairBit (fun _ => fairBit)).map fun pair => (secret, pair.1, pair.2)

/-- Bob publicly uses the answer decoded from the message and his private pad. -/
def signalingInteraction (secret : Bool) : PMF (Bool × Bool × Bool) :=
  (signaling secret).map fun packet => (secret, packet.2, decode packet)

theorem honest_interaction_support (secret message guess : Bool) :
    (secret, message, guess) ∈ (honestInteraction secret).support := by
  rw [honestInteraction, PMF.support_map]
  refine ⟨(message, guess), ?_, rfl⟩
  rw [← pmf_toReal_pos_iff, FinDist.prob_product]
  cases message <;> cases guess <;>
    norm_num [fairBit, mix_apply_toReal, toReal_pure_apply]

theorem signaling_interaction_support_subset (secret : Bool) :
    (signalingInteraction secret).support ⊆ (honestInteraction secret).support := by
  intro transcript supported
  rw [signalingInteraction, PMF.support_map] at supported
  obtain ⟨packet, _, rfl⟩ := supported
  exact honest_interaction_support secret packet.2 (decode packet)

/-- The receiver's public action can statistically distinguish the two laws:
honest guessing succeeds half the time, whereas signaling always succeeds. -/
theorem interaction_laws_differ (secret : Bool) :
    signalingInteraction secret ≠ honestInteraction secret := by
  intro same
  let score : Bool × Bool × Bool → ℝ := fun transcript =>
    if transcript.1 = transcript.2.2 then 1 else 0
  have signaling_score : expect (signalingInteraction secret) score = 1 := by
    simpa only [signalingInteraction, expect_map, score, eq_comm] using
      signaling_correct secret
  have honest_score : expect (honestInteraction secret) score = 1 / 2 := by
    cases secret <;>
      norm_num [honestInteraction, expect_map, FinDist.expect_product,
        fairBit, FinDist.expect_mix, score]
  rw [same, honest_score] at signaling_score
  norm_num at signaling_score

/-- Every monitor report possible after signaling is also possible after honest
complete public interaction. This is support inclusion, not equality of laws. -/
theorem interaction_monitor_support_subset {Report : Type*} (secret : Bool)
    (monitor : Bool × Bool × Bool → PMF Report) :
    ((signalingInteraction secret).bind monitor).support ⊆
      ((honestInteraction secret).bind monitor).support := by
  intro report supported
  simp only [PMF.support_bind, Set.mem_iUnion] at supported ⊢
  obtain ⟨transcript, transcript_supported, reported⟩ := supported
  exact ⟨transcript, signaling_interaction_support_subset secret transcript_supported, reported⟩

/-- Even after observing Bob's public guess, a randomized alarm that never
fires on honest transcripts cannot fire on these signaling transcripts. -/
theorem interaction_alarm_zero (secret : Bool)
    (monitor : Bool × Bool × Bool → PMF Bool)
    (no_false_positives : (((honestInteraction secret).bind monitor) true).toReal = 0) :
    (((signalingInteraction secret).bind monitor) true).toReal = 0 :=
  GameTheory.Enforcement.alarm_zero_of_support_subset
    (honestInteraction secret) (signalingInteraction secret)
    (signaling_interaction_support_subset secret) monitor no_false_positives

/-- Honest guesses split equally between the correct and opposite answers;
the correct-answer branch has exactly the signaling public transcript law. -/
theorem honest_interaction_mixture (secret : Bool) :
    honestInteraction secret =
      mix (1 / 2) (by norm_num) (by norm_num) (signalingInteraction secret)
        (fairBit.map fun message => (secret, message, !secret)) := by
  apply pmf_ext_toReal
  rintro ⟨actualSecret, message, guess⟩
  cases secret <;> cases actualSecret <;> cases message <;> cases guess <;>
    norm_num [honestInteraction, signalingInteraction, signaling, decode, fairBit,
      FinDist.product, ← PMF.bind_pure_comp, Function.comp_def, mix_bind, mix_apply_toReal,
      toReal_pure_apply]

/-- With the receiver's action visible, detecting signaling requires accepting
false positives: any nonnegative expected sanction is at most twice its honest
expectation. The monitor may randomize and see the eventual secret as well. -/
theorem interaction_sanction_le_twice_honest {Report : Type*} (secret : Bool)
    (monitor : Bool × Bool × Bool → PMF Report) (sanction : Report → ℝ)
    (nonnegative : ∀ report, 0 ≤ sanction report) :
    expect ((signalingInteraction secret).bind monitor) sanction ≤
      2 * expect ((honestInteraction secret).bind monitor) sanction := by
  have opposite_nonnegative :
      0 ≤ expect ((fairBit.map fun message => (secret, message, !secret)).bind monitor)
        sanction := by
    have bound := FinDist.expect_mono
      (μ := (fairBit.map fun message => (secret, message, !secret)).bind monitor)
      (fun report _ => nonnegative report)
    simpa only [expect_constant] using bound
  rw [honest_interaction_mixture, mix_bind, FinDist.expect_mix]
  linarith

end GameTheoryExtensionsTests.MonitoredSignaling
