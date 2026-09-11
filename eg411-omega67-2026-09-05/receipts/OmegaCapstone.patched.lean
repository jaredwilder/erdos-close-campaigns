import Mathlib
import OmegaLadder
import OmegaTree5
import RealResult

/-!
# EG#411 (r=2): the ω-capstone — classification below five prime factors (2026-06-10)

This file glues the structural ladder (`SolutionStructure.lean`, `OmegaLadder.lean`) to the
conditional-closure apparatus (`RealResult.lean`):

  • `solution_omega_le_four_classified` — every solution of `3·φ(n) = 2n + 2` with
    `ω(n) ≤ 4` is one of `5, 35, 1295, 1679615`.
  • `WeakTotientHypothesis` — the (strictly weaker) hypothesis that every solution has
    `ω(n) ≤ 4`; `weak_implies_conjecture` upgrades it to Steinerberger's full conjecture.
  • `eg411_r2_conditional_closure_sharp` — conditional closure of EG#411 r=2 from the
    weak hypothesis alone: the exceptional primes are exactly `{7, 47}`.
  • `exceptional_high_omega` — **the unconditional headline**: every EG#411 exceptional
    prime other than `7` and `47` comes from a solution `N` with **at least five distinct
    prime factors**.

Proof of the classification: solutions are squarefree (`solution_squarefree`), so
`n = ∏ p ∈ n.primeFactors, p`; cases on `ω(n) ∈ {0, 1, 2, 3, 4}` feed the sorted prime
tuple to `solution_prime_eq_five` / `solution_two_primes` / `solution_three_primes` /
`solution_four_primes`. For `ω(n) = 4` the minimum prime is split off via `Finset.min'`,
reducing the 24 orderings of four elements to the 6 orderings of three.

The compositeness of the two non-prime candidates `(4·1295+1)/3 = 1727 = 11·157` and
`(4·1679615+1)/3 = 2239487 = 23·97369` is witnessed by explicit divisors, so sections
1–3 — including `exceptional_high_omega` — are fully axiom-free: every theorem there
reports only `{propext, Classical.choice, Quot.sound}` (no `native_decide`, no
project-local axiom).

**Section 4 (2026-06-10)** pushes the ladder one rung higher via the certified ω = 5
kill-tree (`OmegaTree5.lean`):

  • `solution_omega_le_five_classified` — every solution with `ω(n) ≤ 5` is one of
    `5, 35, 1295, 1679615` (the ω = 5 stratum is empty by `omega5_empty`).
  • `exceptional_high_omega_six` — **the strengthened unconditional headline**: every
    EG#411 exceptional prime other than `7` and `47` comes from a solution `N` with
    **at least six distinct prime factors**.
  • `WeakTotientHypothesis5` / `eg411_r2_conditional_closure_sharp5` — the conditional
    closure now needs only the (strictly weaker) bound `ω ≤ 5` on solutions.

Axiom footprint of section 4: `{propext, Classical.choice, Quot.sound}` plus the 33
per-call-site `native_decide` compiler-trust axioms inherited from
`EG411Structure.omega5_empty` (`omega5_empty._native.native_decide.ax_1_*`); no `sorry`,
no project-local axiom. `weak_implies_weak5` alone is native-free.
-/

namespace EG411Capstone

open EG411Structure

/-! ## 1. Classification of all solutions with at most four prime factors -/

/-- Every solution of `3·φ(n) = 2n + 2` with at most four distinct prime factors is one
of the four known solutions `5`, `35`, `1295 = 5·7·37`, `1679615 = 5·7·37·1297`. -/
theorem solution_omega_le_four_classified (n : ℕ)
    (hn : 3 * Nat.totient n = 2 * n + 2) (hcard : n.primeFactors.card ≤ 4) :
    n = 5 ∨ n = 35 ∨ n = 1295 ∨ n = 1679615 := by
  have hsf : Squarefree n := solution_squarefree hn
  have hprod : ∏ p ∈ n.primeFactors, p = n := Nat.prod_primeFactors_of_squarefree hsf
  have h04 : n.primeFactors.card = 0 ∨ n.primeFactors.card = 1 ∨
      n.primeFactors.card = 2 ∨ n.primeFactors.card = 3 ∨ n.primeFactors.card = 4 := by
    omega
  rcases h04 with h | h | h | h | h
  · -- ω(n) = 0: n ∈ {0, 1}, neither satisfies the equation.
    exfalso
    rcases Nat.primeFactors_eq_empty.mp (Finset.card_eq_zero.mp h) with rfl | rfl
    · rw [Nat.totient_zero] at hn; omega
    · rw [Nat.totient_one] at hn; omega
  · -- ω(n) = 1: n is prime (squarefree with a single prime factor), so n = 5.
    obtain ⟨p, hp⟩ := Finset.card_eq_one.mp h
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors (by rw [hp]; simp)
    rw [hp, Finset.prod_singleton] at hprod
    exact Or.inl (solution_prime_eq_five hn (hprod ▸ hpp))
  · -- ω(n) = 2: n = a·b with a ≠ b primes, so n = 35.
    obtain ⟨a, b, hab, hs⟩ := Finset.card_eq_two.mp h
    have hpa : a.Prime := Nat.prime_of_mem_primeFactors (by rw [hs]; simp)
    have hpb : b.Prime := Nat.prime_of_mem_primeFactors (by rw [hs]; simp)
    rw [hs, Finset.prod_insert (by simp [hab]), Finset.prod_singleton] at hprod
    -- hprod : a * b = n
    refine Or.inr (Or.inl ?_)
    rcases lt_trichotomy a b with hlt | heq | hlt
    · exact solution_two_primes hn a b hpa hpb hlt (by rw [← hprod])
    · exact absurd heq hab
    · exact solution_two_primes hn b a hpb hpa hlt (by rw [← hprod]; try ring)
  · -- ω(n) = 3: sort the three primes and feed the ladder, so n = 1295.
    obtain ⟨a, b, c, hab, hac, hbc, hs⟩ := Finset.card_eq_three.mp h
    have hpa : a.Prime := Nat.prime_of_mem_primeFactors (by rw [hs]; simp)
    have hpb : b.Prime := Nat.prime_of_mem_primeFactors (by rw [hs]; simp)
    have hpc : c.Prime := Nat.prime_of_mem_primeFactors (by rw [hs]; simp)
    rw [hs, Finset.prod_insert (by simp [hab, hac]), Finset.prod_insert (by simp [hbc]),
        Finset.prod_singleton] at hprod
    -- hprod : a * (b * c) = n
    refine Or.inr (Or.inr (Or.inl ?_))
    have L := solution_three_primes hn
    rcases lt_trichotomy a b with h1 | h1 | h1
    · rcases lt_trichotomy c a with h2 | h2 | h2
      · exact L c a b hpc hpa hpb h2 h1 (by rw [← hprod]; try ring)
      · exact absurd h2.symm hac
      · rcases lt_trichotomy c b with h3 | h3 | h3
        · exact L a c b hpa hpc hpb h2 h3 (by rw [← hprod]; try ring)
        · exact absurd h3.symm hbc
        · exact L a b c hpa hpb hpc h1 h3 (by rw [← hprod]; try ring)
    · exact absurd h1 hab
    · rcases lt_trichotomy c b with h2 | h2 | h2
      · exact L c b a hpc hpb hpa h2 h1 (by rw [← hprod]; try ring)
      · exact absurd h2.symm hbc
      · rcases lt_trichotomy c a with h3 | h3 | h3
        · exact L b c a hpb hpc hpa h2 h3 (by rw [← hprod]; try ring)
        · exact absurd h3.symm hac
        · exact L b a c hpb hpa hpc h1 h3 (by rw [← hprod]; try ring)
  · -- ω(n) = 4: split off the minimum prime, sort the remaining three, so n = 1679615.
    have hne : n.primeFactors.Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨p, hpmem, hpmin⟩ : ∃ p ∈ n.primeFactors, ∀ x ∈ n.primeFactors, p ≤ x :=
      ⟨n.primeFactors.min' hne, Finset.min'_mem _ _, fun x hx => Finset.min'_le _ x hx⟩
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hpmem
    have htc : (n.primeFactors.erase p).card = 3 := by
      rw [Finset.card_erase_of_mem hpmem, h]
    obtain ⟨a, b, c, hab, hac, hbc, hs⟩ := Finset.card_eq_three.mp htc
    obtain ⟨hane, haf⟩ := Finset.mem_erase.mp (show a ∈ n.primeFactors.erase p by
      rw [hs]; simp)
    obtain ⟨hbne, hbf⟩ := Finset.mem_erase.mp (show b ∈ n.primeFactors.erase p by
      rw [hs]; simp)
    obtain ⟨hcne, hcf⟩ := Finset.mem_erase.mp (show c ∈ n.primeFactors.erase p by
      rw [hs]; simp)
    have hpa : a.Prime := Nat.prime_of_mem_primeFactors haf
    have hpb : b.Prime := Nat.prime_of_mem_primeFactors hbf
    have hpc : c.Prime := Nat.prime_of_mem_primeFactors hcf
    -- p is the strict minimum: p < a, b, c.
    have hlta : p < a := (hpmin a haf).lt_of_ne (Ne.symm hane)
    have hltb : p < b := (hpmin b hbf).lt_of_ne (Ne.symm hbne)
    have hltc : p < c := (hpmin c hcf).lt_of_ne (Ne.symm hcne)
    -- Expand the product over {p} ∪ {a, b, c}.
    have hins : insert p (n.primeFactors.erase p) = n.primeFactors :=
      Finset.insert_erase hpmem
    rw [← hins, Finset.prod_insert (by simp), hs,
        Finset.prod_insert (by simp [hab, hac]), Finset.prod_insert (by simp [hbc]),
        Finset.prod_singleton] at hprod
    -- hprod : p * (a * (b * c)) = n
    refine Or.inr (Or.inr (Or.inr ?_))
    have L := solution_four_primes hn
    rcases lt_trichotomy a b with h1 | h1 | h1
    · rcases lt_trichotomy c a with h2 | h2 | h2
      · exact L p c a b hpp hpc hpa hpb hltc h2 h1 (by rw [← hprod]; try ring)
      · exact absurd h2.symm hac
      · rcases lt_trichotomy c b with h3 | h3 | h3
        · exact L p a c b hpp hpa hpc hpb hlta h2 h3 (by rw [← hprod]; try ring)
        · exact absurd h3.symm hbc
        · exact L p a b c hpp hpa hpb hpc hlta h1 h3 (by rw [← hprod]; try ring)
    · exact absurd h1 hab
    · rcases lt_trichotomy c b with h2 | h2 | h2
      · exact L p c b a hpp hpc hpb hpa hltc h2 h1 (by rw [← hprod]; try ring)
      · exact absurd h2.symm hbc
      · rcases lt_trichotomy c a with h3 | h3 | h3
        · exact L p b c a hpp hpb hpc hpa hltb h2 h3 (by rw [← hprod]; try ring)
        · exact absurd h3.symm hac
        · exact L p b a c hpp hpb hpa hpc hltb h1 h3 (by rw [← hprod]; try ring)

/-! ## 2. The weak hypothesis and its upgrade to the full conjecture -/

/-- The **weak totient hypothesis**: every solution of `3·φ(n) = 2n + 2` has at most
four distinct prime factors. (Hercher proved any unknown solution has ≥ 7, so this is
the open content; it is formally weaker than naming the solutions.) -/
def WeakTotientHypothesis : Prop :=
  ∀ n : ℕ, 3 * Nat.totient n = 2 * n + 2 → n.primeFactors.card ≤ 4

/-- The weak hypothesis already implies Steinerberger's full totient conjecture: the
classification above turns the ω-bound into the explicit solution list. -/
theorem weak_implies_conjecture (H : WeakTotientHypothesis) :
    EG411RealResult.TotientConjecture :=
  fun n hn => solution_omega_le_four_classified n hn (H n hn)

/-- **Sharp conditional closure of EG#411 (r=2).** Assuming only the weak totient
hypothesis (`ω ≤ 4` for all solutions), every EG#411 exceptional prime is `7` or `47`. -/
theorem eg411_r2_conditional_closure_sharp (H : WeakTotientHypothesis)
    (N p : ℕ) (hN : 3 * Nat.totient N = 2 * N + 2)
    (hp : 3 * p = 4 * N + 1) (hpr : p.Prime) :
    p = 7 ∨ p = 47 :=
  EG411RealResult.eg411_r2_conditional_closure (weak_implies_conjecture H) N p hN hp hpr

/-! ## 3. The unconditional headline -/

/-- **Unconditional:** any EG#411 exceptional prime other than `7` and `47` arises from
a solution `N` of `3·φ(N) = 2N + 2` with **at least five distinct prime factors**.
(If `ω(N) ≤ 4` then `N ∈ {5, 35, 1295, 1679615}`, whose primes `(4N+1)/3` are exactly
`7`, `47`, and the composites `1727 = 11·157`, `2239487 = 23·97369`.) -/
theorem exceptional_high_omega (N p : ℕ) (hN : 3 * Nat.totient N = 2 * N + 2)
    (hp : 3 * p = 4 * N + 1) (hpr : p.Prime) (h7 : p ≠ 7) (h47 : p ≠ 47) :
    5 ≤ N.primeFactors.card := by
  by_contra hcon
  have hcard : N.primeFactors.card ≤ 4 := by omega
  rcases solution_omega_le_four_classified N hN hcard with rfl | rfl | rfl | rfl
  · exact h7 (by omega)
  · exact h47 (by omega)
  · -- N = 1295 ⟹ p = 1727 = 11·157, not prime.
    have hp' : p = 1727 := by omega
    subst hp'
    rcases hpr.eq_one_or_self_of_dvd 11 ⟨157, by norm_num⟩ with h | h <;> omega
  · -- N = 1679615 ⟹ p = 2239487 = 23·97369, not prime.
    have hp' : p = 2239487 := by omega
    subst hp'
    rcases hpr.eq_one_or_self_of_dvd 23 ⟨97369, by norm_num⟩ with h | h <;> omega

/-! ## 4. Pushing the ladder one rung higher: the ω = 5 stratum is empty -/

/-- Every solution of `3·φ(n) = 2n + 2` with at most **five** distinct prime factors is
one of the four known solutions `5`, `35`, `1295`, `1679615`. The new content over
`solution_omega_le_four_classified` is that the `ω(n) = 5` stratum is **empty**
(`omega5_empty`, the certified kill-tree of `OmegaTree5.lean`): the two smallest primes
are split off via iterated `Finset.min'`, the remaining three are sorted, and the sorted
five-tuple is fed to the tree. -/
theorem solution_omega_le_five_classified (n : ℕ)
    (hn : 3 * Nat.totient n = 2 * n + 2) (hcard : n.primeFactors.card ≤ 5) :
    n = 5 ∨ n = 35 ∨ n = 1295 ∨ n = 1679615 := by
  rcases Nat.lt_or_ge n.primeFactors.card 5 with hlt | hge
  · exact solution_omega_le_four_classified n hn (by omega)
  · -- ω(n) = 5: derive False from the certified kill-tree.
    exfalso
    have h : n.primeFactors.card = 5 := le_antisymm hcard hge
    have hsf : Squarefree n := solution_squarefree hn
    have hprod : ∏ p ∈ n.primeFactors, p = n := Nat.prod_primeFactors_of_squarefree hsf
    -- Split off the minimum prime p of the five.
    have hne : n.primeFactors.Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨p, hpmem, hpmin⟩ : ∃ p ∈ n.primeFactors, ∀ x ∈ n.primeFactors, p ≤ x :=
      ⟨n.primeFactors.min' hne, Finset.min'_mem _ _, fun x hx => Finset.min'_le _ x hx⟩
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hpmem
    have htc : (n.primeFactors.erase p).card = 4 := by
      rw [Finset.card_erase_of_mem hpmem, h]
    -- Split off the minimum prime q of the remaining four.
    have htne : (n.primeFactors.erase p).Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨q, hqmem, hqmin⟩ : ∃ q ∈ n.primeFactors.erase p,
        ∀ x ∈ n.primeFactors.erase p, q ≤ x :=
      ⟨(n.primeFactors.erase p).min' htne, Finset.min'_mem _ _,
        fun x hx => Finset.min'_le _ x hx⟩
    obtain ⟨hqne, hqf⟩ := Finset.mem_erase.mp hqmem
    have hpq : q.Prime := Nat.prime_of_mem_primeFactors hqf
    have hpltq : p < q := (hpmin q hqf).lt_of_ne (Ne.symm hqne)
    have hsc : ((n.primeFactors.erase p).erase q).card = 3 := by
      rw [Finset.card_erase_of_mem hqmem, htc]
    obtain ⟨a, b, c, hab, hac, hbc, hs⟩ := Finset.card_eq_three.mp hsc
    obtain ⟨hane, haT⟩ := Finset.mem_erase.mp
      (show a ∈ (n.primeFactors.erase p).erase q by rw [hs]; simp)
    obtain ⟨hbne, hbT⟩ := Finset.mem_erase.mp
      (show b ∈ (n.primeFactors.erase p).erase q by rw [hs]; simp)
    obtain ⟨hcne, hcT⟩ := Finset.mem_erase.mp
      (show c ∈ (n.primeFactors.erase p).erase q by rw [hs]; simp)
    have haf : a ∈ n.primeFactors := (Finset.mem_erase.mp haT).2
    have hbf : b ∈ n.primeFactors := (Finset.mem_erase.mp hbT).2
    have hcf : c ∈ n.primeFactors := (Finset.mem_erase.mp hcT).2
    have hpa : a.Prime := Nat.prime_of_mem_primeFactors haf
    have hpb : b.Prime := Nat.prime_of_mem_primeFactors hbf
    have hpc : c.Prime := Nat.prime_of_mem_primeFactors hcf
    -- q is the strict minimum of the remaining four: q < a, b, c.
    have hqlta : q < a := (hqmin a haT).lt_of_ne (Ne.symm hane)
    have hqltb : q < b := (hqmin b hbT).lt_of_ne (Ne.symm hbne)
    have hqltc : q < c := (hqmin c hcT).lt_of_ne (Ne.symm hcne)
    -- Expand the product over {p} ∪ {q} ∪ {a, b, c}.
    have hins1 : insert p (n.primeFactors.erase p) = n.primeFactors :=
      Finset.insert_erase hpmem
    have hins2 : insert q ((n.primeFactors.erase p).erase q) = n.primeFactors.erase p :=
      Finset.insert_erase hqmem
    rw [← hins1, Finset.prod_insert (by simp), ← hins2, Finset.prod_insert (by simp), hs,
        Finset.prod_insert (by simp [hab, hac]), Finset.prod_insert (by simp [hbc]),
        Finset.prod_singleton] at hprod
    -- hprod : p * (q * (a * (b * c))) = n
    have K := omega5_empty n hn
    rcases lt_trichotomy a b with h1 | h1 | h1
    · rcases lt_trichotomy c a with h2 | h2 | h2
      · exact K p q c a b hpp hpq hpc hpa hpb hpltq hqltc h2 h1 (by rw [← hprod]; try ring)
      · exact absurd h2.symm hac
      · rcases lt_trichotomy c b with h3 | h3 | h3
        · exact K p q a c b hpp hpq hpa hpc hpb hpltq hqlta h2 h3 (by rw [← hprod]; try ring)
        · exact absurd h3.symm hbc
        · exact K p q a b c hpp hpq hpa hpb hpc hpltq hqlta h1 h3 (by rw [← hprod]; try ring)
    · exact absurd h1 hab
    · rcases lt_trichotomy c b with h2 | h2 | h2
      · exact K p q c b a hpp hpq hpc hpb hpa hpltq hqltc h2 h1 (by rw [← hprod]; try ring)
      · exact absurd h2.symm hbc
      · rcases lt_trichotomy c a with h3 | h3 | h3
        · exact K p q b c a hpp hpq hpb hpc hpa hpltq hqltb h2 h3 (by rw [← hprod]; try ring)
        · exact absurd h3.symm hac
        · exact K p q b a c hpp hpq hpb hpa hpc hpltq hqltb h1 h3 (by rw [← hprod]; try ring)

/-- **Unconditional, one rung higher than `exceptional_high_omega`:** any EG#411
exceptional prime other than `7` and `47` arises from a solution `N` of
`3·φ(N) = 2N + 2` with **at least six distinct prime factors** — the ω = 5 stratum is
empty by the certified kill-tree. -/
theorem exceptional_high_omega_six (N p : ℕ) (hN : 3 * Nat.totient N = 2 * N + 2)
    (hp : 3 * p = 4 * N + 1) (hpr : p.Prime) (h7 : p ≠ 7) (h47 : p ≠ 47) :
    6 ≤ N.primeFactors.card := by
  by_contra hcon
  have hcard : N.primeFactors.card ≤ 5 := by omega
  rcases solution_omega_le_five_classified N hN hcard with rfl | rfl | rfl | rfl
  · exact h7 (by omega)
  · exact h47 (by omega)
  · -- N = 1295 ⟹ p = 1727 = 11·157, not prime.
    have hp' : p = 1727 := by omega
    subst hp'
    rcases hpr.eq_one_or_self_of_dvd 11 ⟨157, by norm_num⟩ with h | h <;> omega
  · -- N = 1679615 ⟹ p = 2239487 = 23·97369, not prime.
    have hp' : p = 2239487 := by omega
    subst hp'
    rcases hpr.eq_one_or_self_of_dvd 23 ⟨97369, by norm_num⟩ with h | h <;> omega

/-- The **weak totient hypothesis at level five**: every solution of `3·φ(n) = 2n + 2`
has at most five distinct prime factors. Strictly weaker than `WeakTotientHypothesis`
(ω ≤ 4), since the ω = 5 stratum is unconditionally empty (`omega5_empty`). -/
def WeakTotientHypothesis5 : Prop :=
  ∀ n : ℕ, 3 * Nat.totient n = 2 * n + 2 → n.primeFactors.card ≤ 5

/-- The level-four hypothesis trivially implies the level-five one. -/
theorem weak_implies_weak5 (H : WeakTotientHypothesis) : WeakTotientHypothesis5 :=
  fun n hn => le_trans (H n hn) (by norm_num)

/-- The level-five weak hypothesis already implies Steinerberger's full totient
conjecture: the ω ≤ 5 classification turns the bound into the explicit solution list. -/
theorem weak5_implies_conjecture (H : WeakTotientHypothesis5) :
    EG411RealResult.TotientConjecture :=
  fun n hn => solution_omega_le_five_classified n hn (H n hn)

/-- **Sharp conditional closure of EG#411 (r=2), level five.** Assuming only that every
solution has `ω ≤ 5`, every EG#411 exceptional prime is `7` or `47`. -/
theorem eg411_r2_conditional_closure_sharp5 (H : WeakTotientHypothesis5)
    (N p : ℕ) (hN : 3 * Nat.totient N = 2 * N + 2)
    (hp : 3 * p = 4 * N + 1) (hpr : p.Prime) :
    p = 7 ∨ p = 47 :=
  EG411RealResult.eg411_r2_conditional_closure (weak5_implies_conjecture H) N p hN hp hpr

end EG411Capstone
