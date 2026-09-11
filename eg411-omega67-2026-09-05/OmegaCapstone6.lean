import Mathlib
import OmegaCapstone
import Omega6MainMF

/-!
# EG#411 (r=2): the ω = 6 rung — dropping the standing hypothesis to `ω ≤ 6`

`OmegaCapstone.lean` closes the ladder at `ω ≤ 5`
(`solution_omega_le_five_classified`, `WeakTotientHypothesis5`,
`eg411_r2_conditional_closure_sharp5`) and its own docstring names the next move:
consume the certified ω = 6 kill-tree (`EG411Structure.omega6_empty`,
`Omega6MainMF.lean`) and weaken the standing hypothesis one further rung.

This file walks exactly that step:

  • `solution_omega_le_six_classified` — every solution of `3·φ(n) = 2n + 2` with
    `ω(n) ≤ 6` is one of `5, 35, 1295, 1679615`; the ω = 6 stratum is empty.
  • `WeakTotientHypothesis6` — `ω ≤ 6` for all solutions; weaker than
    `WeakTotientHypothesis5`, which is weaker than `WeakTotientHypothesis`.
  • `eg411_r2_conditional_closure_sharp6` — the r=2 conditional closure now standing
    on `ω ≤ 6` alone.
  • `exceptional_high_omega_seven` — unconditional: any exceptional prime other than
    `7` and `47` comes from a solution with **at least seven** distinct prime factors.

Method is the section-4 ladder one rung higher: three iterated `Finset.min'` splits
(p < q < r), the remaining three primes sorted by trichotomy, and the sorted six-tuple
fed to `omega6_empty`.

AXIOM DISCLOSURE. `omega6_empty` is a `native_decide` kill-tree: every theorem in this
file that routes through the ω = 6 stratum inherits the per-call-site `native_decide`
compiler-trust axioms of `EG411Structure.omega6_empty`, on top of
`{propext, Classical.choice, Quot.sound}` and those already inherited from
`omega5_empty`. `weak5_implies_weak6` alone is native-free. The `#print axioms` block
at the tail of this file is the receipt; read it, do not assume it.
-/

namespace EG411Capstone

open EG411Structure

/-! ## 1. The ω = 6 stratum is empty -/

/-- Every solution of `3·φ(n) = 2n + 2` with at most **six** distinct prime factors is
one of the four known solutions `5`, `35`, `1295`, `1679615`. -/
theorem solution_omega_le_six_classified (n : ℕ)
    (hn : 3 * Nat.totient n = 2 * n + 2) (hcard : n.primeFactors.card ≤ 6) :
    n = 5 ∨ n = 35 ∨ n = 1295 ∨ n = 1679615 := by
  rcases Nat.lt_or_ge n.primeFactors.card 6 with hlt | hge
  · exact solution_omega_le_five_classified n hn (by omega)
  · exfalso
    have h : n.primeFactors.card = 6 := le_antisymm hcard hge
    have hsf : Squarefree n := solution_squarefree hn
    have hprod : ∏ p ∈ n.primeFactors, p = n := Nat.prod_primeFactors_of_squarefree hsf
    -- minimum p of the six
    have hne : n.primeFactors.Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨p, hpmem, hpmin⟩ : ∃ p ∈ n.primeFactors, ∀ x ∈ n.primeFactors, p ≤ x :=
      ⟨n.primeFactors.min' hne, Finset.min'_mem _ _, fun x hx => Finset.min'_le _ x hx⟩
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hpmem
    have htc : (n.primeFactors.erase p).card = 5 := by
      rw [Finset.card_erase_of_mem hpmem, h]
    -- minimum q of the remaining five
    have htne : (n.primeFactors.erase p).Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨q, hqmem, hqmin⟩ : ∃ q ∈ n.primeFactors.erase p,
        ∀ x ∈ n.primeFactors.erase p, q ≤ x :=
      ⟨(n.primeFactors.erase p).min' htne, Finset.min'_mem _ _,
        fun x hx => Finset.min'_le _ x hx⟩
    obtain ⟨hqne, hqf⟩ := Finset.mem_erase.mp hqmem
    have hpq : q.Prime := Nat.prime_of_mem_primeFactors hqf
    have hpltq : p < q := (hpmin q hqf).lt_of_ne (Ne.symm hqne)
    have hsc : ((n.primeFactors.erase p).erase q).card = 4 := by
      rw [Finset.card_erase_of_mem hqmem, htc]
    -- minimum r of the remaining four
    have hsne : ((n.primeFactors.erase p).erase q).Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨r, hrmem, hrmin⟩ : ∃ r ∈ (n.primeFactors.erase p).erase q,
        ∀ x ∈ (n.primeFactors.erase p).erase q, r ≤ x :=
      ⟨((n.primeFactors.erase p).erase q).min' hsne, Finset.min'_mem _ _,
        fun x hx => Finset.min'_le _ x hx⟩
    obtain ⟨hrne, hrT⟩ := Finset.mem_erase.mp hrmem
    have hrf : r ∈ n.primeFactors := (Finset.mem_erase.mp hrT).2
    have hpr : r.Prime := Nat.prime_of_mem_primeFactors hrf
    have hqltr : q < r := (hqmin r hrT).lt_of_ne (Ne.symm hrne)
    have hqc : (((n.primeFactors.erase p).erase q).erase r).card = 3 := by
      rw [Finset.card_erase_of_mem hrmem, hsc]
    obtain ⟨a, b, c, hab, hac, hbc, hs⟩ := Finset.card_eq_three.mp hqc
    obtain ⟨hane, haU⟩ := Finset.mem_erase.mp
      (show a ∈ ((n.primeFactors.erase p).erase q).erase r by rw [hs]; simp)
    obtain ⟨hbne, hbU⟩ := Finset.mem_erase.mp
      (show b ∈ ((n.primeFactors.erase p).erase q).erase r by rw [hs]; simp)
    obtain ⟨hcne, hcU⟩ := Finset.mem_erase.mp
      (show c ∈ ((n.primeFactors.erase p).erase q).erase r by rw [hs]; simp)
    have haf : a ∈ n.primeFactors := (Finset.mem_erase.mp (Finset.mem_erase.mp haU).2).2
    have hbf : b ∈ n.primeFactors := (Finset.mem_erase.mp (Finset.mem_erase.mp hbU).2).2
    have hcf : c ∈ n.primeFactors := (Finset.mem_erase.mp (Finset.mem_erase.mp hcU).2).2
    have hpa : a.Prime := Nat.prime_of_mem_primeFactors haf
    have hpb : b.Prime := Nat.prime_of_mem_primeFactors hbf
    have hpc : c.Prime := Nat.prime_of_mem_primeFactors hcf
    -- r is the strict minimum of the remaining three
    have hrlta : r < a := (hrmin a haU).lt_of_ne (Ne.symm hane)
    have hrltb : r < b := (hrmin b hbU).lt_of_ne (Ne.symm hbne)
    have hrltc : r < c := (hrmin c hcU).lt_of_ne (Ne.symm hcne)
    -- expand the product over {p} ∪ {q} ∪ {r} ∪ {a, b, c}
    have hins1 : insert p (n.primeFactors.erase p) = n.primeFactors :=
      Finset.insert_erase hpmem
    have hins2 : insert q ((n.primeFactors.erase p).erase q) = n.primeFactors.erase p :=
      Finset.insert_erase hqmem
    have hins3 : insert r (((n.primeFactors.erase p).erase q).erase r)
        = (n.primeFactors.erase p).erase q := Finset.insert_erase hrmem
    rw [← hins1, Finset.prod_insert (by simp), ← hins2, Finset.prod_insert (by simp),
        ← hins3, Finset.prod_insert (by simp), hs,
        Finset.prod_insert (by simp [hab, hac]), Finset.prod_insert (by simp [hbc]),
        Finset.prod_singleton] at hprod
    -- hprod : p * (q * (r * (a * (b * c)))) = n
    have K := omega6_empty n hn
    rcases lt_trichotomy a b with h1 | h1 | h1
    · rcases lt_trichotomy c a with h2 | h2 | h2
      · exact K p q r c a b hpp hpq hpr hpc hpa hpb hpltq hqltr hrltc h2 h1
          (by rw [← hprod]; ring)
      · exact absurd h2.symm hac
      · rcases lt_trichotomy c b with h3 | h3 | h3
        · exact K p q r a c b hpp hpq hpr hpa hpc hpb hpltq hqltr hrlta h2 h3
            (by rw [← hprod]; ring)
        · exact absurd h3.symm hbc
        · exact K p q r a b c hpp hpq hpr hpa hpb hpc hpltq hqltr hrlta h1 h3
            (by rw [← hprod]; ring)
    · exact absurd h1 hab
    · rcases lt_trichotomy c b with h2 | h2 | h2
      · exact K p q r c b a hpp hpq hpr hpc hpb hpa hpltq hqltr hrltc h2 h1
          (by rw [← hprod]; ring)
      · exact absurd h2.symm hbc
      · rcases lt_trichotomy c a with h3 | h3 | h3
        · exact K p q r b c a hpp hpq hpr hpb hpc hpa hpltq hqltr hrltb h2 h3
            (by rw [← hprod]; ring)
        · exact absurd h3.symm hac
        · exact K p q r b a c hpp hpq hpr hpb hpa hpc hpltq hqltr hrltb h1 h3
            (by rw [← hprod]; ring)

/-! ## 2. The level-six weak hypothesis -/

/-- The **weak totient hypothesis at level six**: every solution of `3·φ(n) = 2n + 2`
has at most six distinct prime factors. Weaker than `WeakTotientHypothesis5`, since the
ω = 6 stratum is unconditionally empty (`omega6_empty`). -/
def WeakTotientHypothesis6 : Prop :=
  ∀ n : ℕ, 3 * Nat.totient n = 2 * n + 2 → n.primeFactors.card ≤ 6

/-- The level-five hypothesis trivially implies the level-six one. Native-free. -/
theorem weak5_implies_weak6 (H : WeakTotientHypothesis5) : WeakTotientHypothesis6 :=
  fun n hn => le_trans (H n hn) (by norm_num)

/-- The level-six weak hypothesis already implies Steinerberger's full totient
conjecture. -/
theorem weak6_implies_conjecture (H : WeakTotientHypothesis6) :
    EG411RealResult.TotientConjecture :=
  fun n hn => solution_omega_le_six_classified n hn (H n hn)

/-- **Sharp conditional closure of EG#411 (r=2), level six.** Assuming only that every
solution has `ω ≤ 6`, every EG#411 exceptional prime is `7` or `47`. -/
theorem eg411_r2_conditional_closure_sharp6 (H : WeakTotientHypothesis6)
    (N p : ℕ) (hN : 3 * Nat.totient N = 2 * N + 2)
    (hp : 3 * p = 4 * N + 1) (hpr : p.Prime) :
    p = 7 ∨ p = 47 :=
  EG411RealResult.eg411_r2_conditional_closure (weak6_implies_conjecture H) N p hN hp hpr

/-! ## 3. The unconditional headline, one rung higher -/

/-- **Unconditional:** any EG#411 exceptional prime other than `7` and `47` arises from
a solution `N` of `3·φ(N) = 2N + 2` with **at least seven** distinct prime factors. -/
theorem exceptional_high_omega_seven (N p : ℕ) (hN : 3 * Nat.totient N = 2 * N + 2)
    (hp : 3 * p = 4 * N + 1) (hpr : p.Prime) (h7 : p ≠ 7) (h47 : p ≠ 47) :
    7 ≤ N.primeFactors.card := by
  by_contra hcon
  have hcard : N.primeFactors.card ≤ 6 := by omega
  rcases solution_omega_le_six_classified N hN hcard with rfl | rfl | rfl | rfl
  · exact h7 (by omega)
  · exact h47 (by omega)
  · have hp' : p = 1727 := by omega
    subst hp'
    rcases hpr.eq_one_or_self_of_dvd 11 ⟨157, by norm_num⟩ with h | h <;> omega
  · have hp' : p = 2239487 := by omega
    subst hp'
    rcases hpr.eq_one_or_self_of_dvd 23 ⟨97369, by norm_num⟩ with h | h <;> omega

end EG411Capstone

#print axioms EG411Capstone.solution_omega_le_six_classified
#print axioms EG411Capstone.weak5_implies_weak6
#print axioms EG411Capstone.weak6_implies_conjecture
#print axioms EG411Capstone.eg411_r2_conditional_closure_sharp6
#print axioms EG411Capstone.exceptional_high_omega_seven
