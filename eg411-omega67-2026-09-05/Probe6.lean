import Mathlib
import OmegaCapstone

namespace Probe

open EG411Structure EG411Capstone

theorem probe_le_six_classified
    (omega6_empty : ∀ (n : ℕ), 3 * Nat.totient n = 2 * n + 2 →
      ∀ p1 p2 p3 p4 p5 p6 : ℕ, p1.Prime → p2.Prime → p3.Prime → p4.Prime → p5.Prime → p6.Prime →
      p1 < p2 → p2 < p3 → p3 < p4 → p4 < p5 → p5 < p6 →
      n = p1 * (p2 * (p3 * (p4 * (p5 * p6)))) → False)
    (n : ℕ)
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
          (by rw [← hprod]; try ring)
      · exact absurd h2.symm hac
      · rcases lt_trichotomy c b with h3 | h3 | h3
        · exact K p q r a c b hpp hpq hpr hpa hpc hpb hpltq hqltr hrlta h2 h3
            (by rw [← hprod]; try ring)
        · exact absurd h3.symm hbc
        · exact K p q r a b c hpp hpq hpr hpa hpb hpc hpltq hqltr hrlta h1 h3
            (by rw [← hprod]; try ring)
    · exact absurd h1 hab
    · rcases lt_trichotomy c b with h2 | h2 | h2
      · exact K p q r c b a hpp hpq hpr hpc hpb hpa hpltq hqltr hrltc h2 h1
          (by rw [← hprod]; try ring)
      · exact absurd h2.symm hbc
      · rcases lt_trichotomy c a with h3 | h3 | h3
        · exact K p q r b c a hpp hpq hpr hpb hpc hpa hpltq hqltr hrltb h2 h3
            (by rw [← hprod]; try ring)
        · exact absurd h3.symm hac
        · exact K p q r b a c hpp hpq hpr hpb hpa hpc hpltq hqltr hrltb h1 h3
            (by rw [← hprod]; try ring)


end Probe
