import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.GenericRejection PEqualNP.ReadK

-- Small orders use L-meta-5351. The other paid case counts read-two witnesses per incidence.
theorem PEqualNP.Outside.R_meta_2984_421
    (smallOrder : ∀ (q N : ℕ) (S : Fin N → Finset (Fin N)) (C : Circuit),
      200 ≤ q → N = q^2 + q + 1 →
      (∀ l, (S l).card = q + 1) → (∀ p p', p ≠ p' → ∃! l, p ∈ S l ∧ p' ∈ S l) →
      IsAO2 (N + N) C → RightOnIncidentPairs S C →
      (∀ X Y, Y.card ≤ q → IsFalseInput S X Y → C.eval (incidenceInput X Y) = false) →
      349 * N ≤ 100 * C.size)
    (countReadTwo : ∀ (q N : ℕ) (S : Fin N → Finset (Fin N)) (C : Circuit),
      200 ≤ q → N = q^2 + q + 1 →
      (∀ l, (S l).card = q + 1) → (∀ p p', p ≠ p' → ∃! l, p ∈ S l ∧ p' ∈ S l) →
      IsAO2 (N + N) C → C.output < N + N + C.size → RightOnIncidentPairs S C →
      (∀ X Y, Y.card ≤ q → IsFalseInput S X Y → C.eval (incidenceInput X Y) = false) →
      let good : Finset (Fin N × Fin N) := Finset.univ.filter fun e => e.1 ∈ S e.2 ∧
        readsAtMost C (N + N) (setList {Fin.castAdd N e.1, Fin.natAdd N e.2}) 2 = true
      good.card ≤ 70 * C.size)
    (manyRepeated : ∀ (q N : ℕ) (S : Fin N → Finset (Fin N)) (C : Circuit),
      350 ≤ q → N = q^2 + q + 1 →
      (∀ l, (S l).card = q + 1) → (∀ p p', p ≠ p' → ∃! l, p ∈ S l ∧ p' ∈ S l) →
      IsAO2 (N + N) C → C.output < N + N + C.size → RightOnIncidentPairs S C →
      (∀ X Y, Y.card ≤ q → IsFalseInput S X Y → C.eval (incidenceInput X Y) = false) →
      let good : Finset (Fin N × Fin N) := Finset.univ.filter fun e => e.1 ∈ S e.2 ∧
        readsAtMost C (N + N) (setList {Fin.castAdd N e.1, Fin.natAdd N e.2}) 2 = true
      10 * good.card < 7 * (N * q) → N * q ≤ 100 * C.size) :
    ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Finset (Fin x2)) (x4 : PEqualNP.CircuitLowerBounds.Circuit), (200 : ℕ) ≤ x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x7 : Fin x2), (x3 x7).card = x1 + (1 : ℕ)) → (∀ (x8 x9 : Fin x2), x8 ≠ x9 → ∃! x11 : Fin x2, x8 ∈ x3 x11 ∧ x9 ∈ x3 x11) → PEqualNP.TopForm.IsAO2 (x2 + x2) x4 → x4.output < x2 + x2 + x4.size → PEqualNP.GenericRejection.RightOnIncidentPairs x3 x4 → (∀ (x12 x13 : Finset (Fin x2)), x13.card ≤ x1 → PEqualNP.GenericRejection.IsFalseInput x3 x12 x13 → x4.eval (PEqualNP.GenericRejection.incidenceInput x12 x13) = Bool.false) → x2 * x1 ≤ (100 : ℕ) * x4.size := by
  intro q N S C hq hN hcard hjoin hao hout hright hfalse
  by_cases high : 350 ≤ q
  · let good := (Finset.univ.filter fun e : Fin N × Fin N => e.1 ∈ S e.2 ∧
      readsAtMost C (N + N) (setList {Fin.castAdd N e.1, Fin.natAdd N e.2}) 2 = true).card
    by_cases few : 10 * good < 7 * (N * q)
    · exact manyRepeated q N S C high hN hcard hjoin hao hout hright hfalse few
    · have bound : good ≤ 70 * C.size := countReadTwo q N S C hq hN hcard hjoin hao hout hright hfalse
      omega
  · have bound := smallOrder q N S C hq hN hcard hjoin hao hright hfalse
    have mul := Nat.mul_le_mul_left N (show q ≤ 349 by omega)
    exact mul.trans (by simpa only [Nat.mul_comm N 349] using bound)
