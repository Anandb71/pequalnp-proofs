import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm
open Classical

theorem PEqualNP.Outside.R_meta_3775_2
    (paid : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      (∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → 5 ≤ p.length) →
      ∀ (C : Circuit), IsLeastAO G C → TopForm G C →
      {e ∈ Ustar G C | ∃ u v : Fin n, e = s(u, v) ∧
        ∃ a ∈ tops G C, ∃ b : Fin 2, ∃ g ∈ junk G C,
          (∀ j ∈ junk G C, ¬ InCone n C j g) ∧
          u ∈ side C a b ∧ OrReaches n C (opnd C a (1 - b)) g ∧
          gateVal n C g (pairInput u v) = true}.card ≤ 54 * (C.size + 1))
    (residual : ∃ k : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      (∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → 5 ≤ p.length) →
      G.edgeFinset.Nonempty →
      ∀ (C : Circuit), IsLeastAO G C → TopForm G C → 2 ≤ (junk G C).card →
      (∃ j ∈ junk G C, ∃ h ∈ junk G C, InCone n C j h) →
      (¬ ∃ (K : Finset (Fin n)) (E : Finset (Sym2 (Fin n))),
        K.card ≤ 4 ∧ E.card ≤ C.size + 1 ∧
        ∀ e ∈ Ustar G C, e ∈ E ∨ ∃ u v : Fin n, e = s(u, v) ∧
          ((∃ x ∈ K, G.Adj u x) ∨ ∃ x ∈ K, G.Adj v x)) →
      (Ustar G C \ {e ∈ Ustar G C | ∃ u v : Fin n, e = s(u, v) ∧
        ∃ a ∈ tops G C, ∃ b : Fin 2, ∃ g ∈ junk G C,
          (∀ j ∈ junk G C, ¬ InCone n C j g) ∧
          u ∈ side C a b ∧ OrReaches n C (opnd C a (1 - b)) g ∧
          gateVal n C g (pairInput u v) = true}).card ≤ k * (C.size + 1)) :
    ∃ (x1 : ℕ), ∀ (x2 : ℕ) (x3 : SimpleGraph (Fin x2)) [x4 : DecidableRel x3.Adj], (∀ (x5 : Fin x2) (x6 : x3.Walk x5 x5), x6.IsCycle → (5 : ℕ) ≤ x6.length) → x3.edgeFinset.Nonempty → ∀ (x7 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsLeastAO x3 x7 → PEqualNP.TopForm.TopForm x3 x7 → (2 : ℕ) ≤ (PEqualNP.TopForm.junk x3 x7).card → (∃ x11 ∈ PEqualNP.TopForm.junk x3 x7, ∃ x12 ∈ PEqualNP.TopForm.junk x3 x7, PEqualNP.EdgeOwnership.InCone x2 x7 x11 x12) → (¬∃ (x12 : Finset (Fin x2)) (x13 : Finset (Sym2 (Fin x2))), x12.card ≤ (4 : ℕ) ∧ x13.card ≤ x7.size + (1 : ℕ) ∧ ∀ x14 ∈ PEqualNP.TopForm.Ustar x3 x7, x14 ∈ x13 ∨ ∃ (x16 : Fin x2) (x17 : Fin x2), x14 = s(x16, x17) ∧ ((∃ x18 ∈ x12, x3.Adj x16 x18) ∨ ∃ x18 ∈ x12, x3.Adj x17 x18)) → (PEqualNP.TopForm.Ustar x3 x7).card ≤ x1 * (x7.size + (1 : ℕ)) := by
  obtain ⟨k, hresidual⟩ := residual
  refine ⟨k + 54, ?_⟩
  intro n G _ hg he C hL hT hj hnest hNo
  let covered := {e ∈ Ustar G C | ∃ u v : Fin n, e = s(u, v) ∧
        ∃ a ∈ tops G C, ∃ b : Fin 2, ∃ g ∈ junk G C,
          (∀ j ∈ junk G C, ¬ InCone n C j g) ∧
          u ∈ side C a b ∧ OrReaches n C (opnd C a (1 - b)) g ∧
          gateVal n C g (pairInput u v) = true}
  have hCovered : covered.card ≤ 54 * (C.size + 1) :=
    paid n G hg C hL hT
  have hOther : (Ustar G C \ covered).card ≤ k * (C.size + 1) :=
    hresidual n G hg he C hL hT hj hnest hNo
  have hSum : (Ustar G C \ covered).card + covered.card = (Ustar G C).card :=
    Finset.card_sdiff_add_card_eq_card (Finset.filter_subset _ _)
  rw [Nat.add_mul]
  omega
