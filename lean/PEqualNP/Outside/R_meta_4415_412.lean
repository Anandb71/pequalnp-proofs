import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_4415_412
    (withoutNot :
      let x : List (BitVec 59) := [360930119642124586, 432486920269079116,
        293578547141297264, 289365901620316032, 439119665042618368,
        297239789478805504, 306275578149863424, 540467122476679168, 576425567931334656]
      let step (w : List (BitVec 59)) (g : Fin 3 × List (Fin 25)) :=
        let args := g.2.map fun i => w.getD i.val 0
        w ++ [if g.1 = 0 then args.foldr (· &&& ·) (~~~0)
          else if g.1 = 1 then args.foldr (· ||| ·) 0 else ~~~args.headD 0]
      ∀ (a b : Fin 9) (gs : List (Fin 3 × List (Fin 25))) (o : Fin 25),
        gs.length ≤ 13 → (∀ g ∈ gs, g.2.length ≤ 2) →
        (∀ g ∈ gs, g.1 ≠ 2) →
        let w := x ++ [x.getD 0 0 ||| x.getD 4 0, x.getD a.val 0 ||| x.getD b.val 0]
        (gs.foldl step w).getD o.val 0 ≠ (316380210352264264 : BitVec 59))
    (withNot :
      let x : List (BitVec 59) := [360930119642124586, 432486920269079116,
        293578547141297264, 289365901620316032, 439119665042618368,
        297239789478805504, 306275578149863424, 540467122476679168, 576425567931334656]
      let step (w : List (BitVec 59)) (g : Fin 3 × List (Fin 25)) :=
        let args := g.2.map fun i => w.getD i.val 0
        w ++ [if g.1 = 0 then args.foldr (· &&& ·) (~~~0)
          else if g.1 = 1 then args.foldr (· ||| ·) 0 else ~~~args.headD 0]
      ∀ (a b : Fin 9) (gs : List (Fin 3 × List (Fin 25))) (o : Fin 25),
        10 * min a.val b.val + max a.val b.val ∈ [13,15,17,18,25,26,28,35,36,37,56,67,78] →
        gs.length ≤ 13 → (∀ g ∈ gs, g.2.length ≤ 2) →
        (∀ i : Fin 25, i.val < 9 → ∃ g ∈ gs, i ∈ if g.1 = 2 then g.2.take 1 else g.2) →
        (∃ g ∈ gs, g.1 = 2) →
        let w := x ++ [x.getD 0 0 ||| x.getD 4 0, x.getD a.val 0 ||| x.getD b.val 0]
        (gs.foldl step w).getD o.val 0 ≠ (316380210352264264 : BitVec 59)) :
    have x1 : List (BitVec (59 : ℕ)) := [(360930119642124586 : BitVec (59 : ℕ)), (432486920269079116 : BitVec (59 : ℕ)), (293578547141297264 : BitVec (59 : ℕ)), (289365901620316032 : BitVec (59 : ℕ)), (439119665042618368 : BitVec (59 : ℕ)), (297239789478805504 : BitVec (59 : ℕ)), (306275578149863424 : BitVec (59 : ℕ)), (540467122476679168 : BitVec (59 : ℕ)), (576425567931334656 : BitVec (59 : ℕ))]; have x2 : List (BitVec (59 : ℕ)) → Fin (3 : ℕ) × List (Fin (25 : ℕ)) → List (BitVec (59 : ℕ)) := fun (x2 : List (BitVec (59 : ℕ))) (x3 : Fin (3 : ℕ) × List (Fin (25 : ℕ))) =>   have x4 : List (BitVec (59 : ℕ)) := List.map (fun (x4 : Fin (25 : ℕ)) => x2.getD ↑x4 (0 : BitVec (59 : ℕ))) x3.2;   x2 ++ [if x3.1 = (0 : Fin (3 : ℕ)) then List.foldr (fun (x5 x6 : BitVec (59 : ℕ)) => x5 &&& x6) (~~~(0 : BitVec (59 : ℕ))) x4 else if x3.1 = (1 : Fin (3 : ℕ)) then List.foldr (fun (x5 x6 : BitVec (59 : ℕ)) => x5 ||| x6) (0 : BitVec (59 : ℕ)) x4 else ~~~x4.headD (0 : BitVec (59 : ℕ))]; ∀ (x3 x4 : Fin (9 : ℕ)) (x5 : List (Fin (3 : ℕ) × List (Fin (25 : ℕ)))) (x6 : Fin (25 : ℕ)),   (10 : ℕ) * Min.min ↑x3 ↑x4 + Max.max ↑x3 ↑x4 ∈ [(13 : ℕ), (15 : ℕ), (17 : ℕ), (18 : ℕ), (25 : ℕ), (26 : ℕ), (28 : ℕ), (35 : ℕ), (36 : ℕ), (37 : ℕ), (56 : ℕ), (67 : ℕ), (78 : ℕ)] →     x5.length ≤ (13 : ℕ) →       (∀ x9 ∈ x5, x9.2.length ≤ (2 : ℕ)) →         (∀ (x10 : Fin (25 : ℕ)), ↑x10 < (9 : ℕ) → ∃ x12 ∈ x5, x10 ∈ if x12.1 = (2 : Fin (3 : ℕ)) then List.take (1 : ℕ) x12.2 else x12.2) →           have x11 : List (BitVec (59 : ℕ)) := x1 ++ [x1.getD (0 : ℕ) (0 : BitVec (59 : ℕ)) ||| x1.getD (4 : ℕ) (0 : BitVec (59 : ℕ)), x1.getD ↑x3 (0 : BitVec (59 : ℕ)) ||| x1.getD ↑x4 (0 : BitVec (59 : ℕ))];           have x12 : List (BitVec (59 : ℕ)) := List.foldl x2 x11 x5;           x12.getD ↑x6 (0 : BitVec (59 : ℕ)) ≠ (316380210352264264 : BitVec (59 : ℕ)) := by
  intro x step a b gs o hp hlen hfan hread w out
  by_cases hn : ∃ g ∈ gs, g.1 = 2
  · exact withNot a b gs o hp hlen hfan hread hn
  · exact withoutNot a b gs o hlen hfan (fun g hg he => hn ⟨g, hg, he⟩)
