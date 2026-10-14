import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C159 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hn1 : (G.edgeFinset.card : ℤ) ≤ 5) :
    2 * (G.edgeFinset.card : ℤ) ≤ 3 * (Fintype.card V : ℤ) - 2 := by
  have s1 : 3 * (Fintype.card V : ℤ) - 2 * (G.edgeFinset.card : ℤ) ≥ 2 := by
    by_cases hc1 : (3 : ℤ) ≤ (G.chromaticNumber.toNat : ℤ)
    · -- 1*chi >= 3
      have s2 : 3 * (Fintype.card V : ℤ) - 2 * (G.edgeFinset.card : ℤ) ≥ 2 := by
        by_cases hc2 : (4 : ℤ) ≤ (Fintype.card V : ℤ)
        · -- 1*n >= 4
          have s3 : (Fintype.card V : ℤ) ≥ 4 := by have hcc := hc2; omega
          have s4 : -(G.edgeFinset.card : ℤ) ≥ -5 := by linarith [hn1]
          have s5 : 3 * (Fintype.card V : ℤ) - 2 * (G.edgeFinset.card : ℤ) ≥ 2 := by linarith [s3, s4]
          linarith [s5]
        · -- 1*n <= 3
          have s6 : -(Fintype.card V : ℤ) - 2 * (G.edgeFinset.card : ℤ) + (Fintype.card V : ℤ) * (Fintype.card V : ℤ) ≥ 0 := by
            have hw := two_mul_edges_le_card_sq_sub_card_int G
            try push_cast at hw
            linarith [hw]
          have s7 : (Fintype.card V : ℤ) ≥ 1 := by
            have hw := card_ge_one_int (V := V)
            try push_cast at hw
            linarith [hw]
          have s8 : -(Fintype.card V : ℤ) ≥ -3 := by have hcc := hc2; omega
          have s9 : 4 * (Fintype.card V : ℤ) - (Fintype.card V : ℤ) * (Fintype.card V : ℤ) ≥ 3 := by
            have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 1) * (3 - (Fintype.card V : ℤ)) :=
              mul_nonneg (by linarith [s7]) (by linarith [s8])
            ring_nf at hmul ⊢
            linarith [hmul]
          have s10 : 3 * (Fintype.card V : ℤ) - 2 * (G.edgeFinset.card : ℤ) ≥ 3 := by linarith [s6, s9]
          linarith [s10]
      linarith [s2]
    · -- 1*chi <= 2
      have s11 : 3 * (Fintype.card V : ℤ) - 2 * (G.edgeFinset.card : ℤ) ≥ 2 := by
        by_cases hc11 : (4 : ℤ) ≤ (Fintype.card V : ℤ)
        · -- 1*n >= 4
          have s12 : (Fintype.card V : ℤ) ≥ 4 := by have hcc := hc11; omega
          have s13 : -(G.edgeFinset.card : ℤ) ≥ -5 := by linarith [hn1]
          have s14 : 3 * (Fintype.card V : ℤ) - 2 * (G.edgeFinset.card : ℤ) ≥ 2 := by linarith [s12, s13]
          linarith [s14]
        · -- 1*n <= 3
          have s15 : -(Fintype.card V : ℤ) - 2 * (G.edgeFinset.card : ℤ) + (Fintype.card V : ℤ) * (Fintype.card V : ℤ) ≥ 0 := by
            have hw := two_mul_edges_le_card_sq_sub_card_int G
            try push_cast at hw
            linarith [hw]
          have s16 : (Fintype.card V : ℤ) ≥ 1 := by
            have hw := card_ge_one_int (V := V)
            try push_cast at hw
            linarith [hw]
          have s17 : -(Fintype.card V : ℤ) ≥ -3 := by have hcc := hc11; omega
          have s18 : 4 * (Fintype.card V : ℤ) - (Fintype.card V : ℤ) * (Fintype.card V : ℤ) ≥ 3 := by
            have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 1) * (3 - (Fintype.card V : ℤ)) :=
              mul_nonneg (by linarith [s16]) (by linarith [s17])
            ring_nf at hmul ⊢
            linarith [hmul]
          have s19 : 3 * (Fintype.card V : ℤ) - 2 * (G.edgeFinset.card : ℤ) ≥ 3 := by linarith [s15, s18]
          linarith [s19]
      linarith [s11]
  have heq_gallai := gallai_int G
  try push_cast at heq_gallai
  linarith [s1, heq_gallai]
