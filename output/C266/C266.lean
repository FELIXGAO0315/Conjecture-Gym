import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C266 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hn1 : (G.edgeFinset.card : ℤ) ≤ 6) :
    2 * (Fintype.card V : ℤ) ≥ (G.edgeFinset.card : ℤ) + 2 := by
  have s1 : 2 * (Fintype.card V : ℤ) - (G.edgeFinset.card : ℤ) ≥ 2 := by
    by_cases hc1 : (3 : ℤ) ≤ (G.chromaticNumber.toNat : ℤ)
    · -- 1*chi >= 3
      have s2 : (Fintype.card V : ℤ) - (G.maxDegree : ℤ) ≥ 1 := by
        have hw := max_lt_card_int' G
        try push_cast at hw
        linarith [hw]
      have s3 : -2 * (G.edgeFinset.card : ℤ) + (Fintype.card V : ℤ) * (G.maxDegree : ℤ) ≥ 0 := by
        have hw := handshake_max_int G
        try push_cast at hw
        linarith [hw]
      have s4 : -(G.edgeFinset.card : ℤ) ≥ -6 := by linarith [hn1]
      have s5 : (Fintype.card V : ℤ) - (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
        have hw := chi_le_n_int G
        try push_cast at hw
        linarith [hw]
      have s6 : (G.chromaticNumber.toNat : ℤ) ≥ 3 := by have hcc := hc1; omega
      have s7 : (Fintype.card V : ℤ) ≥ 3 := by linarith [s5, s6]
      have s8 : (G.edgeFinset.card : ℤ) - (G.maxDegree : ℤ) ≥ 0 := by
        have hw := max_le_edges_int G
        try push_cast at hw
        linarith [hw]
      have s9 : -(G.maxDegree : ℤ) ≥ -6 := by linarith [s8, s4]
      have s10 : 6 * (Fintype.card V : ℤ) + 3 * (G.maxDegree : ℤ) - (Fintype.card V : ℤ) * (G.maxDegree : ℤ) ≥ 18 := by
        have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 3) * (6 - (G.maxDegree : ℤ)) :=
          mul_nonneg (by linarith [s7]) (by linarith [s9])
        ring_nf at hmul ⊢
        linarith [hmul]
      have s11 : 6 * (Fintype.card V : ℤ) - 3 * (G.edgeFinset.card : ℤ) ≥ 4 := by linarith [s2, s3, s4, s10]
      have s12 : 2 * (Fintype.card V : ℤ) - (G.edgeFinset.card : ℤ) ≥ 2 := by have hr := s11; omega
      linarith [s12]
    · -- 1*chi <= 2
      have s13 : 2 * (Fintype.card V : ℤ) - (G.edgeFinset.card : ℤ) ≥ 2 := by
        by_cases hc13 : (4 : ℤ) ≤ (Fintype.card V : ℤ)
        · -- 1*n >= 4
          have s14 : (Fintype.card V : ℤ) ≥ 4 := by have hcc := hc13; omega
          have s15 : -(G.edgeFinset.card : ℤ) ≥ -6 := by linarith [hn1]
          have s16 : 2 * (Fintype.card V : ℤ) - (G.edgeFinset.card : ℤ) ≥ 2 := by linarith [s14, s15]
          linarith [s16]
        · -- 1*n <= 3
          have s17 : (Fintype.card V : ℤ) ≥ 1 := by
            have hw := card_ge_one_int (V := V)
            try push_cast at hw
            linarith [hw]
          have s18 : -(Fintype.card V : ℤ) - 2 * (G.edgeFinset.card : ℤ) + (Fintype.card V : ℤ) * (Fintype.card V : ℤ) ≥ 0 := by
            have hw := two_mul_edges_le_card_sq_sub_card_int G
            try push_cast at hw
            linarith [hw]
          have s19 : -(Fintype.card V : ℤ) ≥ -3 := by have hcc := hc13; omega
          have s20 : 4 * (Fintype.card V : ℤ) - (Fintype.card V : ℤ) * (Fintype.card V : ℤ) ≥ 3 := by
            have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 1) * (3 - (Fintype.card V : ℤ)) :=
              mul_nonneg (by linarith [s17]) (by linarith [s19])
            ring_nf at hmul ⊢
            linarith [hmul]
          have s21 : 2 * (Fintype.card V : ℤ) - (G.edgeFinset.card : ℤ) ≥ 2 := by linarith [s17, s18, s20]
          linarith [s21]
      linarith [s13]
  have heq_gallai := gallai_int G
  try push_cast at heq_gallai
  linarith [s1, heq_gallai]
