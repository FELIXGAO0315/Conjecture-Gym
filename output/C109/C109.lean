import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C109 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hn1 : (G.chromaticNumber.toNat : ℤ) ≥ 2 * (G.maxDegree : ℤ)) (hn2 : (G.edgeFinset.card : ℤ) ≤ 5) :
    2 * (Fintype.card V : ℤ) ≥ 3 * (G.edgeFinset.card : ℤ) - 3 * (G.chromaticNumber.toNat : ℤ) + 5 := by
  have s1 : 2 * (Fintype.card V : ℤ) - 3 * (G.edgeFinset.card : ℤ) + 3 * (G.chromaticNumber.toNat : ℤ) ≥ 5 := by
    by_cases hc1 : (3 : ℤ) ≤ (G.chromaticNumber.toNat : ℤ)
    · -- 1*chi >= 3
      have s2 : 2 * (Fintype.card V : ℤ) - 3 * (G.edgeFinset.card : ℤ) + 3 * (G.chromaticNumber.toNat : ℤ) ≥ 6 := by
        by_cases hc2 : (4 : ℤ) ≤ (G.chromaticNumber.toNat : ℤ)
        · -- 1*chi >= 4
          have s3 : (G.chromaticNumber.toNat : ℤ) ≥ 4 := by have hcc := hc2; omega
          have s4 : -2 * (G.edgeFinset.card : ℤ) + (Fintype.card V : ℤ) * (G.maxDegree : ℤ) ≥ 0 := by
            have hw := handshake_max_int G
            try push_cast at hw
            linarith [hw]
          have s5 : -2 * (G.maxDegree : ℤ) + (G.chromaticNumber.toNat : ℤ) ≥ 0 := by linarith [hn1]
          have s6 : -(G.edgeFinset.card : ℤ) ≥ -5 := by linarith [hn2]
          have s7 : (Fintype.card V : ℤ) - (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
            have hw := chi_le_n_int G
            try push_cast at hw
            linarith [hw]
          have s8 : (Fintype.card V : ℤ) ≥ 4 := by linarith [s7, s3]
          have s9 : (G.edgeFinset.card : ℤ) - (G.maxDegree : ℤ) ≥ 0 := by
            have hw := max_le_edges_int G
            try push_cast at hw
            linarith [hw]
          have s10 : -(G.maxDegree : ℤ) ≥ -5 := by linarith [s9, s6]
          have s11 : 5 * (Fintype.card V : ℤ) + 4 * (G.maxDegree : ℤ) - (Fintype.card V : ℤ) * (G.maxDegree : ℤ) ≥ 20 := by
            have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 4) * (5 - (G.maxDegree : ℤ)) :=
              mul_nonneg (by linarith [s8]) (by linarith [s10])
            ring_nf at hmul ⊢
            linarith [hmul]
          have s12 : 10 * (Fintype.card V : ℤ) - 15 * (G.edgeFinset.card : ℤ) + 15 * (G.chromaticNumber.toNat : ℤ) ≥ 29 := by linarith [s3, s4, s5, s6, s11]
          have s13 : 2 * (Fintype.card V : ℤ) - 3 * (G.edgeFinset.card : ℤ) + 3 * (G.chromaticNumber.toNat : ℤ) ≥ 6 := by have hr := s12; omega
          linarith [s13]
        · -- 1*chi <= 3
          have s14 : (G.chromaticNumber.toNat : ℤ) ≥ 3 := by have hcc := hc2; omega
          have s15 : (Fintype.card V : ℤ) - (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
            have hw := chi_le_n_int G
            try push_cast at hw
            linarith [hw]
          have s16 : (Fintype.card V : ℤ) ≥ 3 := by linarith [s15, s14]
          have s17 : -2 * (G.edgeFinset.card : ℤ) + (Fintype.card V : ℤ) * (G.maxDegree : ℤ) ≥ 0 := by
            have hw := handshake_max_int G
            try push_cast at hw
            linarith [hw]
          have s18 : -2 * (G.maxDegree : ℤ) + (G.chromaticNumber.toNat : ℤ) ≥ 0 := by linarith [hn1]
          have s19 : -(G.chromaticNumber.toNat : ℤ) ≥ -3 := by have hcc := hc2; omega
          have s20 : -2 * (G.maxDegree : ℤ) ≥ -3 := by linarith [s18, s19]
          have s21 : -(G.maxDegree : ℤ) ≥ -1 := by have hr := s20; omega
          have s22 : (Fintype.card V : ℤ) + 3 * (G.maxDegree : ℤ) - (Fintype.card V : ℤ) * (G.maxDegree : ℤ) ≥ 3 := by
            have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 3) * (1 - (G.maxDegree : ℤ)) :=
              mul_nonneg (by linarith [s16]) (by linarith [s21])
            ring_nf at hmul ⊢
            linarith [hmul]
          have s23 : 4 * (Fintype.card V : ℤ) - 6 * (G.edgeFinset.card : ℤ) + 6 * (G.chromaticNumber.toNat : ℤ) ≥ 21 := by linarith [s14, s16, s17, s21, s22]
          have s24 : 2 * (Fintype.card V : ℤ) - 3 * (G.edgeFinset.card : ℤ) + 3 * (G.chromaticNumber.toNat : ℤ) ≥ 11 := by have hr := s23; omega
          linarith [s24]
      linarith [s2]
    · -- 1*chi <= 2
      have s25 : (Fintype.card V : ℤ) - (G.maxDegree : ℤ) ≥ 1 := by
        have hw := max_lt_card_int' G
        try push_cast at hw
        linarith [hw]
      have s26 : (G.chromaticNumber.toNat : ℤ) ≥ 1 := by
        have hw := chi_ge_one_int' G
        try push_cast at hw
        linarith [hw]
      have s27 : -2 * (G.edgeFinset.card : ℤ) + (Fintype.card V : ℤ) * (G.maxDegree : ℤ) ≥ 0 := by
        have hw := handshake_max_int G
        try push_cast at hw
        linarith [hw]
      have s28 : -2 * (G.maxDegree : ℤ) + (G.chromaticNumber.toNat : ℤ) ≥ 0 := by linarith [hn1]
      have s29 : (Fintype.card V : ℤ) ≥ 1 := by
        have hw := card_ge_one_int (V := V)
        try push_cast at hw
        linarith [hw]
      have s30 : -(G.chromaticNumber.toNat : ℤ) ≥ -2 := by have hcc := hc1; omega
      have s31 : -(G.maxDegree : ℤ) ≥ -1 := by linarith [s28, s30]
      have s32 : (Fintype.card V : ℤ) + (G.maxDegree : ℤ) - (Fintype.card V : ℤ) * (G.maxDegree : ℤ) ≥ 1 := by
        have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 1) * (1 - (G.maxDegree : ℤ)) :=
          mul_nonneg (by linarith [s29]) (by linarith [s31])
        ring_nf at hmul ⊢
        linarith [hmul]
      have s33 : 4 * (Fintype.card V : ℤ) - 6 * (G.edgeFinset.card : ℤ) + 6 * (G.chromaticNumber.toNat : ℤ) ≥ 9 := by linarith [s25, s26, s27, s28, s32]
      have s34 : 2 * (Fintype.card V : ℤ) - 3 * (G.edgeFinset.card : ℤ) + 3 * (G.chromaticNumber.toNat : ℤ) ≥ 5 := by have hr := s33; omega
      linarith [s34]
  have heq_gallai := gallai_int G
  try push_cast at heq_gallai
  linarith [s1, heq_gallai]
