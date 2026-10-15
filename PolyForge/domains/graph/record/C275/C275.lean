import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C275 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hn1 : (G.cliqueNum : ℤ) ≥ 3) (hn2 : (G.edgeFinset.card : ℤ) ≥ 5) :
    (G.chromaticNumber.toNat : ℤ) ≥ -3 * (G.edgeFinset.card : ℤ) + 3 * (G.minDegree : ℤ) + 12 := by
  have s1 : 3 * (G.edgeFinset.card : ℤ) - 3 * (G.minDegree : ℤ) + (G.chromaticNumber.toNat : ℤ) ≥ 12 := by
    by_cases hc1 : (5 : ℤ) ≤ (Fintype.card V : ℤ)
    · -- 1*n >= 5
      have s2 : (G.chromaticNumber.toNat : ℤ) - (G.cliqueNum : ℤ) ≥ 0 := by
        have hw := omega_le_chi_int G
        try push_cast at hw
        linarith [hw]
      have s3 : (G.cliqueNum : ℤ) ≥ 3 := by linarith [hn1]
      have s4 : (G.edgeFinset.card : ℤ) ≥ 5 := by linarith [hn2]
      have s5 : 2 * (G.edgeFinset.card : ℤ) - (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
        have hw := handshake_min_int G
        try push_cast at hw
        linarith [hw]
      have s6 : (G.minDegree : ℤ) ≥ 0 := by positivity
      have s7 : (Fintype.card V : ℤ) ≥ 5 := by have hcc := hc1; omega
      have s8 : -5 * (G.minDegree : ℤ) + (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
        have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 5) * ((G.minDegree : ℤ) - 0) :=
          mul_nonneg (by linarith [s7]) (by linarith [s6])
        ring_nf at hmul ⊢
        linarith [hmul]
      have s9 : 3 * (G.edgeFinset.card : ℤ) - 3 * (G.minDegree : ℤ) + (G.chromaticNumber.toNat : ℤ) ≥ 12 := by linarith [s2, s3, s4, s5, s8]
      linarith [s9]
    · -- 1*n <= 4
      have s10 : 3 * (G.edgeFinset.card : ℤ) - 3 * (G.minDegree : ℤ) + (G.chromaticNumber.toNat : ℤ) ≥ 12 := by
        by_cases hc10 : (6 : ℤ) ≤ (G.edgeFinset.card : ℤ)
        · -- 1*m >= 6
          have s11 : (G.chromaticNumber.toNat : ℤ) - (G.cliqueNum : ℤ) ≥ 0 := by
            have hw := omega_le_chi_int G
            try push_cast at hw
            linarith [hw]
          have s12 : (G.maxDegree : ℤ) - (G.minDegree : ℤ) ≥ 0 := by
            have hw := min_le_max_int G
            try push_cast at hw
            linarith [hw]
          have s13 : (Fintype.card V : ℤ) - (G.maxDegree : ℤ) ≥ 1 := by
            have hw := max_lt_card_int' G
            try push_cast at hw
            linarith [hw]
          have s14 : (G.cliqueNum : ℤ) ≥ 3 := by linarith [hn1]
          have s15 : (G.edgeFinset.card : ℤ) ≥ 6 := by have hcc := hc10; omega
          have s16 : -(Fintype.card V : ℤ) ≥ -4 := by have hcc := hc1; omega
          have s17 : 3 * (G.edgeFinset.card : ℤ) - 3 * (G.minDegree : ℤ) + (G.chromaticNumber.toNat : ℤ) ≥ 12 := by linarith [s11, s12, s13, s14, s15, s16]
          linarith [s17]
        · -- 1*m <= 5
          have s18 : (G.chromaticNumber.toNat : ℤ) - (G.cliqueNum : ℤ) ≥ 0 := by
            have hw := omega_le_chi_int G
            try push_cast at hw
            linarith [hw]
          have s19 : (G.cliqueNum : ℤ) ≥ 3 := by linarith [hn1]
          have s20 : (G.chromaticNumber.toNat : ℤ) ≥ 3 := by linarith [s18, s19]
          have s21 : (G.edgeFinset.card : ℤ) ≥ 5 := by linarith [hn2]
          have s22 : 2 * (G.edgeFinset.card : ℤ) - (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
            have hw := handshake_min_int G
            try push_cast at hw
            linarith [hw]
          have s23 : -(G.edgeFinset.card : ℤ) ≥ -5 := by have hcc := hc10; omega
          have s24 : (G.minDegree : ℤ) ≥ 0 := by positivity
          have s25 : -(Fintype.card V : ℤ) - 2 * (G.edgeFinset.card : ℤ) + (Fintype.card V : ℤ) * (Fintype.card V : ℤ) ≥ 0 := by
            have hw := two_mul_edges_le_card_sq_sub_card_int G
            try push_cast at hw
            linarith [hw]
          have s26 : (Fintype.card V : ℤ) ≥ 1 := by
            have hw := card_ge_one_int (V := V)
            try push_cast at hw
            linarith [hw]
          have s27 : -(Fintype.card V : ℤ) ≥ -4 := by have hcc := hc1; omega
          have s28 : 5 * (Fintype.card V : ℤ) - (Fintype.card V : ℤ) * (Fintype.card V : ℤ) ≥ 4 := by
            have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 1) * (4 - (Fintype.card V : ℤ)) :=
              mul_nonneg (by linarith [s26]) (by linarith [s27])
            ring_nf at hmul ⊢
            linarith [hmul]
          have s29 : 2 * (Fintype.card V : ℤ) ≥ 7 := by linarith [s21, s25, s28]
          have s30 : (Fintype.card V : ℤ) ≥ 4 := by have hr := s29; omega
          have s31 : -4 * (G.minDegree : ℤ) + (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
            have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 4) * ((G.minDegree : ℤ) - 0) :=
              mul_nonneg (by linarith [s30]) (by linarith [s24])
            ring_nf at hmul ⊢
            linarith [hmul]
          have s32 : -2 * (G.minDegree : ℤ) ≥ -5 := by linarith [s22, s23, s31]
          have s33 : -(G.minDegree : ℤ) ≥ -2 := by have hr := s32; omega
          have s34 : 3 * (G.edgeFinset.card : ℤ) - 3 * (G.minDegree : ℤ) + (G.chromaticNumber.toNat : ℤ) ≥ 12 := by linarith [s20, s21, s33]
          linarith [s34]
      linarith [s10]
  have heq_gallai := gallai_int G
  try push_cast at heq_gallai
  linarith [s1, heq_gallai]
