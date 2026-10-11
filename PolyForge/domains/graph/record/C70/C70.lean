import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C70 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hn1 : (G.chromaticNumber.toNat : ℤ) ≤ 5) :
    2 * (G.cliqueNum : ℤ) ≤ 3 * (G.edgeFinset.card : ℤ) - 3 * (G.minDegree : ℤ) + 4 := by
  have s1 : 3 * (G.edgeFinset.card : ℤ) - 3 * (G.minDegree : ℤ) - 2 * (G.cliqueNum : ℤ) ≥ -4 := by
    by_cases hc1 : (2 : ℤ) ≤ (G.edgeFinset.card : ℤ)
    · -- 1*m >= 2
      have s2 : 3 * (G.edgeFinset.card : ℤ) - 3 * (G.minDegree : ℤ) - 2 * (G.cliqueNum : ℤ) ≥ -3 := by
        by_cases hc2 : (2 : ℤ) ≤ (G.minDegree : ℤ)
        · -- 1*min_deg >= 2
          have s3 : (Fintype.card V : ℤ) - (G.maxDegree : ℤ) ≥ 1 := by
            have hw := max_lt_card_int' G
            try push_cast at hw
            linarith [hw]
          have s4 : (Fintype.card V : ℤ) - (G.cliqueNum : ℤ) ≥ 0 := by
            have hw := omega_le_card_int G
            try push_cast at hw
            linarith [hw]
          have s5 : (G.maxDegree : ℤ) - (G.minDegree : ℤ) ≥ 0 := by
            have hw := min_le_max_int G
            try push_cast at hw
            linarith [hw]
          have s6 : (G.minDegree : ℤ) ≥ 2 := by have hcc := hc2; omega
          have s7 : (G.maxDegree : ℤ) ≥ 2 := by linarith [s5, s6]
          have s8 : 2 * (G.edgeFinset.card : ℤ) - (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
            have hw := handshake_min_int G
            try push_cast at hw
            linarith [hw]
          have s9 : (G.chromaticNumber.toNat : ℤ) - (G.cliqueNum : ℤ) ≥ 0 := by
            have hw := omega_le_chi_int G
            try push_cast at hw
            linarith [hw]
          have s10 : (Fintype.card V : ℤ) - (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
            have hw := chi_le_n_int G
            try push_cast at hw
            linarith [hw]
          have s11 : (Fintype.card V : ℤ) ≥ 1 := by
            have hw := card_ge_one_int (V := V)
            try push_cast at hw
            linarith [hw]
          have s12 : -2 * (Fintype.card V : ℤ) - (G.minDegree : ℤ) + (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ -2 := by
            have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 1) * ((G.minDegree : ℤ) - 2) :=
              mul_nonneg (by linarith [s11]) (by linarith [s6])
            ring_nf at hmul ⊢
            linarith [hmul]
          have s13 : 3 * (G.edgeFinset.card : ℤ) - 2 * (G.cliqueNum : ℤ) ≥ 3 := by linarith [s9, s10, s5, s3, s6, s8, s12]
          have s14 : (Fintype.card V : ℤ) ≥ 3 := by linarith [s5, s3, s6]
          have s15 : -2 * (Fintype.card V : ℤ) - 3 * (G.minDegree : ℤ) + (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ -6 := by
            have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 3) * ((G.minDegree : ℤ) - 2) :=
              mul_nonneg (by linarith [s14]) (by linarith [s6])
            ring_nf at hmul ⊢
            linarith [hmul]
          have s16 : 3 * (G.edgeFinset.card : ℤ) - 3 * (G.minDegree : ℤ) - 2 * (G.cliqueNum : ℤ) ≥ -3 := by linarith [s3, s4, s7, s8, s13, s15]
          linarith [s16]
        · -- 1*min_deg <= 1
          have s17 : (G.edgeFinset.card : ℤ) - (G.maxDegree : ℤ) ≥ 0 := by
            have hw := max_le_edges_int G
            try push_cast at hw
            linarith [hw]
          have s18 : (G.maxDegree : ℤ) - (G.cliqueNum : ℤ) ≥ -1 := by
            have hw := omega_le_maxdeg_add_one_int G
            try push_cast at hw
            linarith [hw]
          have s19 : (G.edgeFinset.card : ℤ) ≥ 2 := by have hcc := hc1; omega
          have s20 : -(G.minDegree : ℤ) ≥ -1 := by have hcc := hc2; omega
          have s21 : 3 * (G.edgeFinset.card : ℤ) - 3 * (G.minDegree : ℤ) - 2 * (G.cliqueNum : ℤ) ≥ -3 := by linarith [s17, s18, s19, s20]
          linarith [s21]
      linarith [s2]
    · -- 1*m <= 1
      have s22 : (G.maxDegree : ℤ) - (G.minDegree : ℤ) ≥ 0 := by
        have hw := min_le_max_int G
        try push_cast at hw
        linarith [hw]
      have s23 : (G.edgeFinset.card : ℤ) - (G.maxDegree : ℤ) ≥ 0 := by
        have hw := max_le_edges_int G
        try push_cast at hw
        linarith [hw]
      have s24 : (G.maxDegree : ℤ) - (G.cliqueNum : ℤ) ≥ -1 := by
        have hw := omega_le_maxdeg_add_one_int G
        try push_cast at hw
        linarith [hw]
      have s25 : -(G.edgeFinset.card : ℤ) ≥ -1 := by have hcc := hc1; omega
      have s26 : 3 * (G.edgeFinset.card : ℤ) - 3 * (G.minDegree : ℤ) - 2 * (G.cliqueNum : ℤ) ≥ -4 := by linarith [s22, s23, s24, s25]
      linarith [s26]
  linarith [s1]
