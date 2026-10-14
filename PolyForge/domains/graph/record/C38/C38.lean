import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C38 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hn1 : (G.maxDegree : ℤ) ≤ 5) :
    2 * (G.cliqueNum : ℤ) ≤ 3 * (G.edgeFinset.card : ℤ) - 3 * (G.minDegree : ℤ) + 4 := by
  have s1 : 3 * (G.edgeFinset.card : ℤ) - 3 * (G.minDegree : ℤ) - 2 * (G.cliqueNum : ℤ) ≥ -4 := by
    by_cases hc1 : (8 : ℤ) ≤ (G.edgeFinset.card : ℤ)
    · -- 1*m >= 8
      have s2 : 3 * (G.edgeFinset.card : ℤ) - 3 * (G.minDegree : ℤ) - 2 * (G.cliqueNum : ℤ) ≥ 4 := by
        by_cases hc2 : (6 : ℤ) ≤ (Fintype.card V : ℤ)
        · -- 1*n >= 6
          have s3 : (G.maxDegree : ℤ) - (G.cliqueNum : ℤ) ≥ -1 := by
            have hw := omega_le_maxdeg_add_one_int G
            try push_cast at hw
            linarith [hw]
          have s4 : (G.edgeFinset.card : ℤ) ≥ 8 := by have hcc := hc1; omega
          have s5 : 2 * (G.edgeFinset.card : ℤ) - (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
            have hw := handshake_min_int G
            try push_cast at hw
            linarith [hw]
          have s6 : -(G.maxDegree : ℤ) ≥ -5 := by linarith [hn1]
          have s7 : (G.minDegree : ℤ) ≥ 0 := by positivity
          have s8 : (Fintype.card V : ℤ) ≥ 6 := by have hcc := hc2; omega
          have s9 : -6 * (G.minDegree : ℤ) + (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
            have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 6) * ((G.minDegree : ℤ) - 0) :=
              mul_nonneg (by linarith [s8]) (by linarith [s7])
            ring_nf at hmul ⊢
            linarith [hmul]
          have s10 : 3 * (G.edgeFinset.card : ℤ) - 3 * (G.minDegree : ℤ) - 2 * (G.cliqueNum : ℤ) ≥ 4 := by linarith [s3, s4, s5, s6, s9]
          linarith [s10]
        · -- 1*n <= 5
          have s11 : (G.chromaticNumber.toNat : ℤ) - (G.cliqueNum : ℤ) ≥ 0 := by
            have hw := omega_le_chi_int G
            try push_cast at hw
            linarith [hw]
          have s12 : (G.edgeFinset.card : ℤ) ≥ 8 := by have hcc := hc1; omega
          have s13 : 2 * (G.edgeFinset.card : ℤ) - (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
            have hw := handshake_min_int G
            try push_cast at hw
            linarith [hw]
          have s14 : (Fintype.card V : ℤ) - (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
            have hw := chi_le_n_int G
            try push_cast at hw
            linarith [hw]
          have s15 : -(Fintype.card V : ℤ) ≥ -5 := by have hcc := hc2; omega
          have s16 : -(G.chromaticNumber.toNat : ℤ) ≥ -5 := by linarith [s14, s15]
          have s17 : (G.minDegree : ℤ) ≥ 0 := by positivity
          have s18 : -(Fintype.card V : ℤ) - 2 * (G.edgeFinset.card : ℤ) + (Fintype.card V : ℤ) * (Fintype.card V : ℤ) ≥ 0 := by
            have hw := two_mul_edges_le_card_sq_sub_card_int G
            try push_cast at hw
            linarith [hw]
          have s19 : (Fintype.card V : ℤ) ≥ 1 := by
            have hw := card_ge_one_int (V := V)
            try push_cast at hw
            linarith [hw]
          have s20 : 6 * (Fintype.card V : ℤ) - (Fintype.card V : ℤ) * (Fintype.card V : ℤ) ≥ 5 := by
            have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 1) * (5 - (Fintype.card V : ℤ)) :=
              mul_nonneg (by linarith [s19]) (by linarith [s15])
            ring_nf at hmul ⊢
            linarith [hmul]
          have s21 : 5 * (Fintype.card V : ℤ) ≥ 21 := by linarith [s12, s18, s20]
          have s22 : (Fintype.card V : ℤ) ≥ 5 := by have hr := s21; omega
          have s23 : -5 * (G.minDegree : ℤ) + (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
            have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 5) * ((G.minDegree : ℤ) - 0) :=
              mul_nonneg (by linarith [s22]) (by linarith [s17])
            ring_nf at hmul ⊢
            linarith [hmul]
          have s24 : 15 * (G.edgeFinset.card : ℤ) - 15 * (G.minDegree : ℤ) - 10 * (G.cliqueNum : ℤ) ≥ 22 := by linarith [s11, s12, s13, s16, s23]
          have s25 : 3 * (G.edgeFinset.card : ℤ) - 3 * (G.minDegree : ℤ) - 2 * (G.cliqueNum : ℤ) ≥ 5 := by have hr := s24; omega
          linarith [s25]
      linarith [s2]
    · -- 1*m <= 7
      have s26 : 3 * (G.edgeFinset.card : ℤ) - 3 * (G.minDegree : ℤ) - 2 * (G.cliqueNum : ℤ) ≥ -4 := by
        by_cases hc26 : (4 : ℤ) ≤ (Fintype.card V : ℤ)
        · -- 1*n >= 4
          have s27 : (G.edgeFinset.card : ℤ) - (G.maxDegree : ℤ) ≥ 0 := by
            have hw := max_le_edges_int G
            try push_cast at hw
            linarith [hw]
          have s28 : (G.maxDegree : ℤ) - (G.cliqueNum : ℤ) ≥ -1 := by
            have hw := omega_le_maxdeg_add_one_int G
            try push_cast at hw
            linarith [hw]
          have s29 : 2 * (G.edgeFinset.card : ℤ) - (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
            have hw := handshake_min_int G
            try push_cast at hw
            linarith [hw]
          have s30 : -(G.maxDegree : ℤ) ≥ -5 := by linarith [hn1]
          have s31 : (G.minDegree : ℤ) ≥ 0 := by positivity
          have s32 : (Fintype.card V : ℤ) ≥ 4 := by have hcc := hc26; omega
          have s33 : -4 * (G.minDegree : ℤ) + (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
            have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 4) * ((G.minDegree : ℤ) - 0) :=
              mul_nonneg (by linarith [s32]) (by linarith [s31])
            ring_nf at hmul ⊢
            linarith [hmul]
          have s34 : 6 * (G.edgeFinset.card : ℤ) - 6 * (G.minDegree : ℤ) - 4 * (G.cliqueNum : ℤ) ≥ -9 := by linarith [s27, s28, s29, s30, s33]
          have s35 : 3 * (G.edgeFinset.card : ℤ) - 3 * (G.minDegree : ℤ) - 2 * (G.cliqueNum : ℤ) ≥ -4 := by have hr := s34; omega
          linarith [s35]
        · -- 1*n <= 3
          have s36 : (G.maxDegree : ℤ) - (G.minDegree : ℤ) ≥ 0 := by
            have hw := min_le_max_int G
            try push_cast at hw
            linarith [hw]
          have s37 : (G.edgeFinset.card : ℤ) - (G.maxDegree : ℤ) ≥ 0 := by
            have hw := max_le_edges_int G
            try push_cast at hw
            linarith [hw]
          have s38 : (Fintype.card V : ℤ) - (G.cliqueNum : ℤ) ≥ 0 := by
            have hw := omega_le_card_int G
            try push_cast at hw
            linarith [hw]
          have s39 : (G.maxDegree : ℤ) - (G.cliqueNum : ℤ) ≥ -1 := by
            have hw := omega_le_maxdeg_add_one_int G
            try push_cast at hw
            linarith [hw]
          have s40 : 2 * (G.edgeFinset.card : ℤ) - (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
            have hw := handshake_min_int G
            try push_cast at hw
            linarith [hw]
          have s41 : -(Fintype.card V : ℤ) ≥ -3 := by have hcc := hc26; omega
          have s42 : (Fintype.card V : ℤ) - (G.maxDegree : ℤ) ≥ 1 := by
            have hw := max_lt_card_int' G
            try push_cast at hw
            linarith [hw]
          have s43 : -(G.minDegree : ℤ) ≥ -2 := by linarith [s36, s42, s41]
          have s44 : -2 * (Fintype.card V : ℤ) - 3 * (G.minDegree : ℤ) + (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ -6 := by
            have hmul : (0 : ℤ) ≤ (3 - (Fintype.card V : ℤ)) * (2 - (G.minDegree : ℤ)) :=
              mul_nonneg (by linarith [s41]) (by linarith [s43])
            ring_nf at hmul ⊢
            linarith [hmul]
          have s45 : 9 * (G.edgeFinset.card : ℤ) - 9 * (G.minDegree : ℤ) - 6 * (G.cliqueNum : ℤ) ≥ -14 := by linarith [s36, s37, s38, s39, s40, s44]
          have s46 : 3 * (G.edgeFinset.card : ℤ) - 3 * (G.minDegree : ℤ) - 2 * (G.cliqueNum : ℤ) ≥ -4 := by have hr := s45; omega
          linarith [s46]
      linarith [s26]
  have heq_gallai := gallai_int G
  try push_cast at heq_gallai
  linarith [s1, heq_gallai]
