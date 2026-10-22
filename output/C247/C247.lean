import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C247 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hn1 : (G.edgeFinset.card : ℤ) ≤ 5) :
    2 * (G.edgeFinset.card : ℤ) ≤ 3 * (Fintype.card V : ℤ) + 3 * (G.maxDegree : ℤ) - 3 := by
  have s1 : 3 * (Fintype.card V : ℤ) - 2 * (G.edgeFinset.card : ℤ) + 3 * (G.maxDegree : ℤ) ≥ 3 := by
    by_cases hc1 : (3 : ℤ) ≤ (G.chromaticNumber.toNat : ℤ)
    · -- 1*chi >= 3
      have s2 : 3 * (Fintype.card V : ℤ) - 2 * (G.edgeFinset.card : ℤ) + 3 * (G.maxDegree : ℤ) ≥ 8 := by
        by_cases hc2 : (3 : ℤ) ≤ (G.cliqueNum : ℤ)
        · -- 1*omega >= 3
          have s3 : 3 * (Fintype.card V : ℤ) - 2 * (G.edgeFinset.card : ℤ) + 3 * (G.maxDegree : ℤ) ≥ 9 := by
            by_cases hc3 : (4 : ℤ) ≤ (Fintype.card V : ℤ)
            · -- 1*n >= 4
              have s4 : (G.cliqueNum : ℤ) ≥ 3 := by have hcc := hc2; omega
              have s5 : (G.maxDegree : ℤ) - (G.cliqueNum : ℤ) ≥ -1 := by
                have hw := omega_le_maxdeg_add_one_int G
                try push_cast at hw
                linarith [hw]
              have s6 : (G.maxDegree : ℤ) ≥ 2 := by linarith [s4, s5]
              have s7 : -2 * (G.edgeFinset.card : ℤ) + (Fintype.card V : ℤ) * (G.maxDegree : ℤ) ≥ 0 := by
                have hw := handshake_max_int G
                try push_cast at hw
                linarith [hw]
              have s8 : -(G.edgeFinset.card : ℤ) ≥ -5 := by linarith [hn1]
              have s9 : (Fintype.card V : ℤ) ≥ 4 := by have hcc := hc3; omega
              have s10 : (G.edgeFinset.card : ℤ) - (G.maxDegree : ℤ) ≥ 0 := by
                have hw := max_le_edges_int G
                try push_cast at hw
                linarith [hw]
              have s11 : -(G.maxDegree : ℤ) ≥ -5 := by linarith [s10, s8]
              have s12 : 5 * (Fintype.card V : ℤ) + 4 * (G.maxDegree : ℤ) - (Fintype.card V : ℤ) * (G.maxDegree : ℤ) ≥ 20 := by
                have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 4) * (5 - (G.maxDegree : ℤ)) :=
                  mul_nonneg (by linarith [s9]) (by linarith [s11])
                ring_nf at hmul ⊢
                linarith [hmul]
              have s13 : 15 * (Fintype.card V : ℤ) - 10 * (G.edgeFinset.card : ℤ) + 15 * (G.maxDegree : ℤ) ≥ 46 := by linarith [s6, s7, s8, s12]
              have s14 : 3 * (Fintype.card V : ℤ) - 2 * (G.edgeFinset.card : ℤ) + 3 * (G.maxDegree : ℤ) ≥ 10 := by have hr := s13; omega
              linarith [s14]
            · -- 1*n <= 3
              have s15 : (G.cliqueNum : ℤ) ≥ 3 := by have hcc := hc2; omega
              have s16 : (G.maxDegree : ℤ) - (G.cliqueNum : ℤ) ≥ -1 := by
                have hw := omega_le_maxdeg_add_one_int G
                try push_cast at hw
                linarith [hw]
              have s17 : -(Fintype.card V : ℤ) - 2 * (G.edgeFinset.card : ℤ) + (Fintype.card V : ℤ) * (Fintype.card V : ℤ) ≥ 0 := by
                have hw := two_mul_edges_le_card_sq_sub_card_int G
                try push_cast at hw
                linarith [hw]
              have s18 : (Fintype.card V : ℤ) ≥ 1 := by
                have hw := card_ge_one_int (V := V)
                try push_cast at hw
                linarith [hw]
              have s19 : -(Fintype.card V : ℤ) ≥ -3 := by have hcc := hc3; omega
              have s20 : 4 * (Fintype.card V : ℤ) - (Fintype.card V : ℤ) * (Fintype.card V : ℤ) ≥ 3 := by
                have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 1) * (3 - (Fintype.card V : ℤ)) :=
                  mul_nonneg (by linarith [s18]) (by linarith [s19])
                ring_nf at hmul ⊢
                linarith [hmul]
              have s21 : 3 * (Fintype.card V : ℤ) - 2 * (G.edgeFinset.card : ℤ) + 3 * (G.maxDegree : ℤ) ≥ 9 := by linarith [s15, s16, s17, s20]
              linarith [s21]
          linarith [s3]
        · -- 1*omega <= 2
          have s22 : 3 * (Fintype.card V : ℤ) - 2 * (G.edgeFinset.card : ℤ) + 3 * (G.maxDegree : ℤ) ≥ 8 := by
            by_cases hc22 : (4 : ℤ) ≤ (Fintype.card V : ℤ)
            · -- 1*n >= 4
              have s23 : (G.maxDegree : ℤ) ≥ 0 := by positivity
              have s24 : -2 * (G.edgeFinset.card : ℤ) + (Fintype.card V : ℤ) * (G.maxDegree : ℤ) ≥ 0 := by
                have hw := handshake_max_int G
                try push_cast at hw
                linarith [hw]
              have s25 : -(G.edgeFinset.card : ℤ) ≥ -5 := by linarith [hn1]
              have s26 : (Fintype.card V : ℤ) ≥ 4 := by have hcc := hc22; omega
              have s27 : (G.edgeFinset.card : ℤ) - (G.maxDegree : ℤ) ≥ 0 := by
                have hw := max_le_edges_int G
                try push_cast at hw
                linarith [hw]
              have s28 : -(G.maxDegree : ℤ) ≥ -5 := by linarith [s27, s25]
              have s29 : 5 * (Fintype.card V : ℤ) + 4 * (G.maxDegree : ℤ) - (Fintype.card V : ℤ) * (G.maxDegree : ℤ) ≥ 20 := by
                have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 4) * (5 - (G.maxDegree : ℤ)) :=
                  mul_nonneg (by linarith [s26]) (by linarith [s28])
                ring_nf at hmul ⊢
                linarith [hmul]
              have s30 : 3 * (Fintype.card V : ℤ) - 2 * (G.edgeFinset.card : ℤ) + 3 * (G.maxDegree : ℤ) ≥ 8 := by linarith [s23, s24, s25, s29]
              linarith [s30]
            · -- 1*n <= 3
              have s31 : (Fintype.card V : ℤ) - (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
                have hw := chi_le_n_int G
                try push_cast at hw
                linarith [hw]
              have s32 : (G.chromaticNumber.toNat : ℤ) ≥ 3 := by have hcc := hc1; omega
              have s33 : -2 * (G.edgeFinset.card : ℤ) + (Fintype.card V : ℤ) * (G.maxDegree : ℤ) ≥ 0 := by
                have hw := handshake_max_int G
                try push_cast at hw
                linarith [hw]
              have s34 : (G.maxDegree : ℤ) ≥ 0 := by positivity
              have s35 : -(Fintype.card V : ℤ) ≥ -3 := by have hcc := hc22; omega
              have s36 : 3 * (G.maxDegree : ℤ) - (Fintype.card V : ℤ) * (G.maxDegree : ℤ) ≥ 0 := by
                have hmul : (0 : ℤ) ≤ (3 - (Fintype.card V : ℤ)) * ((G.maxDegree : ℤ) - 0) :=
                  mul_nonneg (by linarith [s35]) (by linarith [s34])
                ring_nf at hmul ⊢
                linarith [hmul]
              have s37 : 3 * (Fintype.card V : ℤ) - 2 * (G.edgeFinset.card : ℤ) + 3 * (G.maxDegree : ℤ) ≥ 9 := by linarith [s31, s32, s33, s36]
              linarith [s37]
          linarith [s22]
      linarith [s2]
    · -- 1*chi <= 2
      have s38 : 3 * (Fintype.card V : ℤ) - 2 * (G.edgeFinset.card : ℤ) + 3 * (G.maxDegree : ℤ) ≥ 3 := by
        by_cases hc38 : (3 : ℤ) ≤ (Fintype.card V : ℤ)
        · -- 1*n >= 3
          have s39 : 3 * (Fintype.card V : ℤ) - 2 * (G.edgeFinset.card : ℤ) + 3 * (G.maxDegree : ℤ) ≥ 8 := by
            by_cases hc39 : (4 : ℤ) ≤ (Fintype.card V : ℤ)
            · -- 1*n >= 4
              have s40 : (G.maxDegree : ℤ) ≥ 0 := by positivity
              have s41 : -2 * (G.edgeFinset.card : ℤ) + (Fintype.card V : ℤ) * (G.maxDegree : ℤ) ≥ 0 := by
                have hw := handshake_max_int G
                try push_cast at hw
                linarith [hw]
              have s42 : -(G.edgeFinset.card : ℤ) ≥ -5 := by linarith [hn1]
              have s43 : (Fintype.card V : ℤ) ≥ 4 := by have hcc := hc39; omega
              have s44 : (G.edgeFinset.card : ℤ) - (G.maxDegree : ℤ) ≥ 0 := by
                have hw := max_le_edges_int G
                try push_cast at hw
                linarith [hw]
              have s45 : -(G.maxDegree : ℤ) ≥ -5 := by linarith [s44, s42]
              have s46 : 5 * (Fintype.card V : ℤ) + 4 * (G.maxDegree : ℤ) - (Fintype.card V : ℤ) * (G.maxDegree : ℤ) ≥ 20 := by
                have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 4) * (5 - (G.maxDegree : ℤ)) :=
                  mul_nonneg (by linarith [s43]) (by linarith [s45])
                ring_nf at hmul ⊢
                linarith [hmul]
              have s47 : 3 * (Fintype.card V : ℤ) - 2 * (G.edgeFinset.card : ℤ) + 3 * (G.maxDegree : ℤ) ≥ 8 := by linarith [s40, s41, s42, s46]
              linarith [s47]
            · -- 1*n <= 3
              have s48 : (Fintype.card V : ℤ) ≥ 3 := by have hcc := hc39; omega
              have s49 : -2 * (G.edgeFinset.card : ℤ) + (Fintype.card V : ℤ) * (G.maxDegree : ℤ) ≥ 0 := by
                have hw := handshake_max_int G
                try push_cast at hw
                linarith [hw]
              have s50 : (G.maxDegree : ℤ) ≥ 0 := by positivity
              have s51 : -(Fintype.card V : ℤ) ≥ -3 := by have hcc := hc39; omega
              have s52 : 3 * (G.maxDegree : ℤ) - (Fintype.card V : ℤ) * (G.maxDegree : ℤ) ≥ 0 := by
                have hmul : (0 : ℤ) ≤ (3 - (Fintype.card V : ℤ)) * ((G.maxDegree : ℤ) - 0) :=
                  mul_nonneg (by linarith [s51]) (by linarith [s50])
                ring_nf at hmul ⊢
                linarith [hmul]
              have s53 : 3 * (Fintype.card V : ℤ) - 2 * (G.edgeFinset.card : ℤ) + 3 * (G.maxDegree : ℤ) ≥ 9 := by linarith [s48, s49, s52]
              linarith [s53]
          linarith [s39]
        · -- 1*n <= 2
          have s54 : (Fintype.card V : ℤ) ≥ 1 := by
            have hw := card_ge_one_int (V := V)
            try push_cast at hw
            linarith [hw]
          have s55 : (G.edgeFinset.card : ℤ) ≥ 0 := by positivity
          have s56 : -2 * (G.edgeFinset.card : ℤ) + (Fintype.card V : ℤ) * (G.maxDegree : ℤ) ≥ 0 := by
            have hw := handshake_max_int G
            try push_cast at hw
            linarith [hw]
          have s57 : (G.maxDegree : ℤ) ≥ 0 := by positivity
          have s58 : -(Fintype.card V : ℤ) ≥ -2 := by have hcc := hc38; omega
          have s59 : 2 * (G.maxDegree : ℤ) - (Fintype.card V : ℤ) * (G.maxDegree : ℤ) ≥ 0 := by
            have hmul : (0 : ℤ) ≤ (2 - (Fintype.card V : ℤ)) * ((G.maxDegree : ℤ) - 0) :=
              mul_nonneg (by linarith [s58]) (by linarith [s57])
            ring_nf at hmul ⊢
            linarith [hmul]
          have s60 : 3 * (Fintype.card V : ℤ) - 2 * (G.edgeFinset.card : ℤ) + 3 * (G.maxDegree : ℤ) ≥ 3 := by linarith [s54, s55, s56, s59]
          linarith [s60]
      linarith [s38]
  have heq_gallai := gallai_int G
  try push_cast at heq_gallai
  linarith [s1, heq_gallai]
