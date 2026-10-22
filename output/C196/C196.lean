import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C196 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hn1 : (G.edgeFinset.card : ℤ) ≤ 6) (hn2 : (G.cliqueNum : ℤ) ≥ (G.maxDegree : ℤ)) :
    2 * (Fintype.card V : ℤ) ≥ 3 * (G.edgeFinset.card : ℤ) - 3 * (G.maxDegree : ℤ) - 1 := by
  have s1 : 2 * (Fintype.card V : ℤ) - 3 * (G.edgeFinset.card : ℤ) + 3 * (G.maxDegree : ℤ) ≥ -1 := by
    by_cases hc1 : (4 : ℤ) ≤ (G.edgeFinset.card : ℤ)
    · -- 1*m >= 4
      have s2 : 2 * (Fintype.card V : ℤ) - 3 * (G.edgeFinset.card : ℤ) + 3 * (G.maxDegree : ℤ) ≥ -1 := by
        by_cases hc2 : (3 : ℤ) ≤ (G.cliqueNum : ℤ)
        · -- 1*omega >= 3
          have s3 : 2 * (Fintype.card V : ℤ) - 3 * (G.edgeFinset.card : ℤ) + 3 * (G.maxDegree : ℤ) ≥ -1 := by
            by_cases hc3 : (5 : ℤ) ≤ (Fintype.card V : ℤ)
            · -- 1*n >= 5
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
              have s8 : -(G.edgeFinset.card : ℤ) ≥ -6 := by linarith [hn1]
              have s9 : (Fintype.card V : ℤ) ≥ 5 := by have hcc := hc3; omega
              have s10 : (G.edgeFinset.card : ℤ) - (G.maxDegree : ℤ) ≥ 0 := by
                have hw := max_le_edges_int G
                try push_cast at hw
                linarith [hw]
              have s11 : -(G.maxDegree : ℤ) ≥ -6 := by linarith [s10, s8]
              have s12 : 6 * (Fintype.card V : ℤ) + 5 * (G.maxDegree : ℤ) - (Fintype.card V : ℤ) * (G.maxDegree : ℤ) ≥ 30 := by
                have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 5) * (6 - (G.maxDegree : ℤ)) :=
                  mul_nonneg (by linarith [s9]) (by linarith [s11])
                ring_nf at hmul ⊢
                linarith [hmul]
              have s13 : 6 * (Fintype.card V : ℤ) - 9 * (G.edgeFinset.card : ℤ) + 9 * (G.maxDegree : ℤ) ≥ -4 := by linarith [s6, s7, s8, s12]
              have s14 : 2 * (Fintype.card V : ℤ) - 3 * (G.edgeFinset.card : ℤ) + 3 * (G.maxDegree : ℤ) ≥ -1 := by have hr := s13; omega
              linarith [s14]
            · -- 1*n <= 4
              have s15 : -2 * (G.edgeFinset.card : ℤ) + (Fintype.card V : ℤ) * (G.maxDegree : ℤ) ≥ 0 := by
                have hw := handshake_max_int G
                try push_cast at hw
                linarith [hw]
              have s16 : -(Fintype.card V : ℤ) - 2 * (G.edgeFinset.card : ℤ) + (Fintype.card V : ℤ) * (Fintype.card V : ℤ) ≥ 0 := by
                have hw := two_mul_edges_le_card_sq_sub_card_int G
                try push_cast at hw
                linarith [hw]
              have s17 : -(G.edgeFinset.card : ℤ) ≥ -6 := by linarith [hn1]
              have s18 : (Fintype.card V : ℤ) ≥ 1 := by
                have hw := card_ge_one_int (V := V)
                try push_cast at hw
                linarith [hw]
              have s19 : -(Fintype.card V : ℤ) ≥ -4 := by have hcc := hc3; omega
              have s20 : 5 * (Fintype.card V : ℤ) - (Fintype.card V : ℤ) * (Fintype.card V : ℤ) ≥ 4 := by
                have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 1) * (4 - (Fintype.card V : ℤ)) :=
                  mul_nonneg (by linarith [s18]) (by linarith [s19])
                ring_nf at hmul ⊢
                linarith [hmul]
              have s21 : (G.maxDegree : ℤ) ≥ 0 := by positivity
              have s22 : 4 * (G.maxDegree : ℤ) - (Fintype.card V : ℤ) * (G.maxDegree : ℤ) ≥ 0 := by
                have hmul : (0 : ℤ) ≤ (4 - (Fintype.card V : ℤ)) * ((G.maxDegree : ℤ) - 0) :=
                  mul_nonneg (by linarith [s19]) (by linarith [s21])
                ring_nf at hmul ⊢
                linarith [hmul]
              have s23 : 2 * (Fintype.card V : ℤ) - 3 * (G.edgeFinset.card : ℤ) + 3 * (G.maxDegree : ℤ) ≥ -1 := by linarith [s15, s16, s17, s20, s22]
              linarith [s23]
          linarith [s3]
        · -- 1*omega <= 2
          have s24 : -2 * (G.edgeFinset.card : ℤ) + (Fintype.card V : ℤ) * (G.maxDegree : ℤ) ≥ 0 := by
            have hw := handshake_max_int G
            try push_cast at hw
            linarith [hw]
          have s25 : -(G.edgeFinset.card : ℤ) ≥ -6 := by linarith [hn1]
          have s26 : -(G.maxDegree : ℤ) + (G.cliqueNum : ℤ) ≥ 0 := by linarith [hn2]
          have s27 : -(G.cliqueNum : ℤ) ≥ -2 := by have hcc := hc2; omega
          have s28 : -(G.maxDegree : ℤ) ≥ -2 := by linarith [s26, s27]
          have s29 : (G.edgeFinset.card : ℤ) ≥ 4 := by have hcc := hc1; omega
          have s30 : (Fintype.card V : ℤ) ≥ 1 := by
            have hw := card_ge_one_int (V := V)
            try push_cast at hw
            linarith [hw]
          have s31 : 2 * (Fintype.card V : ℤ) + (G.maxDegree : ℤ) - (Fintype.card V : ℤ) * (G.maxDegree : ℤ) ≥ 2 := by
            have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 1) * (2 - (G.maxDegree : ℤ)) :=
              mul_nonneg (by linarith [s30]) (by linarith [s28])
            ring_nf at hmul ⊢
            linarith [hmul]
          have s32 : (Fintype.card V : ℤ) ≥ 4 := by linarith [s29, s24, s28, s31]
          have s33 : 2 * (Fintype.card V : ℤ) + 4 * (G.maxDegree : ℤ) - (Fintype.card V : ℤ) * (G.maxDegree : ℤ) ≥ 8 := by
            have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 4) * (2 - (G.maxDegree : ℤ)) :=
              mul_nonneg (by linarith [s32]) (by linarith [s28])
            ring_nf at hmul ⊢
            linarith [hmul]
          have s34 : 2 * (Fintype.card V : ℤ) - 3 * (G.edgeFinset.card : ℤ) + 3 * (G.maxDegree : ℤ) ≥ 0 := by linarith [s24, s25, s28, s33]
          linarith [s34]
      linarith [s2]
    · -- 1*m <= 3
      have s35 : 2 * (Fintype.card V : ℤ) - 3 * (G.edgeFinset.card : ℤ) + 3 * (G.maxDegree : ℤ) ≥ 2 := by
        by_cases hc35 : (1 : ℤ) ≤ (G.maxDegree : ℤ)
        · -- 1*max_deg >= 1
          have s36 : 2 * (Fintype.card V : ℤ) - 3 * (G.edgeFinset.card : ℤ) + 3 * (G.maxDegree : ℤ) ≥ 3 := by
            by_cases hc36 : (2 : ℤ) ≤ (G.maxDegree : ℤ)
            · -- 1*max_deg >= 2
              have s37 : (Fintype.card V : ℤ) - (G.maxDegree : ℤ) ≥ 1 := by
                have hw := max_lt_card_int' G
                try push_cast at hw
                linarith [hw]
              have s38 : (G.maxDegree : ℤ) ≥ 2 := by have hcc := hc36; omega
              have s39 : -(G.edgeFinset.card : ℤ) ≥ -3 := by have hcc := hc1; omega
              have s40 : 2 * (Fintype.card V : ℤ) - 3 * (G.edgeFinset.card : ℤ) + 3 * (G.maxDegree : ℤ) ≥ 3 := by linarith [s37, s38, s39]
              linarith [s40]
            · -- 1*max_deg <= 1
              have s41 : (G.edgeFinset.card : ℤ) - (G.maxDegree : ℤ) ≥ 0 := by
                have hw := max_le_edges_int G
                try push_cast at hw
                linarith [hw]
              have s42 : (G.maxDegree : ℤ) ≥ 1 := by have hcc := hc36; omega
              have s43 : -2 * (G.edgeFinset.card : ℤ) + (Fintype.card V : ℤ) * (G.maxDegree : ℤ) ≥ 0 := by
                have hw := handshake_max_int G
                try push_cast at hw
                linarith [hw]
              have s44 : (Fintype.card V : ℤ) ≥ 1 := by
                have hw := card_ge_one_int (V := V)
                try push_cast at hw
                linarith [hw]
              have s45 : -(G.maxDegree : ℤ) ≥ -1 := by have hcc := hc36; omega
              have s46 : (Fintype.card V : ℤ) + (G.maxDegree : ℤ) - (Fintype.card V : ℤ) * (G.maxDegree : ℤ) ≥ 1 := by
                have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 1) * (1 - (G.maxDegree : ℤ)) :=
                  mul_nonneg (by linarith [s44]) (by linarith [s45])
                ring_nf at hmul ⊢
                linarith [hmul]
              have s47 : 2 * (Fintype.card V : ℤ) - 3 * (G.edgeFinset.card : ℤ) + 3 * (G.maxDegree : ℤ) ≥ 4 := by linarith [s41, s42, s43, s46]
              linarith [s47]
          linarith [s36]
        · -- 1*max_deg <= 0
          have s48 : (G.indepNum : ℤ) ≥ 1 := by
            have hw := alpha_ge_one_int' G
            try push_cast at hw
            linarith [hw]
          have s49 : (G.maxDegree : ℤ) ≥ 0 := by positivity
          have s50 : (G.vertexCoverNum.toNat : ℤ) ≥ 0 := by positivity
          have s51 : -2 * (G.edgeFinset.card : ℤ) + (Fintype.card V : ℤ) * (G.maxDegree : ℤ) ≥ 0 := by
            have hw := handshake_max_int G
            try push_cast at hw
            linarith [hw]
          have s52 : (Fintype.card V : ℤ) ≥ 1 := by
            have hw := card_ge_one_int (V := V)
            try push_cast at hw
            linarith [hw]
          have s53 : -(G.maxDegree : ℤ) ≥ 0 := by have hcc := hc35; omega
          have s54 : (G.maxDegree : ℤ) - (Fintype.card V : ℤ) * (G.maxDegree : ℤ) ≥ 0 := by
            have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 1) * (0 - (G.maxDegree : ℤ)) :=
              mul_nonneg (by linarith [s52]) (by linarith [s53])
            ring_nf at hmul ⊢
            linarith [hmul]
          have s55 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
            have hw := gallai_int G
            try push_cast at hw
            linarith [hw]
          have s56 : 2 * (Fintype.card V : ℤ) - 3 * (G.edgeFinset.card : ℤ) + 3 * (G.maxDegree : ℤ) ≥ 2 := by linarith [s48, s49, s50, s51, s54, s55]
          linarith [s56]
      linarith [s35]
  have heq_gallai := gallai_int G
  try push_cast at heq_gallai
  linarith [s1, heq_gallai]
