import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C76 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hp1 : ¬ G.IsBipartite) (hn1 : (G.vertexCoverNum.toNat : ℤ) ≤ 5) :
    2 * (G.indepNum : ℤ) ≥ -(G.edgeFinset.card : ℤ) + 3 * (G.minDegree : ℤ) - 1 := by
  have s1 : (G.edgeFinset.card : ℤ) - 3 * (G.minDegree : ℤ) + 2 * (G.indepNum : ℤ) ≥ -1 := by
    by_cases hc1 : (3 : ℤ) ≤ (G.cliqueNum : ℤ)
    · -- 1*omega >= 3
      have s2 : (G.edgeFinset.card : ℤ) - 3 * (G.minDegree : ℤ) + 2 * (G.indepNum : ℤ) ≥ -1 := by
        by_cases hc2 : (6 : ℤ) ≤ (Fintype.card V : ℤ)
        · -- 1*n >= 6
          have s3 : (Fintype.card V : ℤ) ≥ 6 := by have hcc := hc2; omega
          have s4 : 2 * (G.edgeFinset.card : ℤ) - (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
            have hw := handshake_min_int G
            try push_cast at hw
            linarith [hw]
          have s5 : -(G.vertexCoverNum.toNat : ℤ) ≥ -5 := by linarith [hn1]
          have s6 : (G.minDegree : ℤ) ≥ 0 := by positivity
          have s7 : -6 * (G.minDegree : ℤ) + (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
            have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 6) * ((G.minDegree : ℤ) - 0) :=
              mul_nonneg (by linarith [s3]) (by linarith [s6])
            ring_nf at hmul ⊢
            linarith [hmul]
          have s8 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
            have hw := gallai_int G
            try push_cast at hw
            linarith [hw]
          have s9 : (G.edgeFinset.card : ℤ) - 3 * (G.minDegree : ℤ) + 2 * (G.indepNum : ℤ) ≥ 2 := by linarith [s3, s4, s5, s7, s8]
          linarith [s9]
        · -- 1*n <= 5
          have s10 : (G.edgeFinset.card : ℤ) - 3 * (G.minDegree : ℤ) + 2 * (G.indepNum : ℤ) ≥ -1 := by
            by_cases hc10 : (4 : ℤ) ≤ (Fintype.card V : ℤ)
            · -- 1*n >= 4
              have s11 : (G.maxDegree : ℤ) - (G.minDegree : ℤ) ≥ 0 := by
                have hw := min_le_max_int G
                try push_cast at hw
                linarith [hw]
              have s12 : (Fintype.card V : ℤ) - (G.maxDegree : ℤ) ≥ 1 := by
                have hw := max_lt_card_int' G
                try push_cast at hw
                linarith [hw]
              have s13 : (G.indepNum : ℤ) ≥ 1 := by
                have hw := alpha_ge_one_int' G
                try push_cast at hw
                linarith [hw]
              have s14 : 2 * (G.edgeFinset.card : ℤ) - (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
                have hw := handshake_min_int G
                try push_cast at hw
                linarith [hw]
              have s15 : (G.minDegree : ℤ) ≥ 0 := by positivity
              have s16 : (Fintype.card V : ℤ) ≥ 4 := by have hcc := hc10; omega
              have s17 : -4 * (G.minDegree : ℤ) + (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
                have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 4) * ((G.minDegree : ℤ) - 0) :=
                  mul_nonneg (by linarith [s16]) (by linarith [s15])
                ring_nf at hmul ⊢
                linarith [hmul]
              have s18 : -(Fintype.card V : ℤ) ≥ -5 := by have hcc := hc10; omega
              have s19 : -(G.minDegree : ℤ) ≥ -4 := by linarith [s11, s12, s18]
              have s20 : -4 * (Fintype.card V : ℤ) - 5 * (G.minDegree : ℤ) + (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ -20 := by
                have hmul : (0 : ℤ) ≤ (5 - (Fintype.card V : ℤ)) * (4 - (G.minDegree : ℤ)) :=
                  mul_nonneg (by linarith [s18]) (by linarith [s19])
                ring_nf at hmul ⊢
                linarith [hmul]
              have s21 : 5 * (G.edgeFinset.card : ℤ) - 15 * (G.minDegree : ℤ) + 10 * (G.indepNum : ℤ) ≥ -6 := by linarith [s11, s12, s13, s14, s17, s20]
              have s22 : (G.edgeFinset.card : ℤ) - 3 * (G.minDegree : ℤ) + 2 * (G.indepNum : ℤ) ≥ -1 := by have hr := s21; omega
              linarith [s22]
            · -- 1*n <= 3
              have s23 : (G.indepNum : ℤ) ≥ 1 := by
                have hw := alpha_ge_one_int' G
                try push_cast at hw
                linarith [hw]
              have s24 : 2 * (G.edgeFinset.card : ℤ) - (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
                have hw := handshake_min_int G
                try push_cast at hw
                linarith [hw]
              have s25 : -(Fintype.card V : ℤ) - 2 * (G.edgeFinset.card : ℤ) + (Fintype.card V : ℤ) * (Fintype.card V : ℤ) ≥ 0 := by
                have hw := two_mul_edges_le_card_sq_sub_card_int G
                try push_cast at hw
                linarith [hw]
              have s26 : -(Fintype.card V : ℤ) ≥ -3 := by have hcc := hc10; omega
              have s27 : (Fintype.card V : ℤ) ≥ 1 := by
                have hw := card_ge_one_int (V := V)
                try push_cast at hw
                linarith [hw]
              have s28 : 4 * (Fintype.card V : ℤ) - (Fintype.card V : ℤ) * (Fintype.card V : ℤ) ≥ 3 := by
                have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 1) * (3 - (Fintype.card V : ℤ)) :=
                  mul_nonneg (by linarith [s27]) (by linarith [s26])
                ring_nf at hmul ⊢
                linarith [hmul]
              have s29 : -(G.edgeFinset.card : ℤ) ≥ -3 := by linarith [s25, s26, s28]
              have s30 : (G.minDegree : ℤ) ≥ 0 := by positivity
              have s31 : (G.cliqueNum : ℤ) ≥ 3 := by have hcc := hc1; omega
              have s32 : (Fintype.card V : ℤ) - (G.cliqueNum : ℤ) ≥ 0 := by
                have hw := omega_le_card_int G
                try push_cast at hw
                linarith [hw]
              have s33 : (Fintype.card V : ℤ) ≥ 3 := by linarith [s31, s32]
              have s34 : -3 * (G.minDegree : ℤ) + (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
                have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 3) * ((G.minDegree : ℤ) - 0) :=
                  mul_nonneg (by linarith [s33]) (by linarith [s30])
                ring_nf at hmul ⊢
                linarith [hmul]
              have s35 : (G.edgeFinset.card : ℤ) - 3 * (G.minDegree : ℤ) + 2 * (G.indepNum : ℤ) ≥ -1 := by linarith [s23, s24, s29, s34]
              linarith [s35]
          linarith [s10]
      linarith [s2]
    · -- 1*omega <= 2
      have s36 : (G.edgeFinset.card : ℤ) - 3 * (G.minDegree : ℤ) + 2 * (G.indepNum : ℤ) ≥ 0 := by
        by_cases hc36 : (6 : ℤ) ≤ (Fintype.card V : ℤ)
        · -- 1*n >= 6
          have s37 : (Fintype.card V : ℤ) ≥ 6 := by have hcc := hc36; omega
          have s38 : 2 * (G.edgeFinset.card : ℤ) - (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
            have hw := handshake_min_int G
            try push_cast at hw
            linarith [hw]
          have s39 : -(G.vertexCoverNum.toNat : ℤ) ≥ -5 := by linarith [hn1]
          have s40 : (G.minDegree : ℤ) ≥ 0 := by positivity
          have s41 : -6 * (G.minDegree : ℤ) + (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
            have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 6) * ((G.minDegree : ℤ) - 0) :=
              mul_nonneg (by linarith [s37]) (by linarith [s40])
            ring_nf at hmul ⊢
            linarith [hmul]
          have s42 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
            have hw := gallai_int G
            try push_cast at hw
            linarith [hw]
          have s43 : (G.edgeFinset.card : ℤ) - 3 * (G.minDegree : ℤ) + 2 * (G.indepNum : ℤ) ≥ 2 := by linarith [s37, s38, s39, s41, s42]
          linarith [s43]
        · -- 1*n <= 5
          have s44 : (G.indepNum : ℤ) ≥ 1 := by
            have hw := alpha_ge_one_int' G
            try push_cast at hw
            linarith [hw]
          have s45 : 2 * (G.edgeFinset.card : ℤ) - (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
            have hw := handshake_min_int G
            try push_cast at hw
            linarith [hw]
          have s46 : -(G.cliqueNum : ℤ) ≥ -2 := by have hcc := hc1; omega
          have s47 : -4 * (G.edgeFinset.card : ℤ) + (Fintype.card V : ℤ) * (Fintype.card V : ℤ) ≥ 0 := by
            have hw := turan_r2_int G (by linarith [s46])
            try push_cast at hw
            linarith [hw]
          have s48 : -(Fintype.card V : ℤ) ≥ -5 := by have hcc := hc36; omega
          have s49 : (Fintype.card V : ℤ) - (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
            have hw := chi_le_n_int G
            try push_cast at hw
            linarith [hw]
          have s50 : (G.chromaticNumber.toNat : ℤ) ≥ 3 := by
            have hw := not_bipartite_chi_int G hp1
            try push_cast at hw
            linarith [hw]
          have s51 : (Fintype.card V : ℤ) ≥ 3 := by linarith [s49, s50]
          have s52 : 8 * (Fintype.card V : ℤ) - (Fintype.card V : ℤ) * (Fintype.card V : ℤ) ≥ 15 := by
            have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 3) * (5 - (Fintype.card V : ℤ)) :=
              mul_nonneg (by linarith [s51]) (by linarith [s48])
            ring_nf at hmul ⊢
            linarith [hmul]
          have s53 : (G.minDegree : ℤ) ≥ 0 := by positivity
          have s54 : -3 * (G.minDegree : ℤ) + (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
            have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 3) * ((G.minDegree : ℤ) - 0) :=
              mul_nonneg (by linarith [s51]) (by linarith [s53])
            ring_nf at hmul ⊢
            linarith [hmul]
          have s55 : (G.maxDegree : ℤ) - (G.minDegree : ℤ) ≥ 0 := by
            have hw := min_le_max_int G
            try push_cast at hw
            linarith [hw]
          have s56 : (Fintype.card V : ℤ) - (G.maxDegree : ℤ) ≥ 1 := by
            have hw := max_lt_card_int' G
            try push_cast at hw
            linarith [hw]
          have s57 : -(G.minDegree : ℤ) ≥ -4 := by linarith [s55, s56, s48]
          have s58 : -4 * (Fintype.card V : ℤ) - 5 * (G.minDegree : ℤ) + (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ -20 := by
            have hmul : (0 : ℤ) ≤ (5 - (Fintype.card V : ℤ)) * (4 - (G.minDegree : ℤ)) :=
              mul_nonneg (by linarith [s48]) (by linarith [s57])
            ring_nf at hmul ⊢
            linarith [hmul]
          have s59 : -2 * (G.minDegree : ℤ) ≥ -5 := by linarith [s45, s47, s52, s58]
          have s60 : -(G.minDegree : ℤ) ≥ -2 := by have hr := s59; omega
          have s61 : -2 * (Fintype.card V : ℤ) - 5 * (G.minDegree : ℤ) + (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ -10 := by
            have hmul : (0 : ℤ) ≤ (5 - (Fintype.card V : ℤ)) * (2 - (G.minDegree : ℤ)) :=
              mul_nonneg (by linarith [s48]) (by linarith [s60])
            ring_nf at hmul ⊢
            linarith [hmul]
          have s62 : 28 * (G.edgeFinset.card : ℤ) - 84 * (G.minDegree : ℤ) + 56 * (G.indepNum : ℤ) ≥ -19 := by linarith [s44, s45, s47, s52, s54, s61]
          have s63 : (G.edgeFinset.card : ℤ) - 3 * (G.minDegree : ℤ) + 2 * (G.indepNum : ℤ) ≥ 0 := by have hr := s62; omega
          linarith [s63]
      linarith [s36]
  have heq_gallai := gallai_int G
  try push_cast at heq_gallai
  linarith [s1, heq_gallai]
