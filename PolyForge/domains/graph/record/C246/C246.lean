import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C246 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hn1 : (G.maxDegree : ℤ) ≤ 2 * (G.chromaticNumber.toNat : ℤ)) (hn2 : (G.chromaticNumber.toNat : ℤ) ≤ 5) :
    2 * (G.minDegree : ℤ) ≤ (G.edgeFinset.card : ℤ) + 1 := by
  have s1 : (G.edgeFinset.card : ℤ) - 2 * (G.minDegree : ℤ) ≥ -1 := by
    by_cases hc1 : (3 : ℤ) ≤ (G.cliqueNum : ℤ)
    · -- 1*omega >= 3
      have s2 : (G.edgeFinset.card : ℤ) - 2 * (G.minDegree : ℤ) ≥ -1 := by
        by_cases hc2 : (9 : ℤ) ≤ (Fintype.card V : ℤ)
        · -- 1*n >= 9
          have s3 : (G.edgeFinset.card : ℤ) - (G.maxDegree : ℤ) ≥ 0 := by
            have hw := max_le_edges_int G
            try push_cast at hw
            linarith [hw]
          have s4 : (G.cliqueNum : ℤ) ≥ 3 := by have hcc := hc1; omega
          have s5 : (G.maxDegree : ℤ) - (G.cliqueNum : ℤ) ≥ -1 := by
            have hw := omega_le_maxdeg_add_one_int G
            try push_cast at hw
            linarith [hw]
          have s6 : 2 * (G.edgeFinset.card : ℤ) - (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
            have hw := handshake_min_int G
            try push_cast at hw
            linarith [hw]
          have s7 : (G.minDegree : ℤ) ≥ 0 := by positivity
          have s8 : (Fintype.card V : ℤ) ≥ 9 := by have hcc := hc2; omega
          have s9 : -9 * (G.minDegree : ℤ) + (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
            have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 9) * ((G.minDegree : ℤ) - 0) :=
              mul_nonneg (by linarith [s8]) (by linarith [s7])
            ring_nf at hmul ⊢
            linarith [hmul]
          have s10 : 9 * (G.edgeFinset.card : ℤ) - 18 * (G.minDegree : ℤ) ≥ 10 := by linarith [s3, s4, s5, s6, s9]
          have s11 : (G.edgeFinset.card : ℤ) - 2 * (G.minDegree : ℤ) ≥ 2 := by have hr := s10; omega
          linarith [s11]
        · -- 1*n <= 8
          have s12 : (G.maxDegree : ℤ) - (G.minDegree : ℤ) ≥ 0 := by
            have hw := min_le_max_int G
            try push_cast at hw
            linarith [hw]
          have s13 : (Fintype.card V : ℤ) - (G.maxDegree : ℤ) ≥ 1 := by
            have hw := max_lt_card_int' G
            try push_cast at hw
            linarith [hw]
          have s14 : 2 * (G.edgeFinset.card : ℤ) - (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
            have hw := handshake_min_int G
            try push_cast at hw
            linarith [hw]
          have s15 : (G.minDegree : ℤ) ≥ 0 := by positivity
          have s16 : (G.cliqueNum : ℤ) ≥ 3 := by have hcc := hc1; omega
          have s17 : (Fintype.card V : ℤ) - (G.cliqueNum : ℤ) ≥ 0 := by
            have hw := omega_le_card_int G
            try push_cast at hw
            linarith [hw]
          have s18 : (Fintype.card V : ℤ) ≥ 3 := by linarith [s16, s17]
          have s19 : -3 * (G.minDegree : ℤ) + (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
            have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 3) * ((G.minDegree : ℤ) - 0) :=
              mul_nonneg (by linarith [s18]) (by linarith [s15])
            ring_nf at hmul ⊢
            linarith [hmul]
          have s20 : -(Fintype.card V : ℤ) ≥ -8 := by have hcc := hc2; omega
          have s21 : (Fintype.card V : ℤ) ≥ 1 := by
            have hw := card_ge_one_int (V := V)
            try push_cast at hw
            linarith [hw]
          have s22 : 9 * (Fintype.card V : ℤ) - (Fintype.card V : ℤ) * (Fintype.card V : ℤ) ≥ 8 := by
            have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 1) * (8 - (Fintype.card V : ℤ)) :=
              mul_nonneg (by linarith [s21]) (by linarith [s20])
            ring_nf at hmul ⊢
            linarith [hmul]
          have s23 : (G.chromaticNumber.toNat : ℤ) - (G.cliqueNum : ℤ) ≥ 0 := by
            have hw := omega_le_chi_int G
            try push_cast at hw
            linarith [hw]
          have s24 : -(G.chromaticNumber.toNat : ℤ) ≥ -5 := by linarith [hn2]
          have s25 : -(G.cliqueNum : ℤ) ≥ -5 := by linarith [s23, s24]
          have s26 : -10 * (G.edgeFinset.card : ℤ) + 4 * (Fintype.card V : ℤ) * (Fintype.card V : ℤ) ≥ 0 := by
            have hw := turan_r5_int G (by linarith [s25])
            try push_cast at hw
            linarith [hw]
          have s27 : -(G.minDegree : ℤ) ≥ -7 := by linarith [s12, s13, s20]
          have s28 : -7 * (Fintype.card V : ℤ) - 8 * (G.minDegree : ℤ) + (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ -56 := by
            have hmul : (0 : ℤ) ≤ (8 - (Fintype.card V : ℤ)) * (7 - (G.minDegree : ℤ)) :=
              mul_nonneg (by linarith [s20]) (by linarith [s27])
            ring_nf at hmul ⊢
            linarith [hmul]
          have s29 : -5 * (G.minDegree : ℤ) ≥ -32 := by linarith [s14, s20, s22, s26, s28]
          have s30 : -(G.minDegree : ℤ) ≥ -6 := by have hr := s29; omega
          have s31 : -6 * (Fintype.card V : ℤ) - 8 * (G.minDegree : ℤ) + (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ -48 := by
            have hmul : (0 : ℤ) ≤ (8 - (Fintype.card V : ℤ)) * (6 - (G.minDegree : ℤ)) :=
              mul_nonneg (by linarith [s20]) (by linarith [s30])
            ring_nf at hmul ⊢
            linarith [hmul]
          have s32 : 11 * (G.edgeFinset.card : ℤ) - 22 * (G.minDegree : ℤ) ≥ -21 := by linarith [s12, s13, s14, s19, s31]
          have s33 : (G.edgeFinset.card : ℤ) - 2 * (G.minDegree : ℤ) ≥ -1 := by have hr := s32; omega
          linarith [s33]
      linarith [s2]
    · -- 1*omega <= 2
      have s34 : (G.edgeFinset.card : ℤ) - 2 * (G.minDegree : ℤ) ≥ -1 := by
        by_cases hc34 : (3 : ℤ) ≤ (Fintype.card V : ℤ)
        · -- 1*n >= 3
          have s35 : (G.edgeFinset.card : ℤ) - 2 * (G.minDegree : ℤ) ≥ -1 := by
            by_cases hc35 : (9 : ℤ) ≤ (Fintype.card V : ℤ)
            · -- 1*n >= 9
              have s36 : (G.edgeFinset.card : ℤ) ≥ 0 := by positivity
              have s37 : 2 * (G.edgeFinset.card : ℤ) - (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
                have hw := handshake_min_int G
                try push_cast at hw
                linarith [hw]
              have s38 : (G.minDegree : ℤ) ≥ 0 := by positivity
              have s39 : (Fintype.card V : ℤ) ≥ 9 := by have hcc := hc35; omega
              have s40 : -9 * (G.minDegree : ℤ) + (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
                have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 9) * ((G.minDegree : ℤ) - 0) :=
                  mul_nonneg (by linarith [s39]) (by linarith [s38])
                ring_nf at hmul ⊢
                linarith [hmul]
              have s41 : (G.edgeFinset.card : ℤ) - 2 * (G.minDegree : ℤ) ≥ 0 := by linarith [s36, s37, s40]
              linarith [s41]
            · -- 1*n <= 8
              have s42 : (G.maxDegree : ℤ) - (G.minDegree : ℤ) ≥ 0 := by
                have hw := min_le_max_int G
                try push_cast at hw
                linarith [hw]
              have s43 : (Fintype.card V : ℤ) - (G.maxDegree : ℤ) ≥ 1 := by
                have hw := max_lt_card_int' G
                try push_cast at hw
                linarith [hw]
              have s44 : 2 * (G.edgeFinset.card : ℤ) - (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
                have hw := handshake_min_int G
                try push_cast at hw
                linarith [hw]
              have s45 : (G.minDegree : ℤ) ≥ 0 := by positivity
              have s46 : (Fintype.card V : ℤ) ≥ 3 := by have hcc := hc35; omega
              have s47 : -3 * (G.minDegree : ℤ) + (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
                have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 3) * ((G.minDegree : ℤ) - 0) :=
                  mul_nonneg (by linarith [s46]) (by linarith [s45])
                ring_nf at hmul ⊢
                linarith [hmul]
              have s48 : -(Fintype.card V : ℤ) ≥ -8 := by have hcc := hc35; omega
              have s49 : -(G.cliqueNum : ℤ) ≥ -2 := by have hcc := hc1; omega
              have s50 : -4 * (G.edgeFinset.card : ℤ) + (Fintype.card V : ℤ) * (Fintype.card V : ℤ) ≥ 0 := by
                have hw := turan_r2_int G (by linarith [s49])
                try push_cast at hw
                linarith [hw]
              have s51 : 11 * (Fintype.card V : ℤ) - (Fintype.card V : ℤ) * (Fintype.card V : ℤ) ≥ 24 := by
                have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 3) * (8 - (Fintype.card V : ℤ)) :=
                  mul_nonneg (by linarith [s46]) (by linarith [s48])
                ring_nf at hmul ⊢
                linarith [hmul]
              have s52 : -(G.minDegree : ℤ) ≥ -7 := by linarith [s42, s43, s48]
              have s53 : -7 * (Fintype.card V : ℤ) - 8 * (G.minDegree : ℤ) + (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ -56 := by
                have hmul : (0 : ℤ) ≤ (8 - (Fintype.card V : ℤ)) * (7 - (G.minDegree : ℤ)) :=
                  mul_nonneg (by linarith [s48]) (by linarith [s52])
                ring_nf at hmul ⊢
                linarith [hmul]
              have s54 : -19 * (G.minDegree : ℤ) ≥ -85 := by linarith [s42, s43, s44, s50, s51, s53]
              have s55 : -(G.minDegree : ℤ) ≥ -4 := by have hr := s54; omega
              have s56 : -4 * (Fintype.card V : ℤ) - 8 * (G.minDegree : ℤ) + (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ -32 := by
                have hmul : (0 : ℤ) ≤ (8 - (Fintype.card V : ℤ)) * (4 - (G.minDegree : ℤ)) :=
                  mul_nonneg (by linarith [s48]) (by linarith [s55])
                ring_nf at hmul ⊢
                linarith [hmul]
              have s57 : 9 * (G.edgeFinset.card : ℤ) - 18 * (G.minDegree : ℤ) ≥ -14 := by linarith [s42, s43, s44, s47, s56]
              have s58 : (G.edgeFinset.card : ℤ) - 2 * (G.minDegree : ℤ) ≥ -1 := by have hr := s57; omega
              linarith [s58]
          linarith [s35]
        · -- 1*n <= 2
          have s59 : (G.maxDegree : ℤ) - (G.minDegree : ℤ) ≥ 0 := by
            have hw := min_le_max_int G
            try push_cast at hw
            linarith [hw]
          have s60 : (Fintype.card V : ℤ) - (G.maxDegree : ℤ) ≥ 1 := by
            have hw := max_lt_card_int' G
            try push_cast at hw
            linarith [hw]
          have s61 : (G.edgeFinset.card : ℤ) - (G.maxDegree : ℤ) ≥ 0 := by
            have hw := max_le_edges_int G
            try push_cast at hw
            linarith [hw]
          have s62 : -(Fintype.card V : ℤ) ≥ -2 := by have hcc := hc34; omega
          have s63 : (G.edgeFinset.card : ℤ) - 2 * (G.minDegree : ℤ) ≥ -1 := by linarith [s59, s60, s61, s62]
          linarith [s63]
      linarith [s34]
  have heq_gallai := gallai_int G
  try push_cast at heq_gallai
  linarith [s1, heq_gallai]
