import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C46 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hn1 : (G.edgeFinset.card : ℤ) ≤ 6) :
    2 * (G.edgeFinset.card : ℤ) ≤ 3 * (Fintype.card V : ℤ) := by
  have s1 : 3 * (Fintype.card V : ℤ) - 2 * (G.edgeFinset.card : ℤ) ≥ 0 := by
    by_cases hc1 : (3 : ℤ) ≤ (G.chromaticNumber.toNat : ℤ)
    · -- 1*chi >= 3
      have s2 : 3 * (Fintype.card V : ℤ) - 2 * (G.edgeFinset.card : ℤ) ≥ 0 := by
        by_cases hc2 : (3 : ℤ) ≤ (G.cliqueNum : ℤ)
        · -- 1*omega >= 3
          have s3 : 3 * (Fintype.card V : ℤ) - 2 * (G.edgeFinset.card : ℤ) ≥ 0 := by
            by_cases hc3 : (4 : ℤ) ≤ (Fintype.card V : ℤ)
            · -- 1*n >= 4
              have s4 : (Fintype.card V : ℤ) ≥ 4 := by have hcc := hc3; omega
              have s5 : -(G.edgeFinset.card : ℤ) ≥ -6 := by linarith [hn1]
              have s6 : 3 * (Fintype.card V : ℤ) - 2 * (G.edgeFinset.card : ℤ) ≥ 0 := by linarith [s4, s5]
              linarith [s6]
            · -- 1*n <= 3
              have s7 : -(Fintype.card V : ℤ) - 2 * (G.edgeFinset.card : ℤ) + (Fintype.card V : ℤ) * (Fintype.card V : ℤ) ≥ 0 := by
                have hw := two_mul_edges_le_card_sq_sub_card_int G
                try push_cast at hw
                linarith [hw]
              have s8 : (Fintype.card V : ℤ) ≥ 1 := by
                have hw := card_ge_one_int (V := V)
                try push_cast at hw
                linarith [hw]
              have s9 : -(Fintype.card V : ℤ) ≥ -3 := by have hcc := hc3; omega
              have s10 : 4 * (Fintype.card V : ℤ) - (Fintype.card V : ℤ) * (Fintype.card V : ℤ) ≥ 3 := by
                have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 1) * (3 - (Fintype.card V : ℤ)) :=
                  mul_nonneg (by linarith [s8]) (by linarith [s9])
                ring_nf at hmul ⊢
                linarith [hmul]
              have s11 : 3 * (Fintype.card V : ℤ) - 2 * (G.edgeFinset.card : ℤ) ≥ 3 := by linarith [s7, s10]
              linarith [s11]
          linarith [s3]
        · -- 1*omega <= 2
          have s12 : 3 * (Fintype.card V : ℤ) - 2 * (G.edgeFinset.card : ℤ) ≥ 0 := by
            by_cases hc12 : (4 : ℤ) ≤ (Fintype.card V : ℤ)
            · -- 1*n >= 4
              have s13 : (Fintype.card V : ℤ) ≥ 4 := by have hcc := hc12; omega
              have s14 : -(G.edgeFinset.card : ℤ) ≥ -6 := by linarith [hn1]
              have s15 : 3 * (Fintype.card V : ℤ) - 2 * (G.edgeFinset.card : ℤ) ≥ 0 := by linarith [s13, s14]
              linarith [s15]
            · -- 1*n <= 3
              have s16 : (Fintype.card V : ℤ) - (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
                have hw := chi_le_n_int G
                try push_cast at hw
                linarith [hw]
              have s17 : (G.chromaticNumber.toNat : ℤ) ≥ 3 := by have hcc := hc1; omega
              have s18 : -(G.cliqueNum : ℤ) ≥ -2 := by have hcc := hc2; omega
              have s19 : -4 * (G.edgeFinset.card : ℤ) + (Fintype.card V : ℤ) * (Fintype.card V : ℤ) ≥ 0 := by
                have hw := turan_r2_int G (by linarith [s18])
                try push_cast at hw
                linarith [hw]
              have s20 : (Fintype.card V : ℤ) ≥ 1 := by
                have hw := card_ge_one_int (V := V)
                try push_cast at hw
                linarith [hw]
              have s21 : -(Fintype.card V : ℤ) ≥ -3 := by have hcc := hc12; omega
              have s22 : 4 * (Fintype.card V : ℤ) - (Fintype.card V : ℤ) * (Fintype.card V : ℤ) ≥ 3 := by
                have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 1) * (3 - (Fintype.card V : ℤ)) :=
                  mul_nonneg (by linarith [s20]) (by linarith [s21])
                ring_nf at hmul ⊢
                linarith [hmul]
              have s23 : 6 * (Fintype.card V : ℤ) - 4 * (G.edgeFinset.card : ℤ) ≥ 9 := by linarith [s16, s17, s19, s22]
              have s24 : 3 * (Fintype.card V : ℤ) - 2 * (G.edgeFinset.card : ℤ) ≥ 5 := by have hr := s23; omega
              linarith [s24]
          linarith [s12]
      linarith [s2]
    · -- 1*chi <= 2
      have s25 : 3 * (Fintype.card V : ℤ) - 2 * (G.edgeFinset.card : ℤ) ≥ 0 := by
        by_cases hc25 : (6 : ℤ) ≤ (G.edgeFinset.card : ℤ)
        · -- 1*m >= 6
          have s26 : (Fintype.card V : ℤ) - (G.maxDegree : ℤ) ≥ 1 := by
            have hw := max_lt_card_int' G
            try push_cast at hw
            linarith [hw]
          have s27 : (G.edgeFinset.card : ℤ) ≥ 6 := by have hcc := hc25; omega
          have s28 : -2 * (G.edgeFinset.card : ℤ) + (Fintype.card V : ℤ) * (G.maxDegree : ℤ) ≥ 0 := by
            have hw := handshake_max_int G
            try push_cast at hw
            linarith [hw]
          have s29 : (G.edgeFinset.card : ℤ) - (G.maxDegree : ℤ) ≥ 0 := by
            have hw := max_le_edges_int G
            try push_cast at hw
            linarith [hw]
          have s30 : -(G.edgeFinset.card : ℤ) ≥ -6 := by linarith [hn1]
          have s31 : -(G.maxDegree : ℤ) ≥ -6 := by linarith [s29, s30]
          have s32 : (Fintype.card V : ℤ) ≥ 1 := by
            have hw := card_ge_one_int (V := V)
            try push_cast at hw
            linarith [hw]
          have s33 : 6 * (Fintype.card V : ℤ) + (G.maxDegree : ℤ) - (Fintype.card V : ℤ) * (G.maxDegree : ℤ) ≥ 6 := by
            have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 1) * (6 - (G.maxDegree : ℤ)) :=
              mul_nonneg (by linarith [s32]) (by linarith [s31])
            ring_nf at hmul ⊢
            linarith [hmul]
          have s34 : 7 * (Fintype.card V : ℤ) ≥ 19 := by linarith [s26, s27, s28, s33]
          have s35 : (Fintype.card V : ℤ) ≥ 3 := by have hr := s34; omega
          have s36 : 6 * (Fintype.card V : ℤ) + 3 * (G.maxDegree : ℤ) - (Fintype.card V : ℤ) * (G.maxDegree : ℤ) ≥ 18 := by
            have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 3) * (6 - (G.maxDegree : ℤ)) :=
              mul_nonneg (by linarith [s35]) (by linarith [s31])
            ring_nf at hmul ⊢
            linarith [hmul]
          have s37 : 3 * (Fintype.card V : ℤ) ≥ 11 := by linarith [s26, s27, s28, s36]
          have s38 : (Fintype.card V : ℤ) ≥ 4 := by have hr := s37; omega
          have s39 : 3 * (Fintype.card V : ℤ) - 2 * (G.edgeFinset.card : ℤ) ≥ 0 := by linarith [s38, s30]
          linarith [s39]
        · -- 1*m <= 5
          have s40 : 3 * (Fintype.card V : ℤ) - 2 * (G.edgeFinset.card : ℤ) ≥ 2 := by
            by_cases hc40 : (4 : ℤ) ≤ (Fintype.card V : ℤ)
            · -- 1*n >= 4
              have s41 : (Fintype.card V : ℤ) ≥ 4 := by have hcc := hc40; omega
              have s42 : -(G.edgeFinset.card : ℤ) ≥ -5 := by have hcc := hc25; omega
              have s43 : 3 * (Fintype.card V : ℤ) - 2 * (G.edgeFinset.card : ℤ) ≥ 2 := by linarith [s41, s42]
              linarith [s43]
            · -- 1*n <= 3
              have s44 : -(Fintype.card V : ℤ) - 2 * (G.edgeFinset.card : ℤ) + (Fintype.card V : ℤ) * (Fintype.card V : ℤ) ≥ 0 := by
                have hw := two_mul_edges_le_card_sq_sub_card_int G
                try push_cast at hw
                linarith [hw]
              have s45 : (Fintype.card V : ℤ) ≥ 1 := by
                have hw := card_ge_one_int (V := V)
                try push_cast at hw
                linarith [hw]
              have s46 : -(Fintype.card V : ℤ) ≥ -3 := by have hcc := hc40; omega
              have s47 : 4 * (Fintype.card V : ℤ) - (Fintype.card V : ℤ) * (Fintype.card V : ℤ) ≥ 3 := by
                have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 1) * (3 - (Fintype.card V : ℤ)) :=
                  mul_nonneg (by linarith [s45]) (by linarith [s46])
                ring_nf at hmul ⊢
                linarith [hmul]
              have s48 : 3 * (Fintype.card V : ℤ) - 2 * (G.edgeFinset.card : ℤ) ≥ 3 := by linarith [s44, s47]
              linarith [s48]
          linarith [s40]
      linarith [s25]
  have heq_gallai := gallai_int G
  try push_cast at heq_gallai
  linarith [s1, heq_gallai]
