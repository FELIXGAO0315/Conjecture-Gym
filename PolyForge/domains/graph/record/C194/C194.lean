import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C194 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hn1 : (G.cliqueNum : ℤ) ≥ (G.maxDegree : ℤ)) (hn2 : (G.edgeFinset.card : ℤ) ≥ 4) :
    2 * (G.edgeFinset.card : ℤ) ≥ -3 * (Fintype.card V : ℤ) - 3 * (G.maxDegree : ℤ) + 26 := by
  have s1 : 3 * (Fintype.card V : ℤ) + 2 * (G.edgeFinset.card : ℤ) + 3 * (G.maxDegree : ℤ) ≥ 26 := by
    by_cases hc1 : (3 : ℤ) ≤ (G.chromaticNumber.toNat : ℤ)
    · -- 1*chi >= 3
      have s2 : 3 * (Fintype.card V : ℤ) + 2 * (G.edgeFinset.card : ℤ) + 3 * (G.maxDegree : ℤ) ≥ 26 := by
        by_cases hc2 : (6 : ℤ) ≤ (G.edgeFinset.card : ℤ)
        · -- 1*m >= 6
          have s3 : 3 * (Fintype.card V : ℤ) + 2 * (G.edgeFinset.card : ℤ) + 3 * (G.maxDegree : ℤ) ≥ 27 := by
            by_cases hc3 : (3 : ℤ) ≤ (G.cliqueNum : ℤ)
            · -- 1*omega >= 3
              have s4 : (Fintype.card V : ℤ) - (G.maxDegree : ℤ) ≥ 1 := by
                have hw := max_lt_card_int' G
                try push_cast at hw
                linarith [hw]
              have s5 : (G.cliqueNum : ℤ) ≥ 3 := by have hcc := hc3; omega
              have s6 : (G.maxDegree : ℤ) - (G.cliqueNum : ℤ) ≥ -1 := by
                have hw := omega_le_maxdeg_add_one_int G
                try push_cast at hw
                linarith [hw]
              have s7 : (G.edgeFinset.card : ℤ) ≥ 6 := by have hcc := hc2; omega
              have s8 : 3 * (Fintype.card V : ℤ) + 2 * (G.edgeFinset.card : ℤ) + 3 * (G.maxDegree : ℤ) ≥ 27 := by linarith [s4, s5, s6, s7]
              linarith [s8]
            · -- 1*omega <= 2
              have s9 : (G.edgeFinset.card : ℤ) ≥ 6 := by have hcc := hc2; omega
              have s10 : -2 * (G.edgeFinset.card : ℤ) + (Fintype.card V : ℤ) * (G.maxDegree : ℤ) ≥ 0 := by
                have hw := handshake_max_int G
                try push_cast at hw
                linarith [hw]
              have s11 : -(G.maxDegree : ℤ) + (G.cliqueNum : ℤ) ≥ 0 := by linarith [hn1]
              have s12 : -(G.cliqueNum : ℤ) ≥ -2 := by have hcc := hc3; omega
              have s13 : -(G.maxDegree : ℤ) ≥ -2 := by linarith [s11, s12]
              have s14 : (Fintype.card V : ℤ) - (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
                have hw := chi_le_n_int G
                try push_cast at hw
                linarith [hw]
              have s15 : (G.chromaticNumber.toNat : ℤ) ≥ 3 := by have hcc := hc1; omega
              have s16 : (Fintype.card V : ℤ) ≥ 3 := by linarith [s14, s15]
              have s17 : 2 * (Fintype.card V : ℤ) + 3 * (G.maxDegree : ℤ) - (Fintype.card V : ℤ) * (G.maxDegree : ℤ) ≥ 6 := by
                have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 3) * (2 - (G.maxDegree : ℤ)) :=
                  mul_nonneg (by linarith [s16]) (by linarith [s13])
                ring_nf at hmul ⊢
                linarith [hmul]
              have s18 : 3 * (Fintype.card V : ℤ) + 2 * (G.edgeFinset.card : ℤ) + 3 * (G.maxDegree : ℤ) ≥ 36 := by linarith [s9, s10, s13, s17]
              linarith [s18]
          linarith [s3]
        · -- 1*m <= 5
          have s19 : 3 * (Fintype.card V : ℤ) + 2 * (G.edgeFinset.card : ℤ) + 3 * (G.maxDegree : ℤ) ≥ 26 := by
            by_cases hc19 : (3 : ℤ) ≤ (G.cliqueNum : ℤ)
            · -- 1*omega >= 3
              have s20 : (Fintype.card V : ℤ) - (G.maxDegree : ℤ) ≥ 1 := by
                have hw := max_lt_card_int' G
                try push_cast at hw
                linarith [hw]
              have s21 : (G.edgeFinset.card : ℤ) ≥ 4 := by linarith [hn2]
              have s22 : -2 * (G.edgeFinset.card : ℤ) + (Fintype.card V : ℤ) * (G.maxDegree : ℤ) ≥ 0 := by
                have hw := handshake_max_int G
                try push_cast at hw
                linarith [hw]
              have s23 : (G.chromaticNumber.toNat : ℤ) - (G.cliqueNum : ℤ) ≥ 0 := by
                have hw := omega_le_chi_int G
                try push_cast at hw
                linarith [hw]
              have s24 : (Fintype.card V : ℤ) - (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
                have hw := chi_le_n_int G
                try push_cast at hw
                linarith [hw]
              have s25 : (G.cliqueNum : ℤ) ≥ 3 := by have hcc := hc19; omega
              have s26 : (Fintype.card V : ℤ) ≥ 3 := by linarith [s23, s24, s25]
              have s27 : (G.edgeFinset.card : ℤ) - (G.maxDegree : ℤ) ≥ 0 := by
                have hw := max_le_edges_int G
                try push_cast at hw
                linarith [hw]
              have s28 : -(G.edgeFinset.card : ℤ) ≥ -5 := by have hcc := hc2; omega
              have s29 : -(G.maxDegree : ℤ) ≥ -5 := by linarith [s27, s28]
              have s30 : 5 * (Fintype.card V : ℤ) + 3 * (G.maxDegree : ℤ) - (Fintype.card V : ℤ) * (G.maxDegree : ℤ) ≥ 15 := by
                have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 3) * (5 - (G.maxDegree : ℤ)) :=
                  mul_nonneg (by linarith [s26]) (by linarith [s29])
                ring_nf at hmul ⊢
                linarith [hmul]
              have s31 : 4 * (Fintype.card V : ℤ) ≥ 13 := by linarith [s20, s21, s22, s30]
              have s32 : (Fintype.card V : ℤ) ≥ 4 := by have hr := s31; omega
              have s33 : (G.maxDegree : ℤ) - (G.cliqueNum : ℤ) ≥ -1 := by
                have hw := omega_le_maxdeg_add_one_int G
                try push_cast at hw
                linarith [hw]
              have s34 : (G.maxDegree : ℤ) ≥ 2 := by linarith [s25, s33]
              have s35 : 3 * (Fintype.card V : ℤ) + 2 * (G.edgeFinset.card : ℤ) + 3 * (G.maxDegree : ℤ) ≥ 26 := by linarith [s32, s21, s34]
              linarith [s35]
            · -- 1*omega <= 2
              have s36 : (G.edgeFinset.card : ℤ) ≥ 4 := by linarith [hn2]
              have s37 : -2 * (G.edgeFinset.card : ℤ) + (Fintype.card V : ℤ) * (G.maxDegree : ℤ) ≥ 0 := by
                have hw := handshake_max_int G
                try push_cast at hw
                linarith [hw]
              have s38 : -(G.maxDegree : ℤ) + (G.cliqueNum : ℤ) ≥ 0 := by linarith [hn1]
              have s39 : -(G.cliqueNum : ℤ) ≥ -2 := by have hcc := hc19; omega
              have s40 : -(G.maxDegree : ℤ) ≥ -2 := by linarith [s38, s39]
              have s41 : (Fintype.card V : ℤ) - (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
                have hw := chi_le_n_int G
                try push_cast at hw
                linarith [hw]
              have s42 : (G.chromaticNumber.toNat : ℤ) ≥ 3 := by have hcc := hc1; omega
              have s43 : (Fintype.card V : ℤ) ≥ 3 := by linarith [s41, s42]
              have s44 : 2 * (Fintype.card V : ℤ) + 3 * (G.maxDegree : ℤ) - (Fintype.card V : ℤ) * (G.maxDegree : ℤ) ≥ 6 := by
                have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 3) * (2 - (G.maxDegree : ℤ)) :=
                  mul_nonneg (by linarith [s43]) (by linarith [s40])
                ring_nf at hmul ⊢
                linarith [hmul]
              have s45 : 3 * (Fintype.card V : ℤ) + 2 * (G.edgeFinset.card : ℤ) + 3 * (G.maxDegree : ℤ) ≥ 26 := by linarith [s36, s37, s40, s44]
              linarith [s45]
          linarith [s19]
      linarith [s2]
    · -- 1*chi <= 2
      have s46 : (G.edgeFinset.card : ℤ) ≥ 4 := by linarith [hn2]
      have s47 : -2 * (G.edgeFinset.card : ℤ) + (Fintype.card V : ℤ) * (G.maxDegree : ℤ) ≥ 0 := by
        have hw := handshake_max_int G
        try push_cast at hw
        linarith [hw]
      have s48 : (G.chromaticNumber.toNat : ℤ) - (G.cliqueNum : ℤ) ≥ 0 := by
        have hw := omega_le_chi_int G
        try push_cast at hw
        linarith [hw]
      have s49 : -(G.maxDegree : ℤ) + (G.cliqueNum : ℤ) ≥ 0 := by linarith [hn1]
      have s50 : -(G.chromaticNumber.toNat : ℤ) ≥ -2 := by have hcc := hc1; omega
      have s51 : -(G.maxDegree : ℤ) ≥ -2 := by linarith [s48, s49, s50]
      have s52 : -(G.cliqueNum : ℤ) ≥ -2 := by linarith [s48, s50]
      have s53 : (Fintype.card V : ℤ) ≥ 1 := by
        have hw := card_ge_one_int (V := V)
        try push_cast at hw
        linarith [hw]
      have s54 : 2 * (Fintype.card V : ℤ) + (G.maxDegree : ℤ) - (Fintype.card V : ℤ) * (G.maxDegree : ℤ) ≥ 2 := by
        have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 1) * (2 - (G.maxDegree : ℤ)) :=
          mul_nonneg (by linarith [s53]) (by linarith [s51])
        ring_nf at hmul ⊢
        linarith [hmul]
      have s55 : (Fintype.card V : ℤ) ≥ 4 := by linarith [s46, s47, s49, s52, s54]
      have s56 : 2 * (Fintype.card V : ℤ) + 4 * (G.maxDegree : ℤ) - (Fintype.card V : ℤ) * (G.maxDegree : ℤ) ≥ 8 := by
        have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 4) * (2 - (G.maxDegree : ℤ)) :=
          mul_nonneg (by linarith [s55]) (by linarith [s51])
        ring_nf at hmul ⊢
        linarith [hmul]
      have s57 : 3 * (Fintype.card V : ℤ) + 2 * (G.edgeFinset.card : ℤ) + 3 * (G.maxDegree : ℤ) ≥ 26 := by linarith [s46, s47, s51, s56]
      linarith [s57]
  have heq_gallai := gallai_int G
  try push_cast at heq_gallai
  linarith [s1, heq_gallai]
