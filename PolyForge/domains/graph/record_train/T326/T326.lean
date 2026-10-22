import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem T326 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hn1 : (G.cliqueNum : ℤ) ≥ (G.maxDegree : ℤ)) :
    2 * (G.minDegree : ℤ) ≤ 3 * (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) - 5 := by
  have s1 : -2 * (G.minDegree : ℤ) + 3 * (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) ≥ 5 := by
    by_cases hc1 : (3 : ℤ) ≤ (G.chromaticNumber.toNat : ℤ)
    · -- 1*chi >= 3
      have s2 : (G.chromaticNumber.toNat : ℤ) - (G.cliqueNum : ℤ) ≥ 0 := by
        have hw := omega_le_chi_int G
        try push_cast at hw
        linarith [hw]
      have s3 : (G.maxDegree : ℤ) - (G.minDegree : ℤ) ≥ 0 := by
        have hw := min_le_max_int G
        try push_cast at hw
        linarith [hw]
      have s4 : (G.chromaticNumber.toNat : ℤ) ≥ 3 := by have hcc := hc1; omega
      have s5 : (G.indepNum : ℤ) ≥ 1 := by
        have hw := alpha_ge_one_int' G
        try push_cast at hw
        linarith [hw]
      have s6 : -(G.maxDegree : ℤ) + (G.cliqueNum : ℤ) ≥ 0 := by linarith [hn1]
      have s7 : -2 * (G.minDegree : ℤ) + 3 * (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) ≥ 5 := by linarith [s2, s3, s4, s5, s6]
      linarith [s7]
    · -- 1*chi <= 2
      have s8 : -2 * (G.minDegree : ℤ) + 3 * (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) ≥ 5 := by
        by_cases hc8 : (2 : ℤ) ≤ (G.edgeFinset.card : ℤ)
        · -- 1*m >= 2
          have s9 : (G.chromaticNumber.toNat : ℤ) - (G.cliqueNum : ℤ) ≥ 0 := by
            have hw := omega_le_chi_int G
            try push_cast at hw
            linarith [hw]
          have s10 : (G.maxDegree : ℤ) - (G.minDegree : ℤ) ≥ 0 := by
            have hw := min_le_max_int G
            try push_cast at hw
            linarith [hw]
          have s11 : (Fintype.card V : ℤ) - (G.maxDegree : ℤ) ≥ 1 := by
            have hw := max_lt_card_int' G
            try push_cast at hw
            linarith [hw]
          have s12 : (G.edgeFinset.card : ℤ) ≥ 2 := by have hcc := hc8; omega
          have s13 : -2 * (G.edgeFinset.card : ℤ) + (Fintype.card V : ℤ) * (G.maxDegree : ℤ) ≥ 0 := by
            have hw := handshake_max_int G
            try push_cast at hw
            linarith [hw]
          have s14 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
            have hw := card_le_alpha_chi_int G
            try push_cast at hw
            linarith [hw]
          have s15 : -(G.chromaticNumber.toNat : ℤ) ≥ -2 := by have hcc := hc1; omega
          have s16 : (G.indepNum : ℤ) ≥ 1 := by
            have hw := alpha_ge_one_int' G
            try push_cast at hw
            linarith [hw]
          have s17 : (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 2 := by
            have hmul : (0 : ℤ) ≤ ((G.indepNum : ℤ) - 1) * (2 - (G.chromaticNumber.toNat : ℤ)) :=
              mul_nonneg (by linarith [s16]) (by linarith [s15])
            ring_nf at hmul ⊢
            linarith [hmul]
          have s18 : (Fintype.card V : ℤ) ≥ 1 := by
            have hw := card_ge_one_int (V := V)
            try push_cast at hw
            linarith [hw]
          have s19 : -(G.maxDegree : ℤ) + (G.cliqueNum : ℤ) ≥ 0 := by linarith [hn1]
          have s20 : -(G.maxDegree : ℤ) ≥ -2 := by linarith [s9, s19, s15]
          have s21 : 2 * (Fintype.card V : ℤ) + (G.maxDegree : ℤ) - (Fintype.card V : ℤ) * (G.maxDegree : ℤ) ≥ 2 := by
            have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 1) * (2 - (G.maxDegree : ℤ)) :=
              mul_nonneg (by linarith [s18]) (by linarith [s20])
            ring_nf at hmul ⊢
            linarith [hmul]
          have s22 : 6 * (G.indepNum : ℤ) ≥ 7 := by linarith [s11, s12, s13, s14, s15, s17, s21]
          have s23 : (G.indepNum : ℤ) ≥ 2 := by have hr := s22; omega
          have s24 : 2 * (G.edgeFinset.card : ℤ) - (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
            have hw := handshake_min_int G
            try push_cast at hw
            linarith [hw]
          have s25 : 2 * (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 4 := by
            have hmul : (0 : ℤ) ≤ ((G.indepNum : ℤ) - 2) * (2 - (G.chromaticNumber.toNat : ℤ)) :=
              mul_nonneg (by linarith [s23]) (by linarith [s15])
            ring_nf at hmul ⊢
            linarith [hmul]
          have s26 : 3 * (Fintype.card V : ℤ) ≥ 7 := by linarith [s11, s12, s13, s21]
          have s27 : (Fintype.card V : ℤ) ≥ 3 := by have hr := s26; omega
          have s28 : 2 * (Fintype.card V : ℤ) + 3 * (G.maxDegree : ℤ) - (Fintype.card V : ℤ) * (G.maxDegree : ℤ) ≥ 6 := by
            have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 3) * (2 - (G.maxDegree : ℤ)) :=
              mul_nonneg (by linarith [s27]) (by linarith [s20])
            ring_nf at hmul ⊢
            linarith [hmul]
          have s29 : (G.minDegree : ℤ) ≥ 0 := by positivity
          have s30 : -3 * (G.minDegree : ℤ) + (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
            have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 3) * ((G.minDegree : ℤ) - 0) :=
              mul_nonneg (by linarith [s27]) (by linarith [s29])
            ring_nf at hmul ⊢
            linarith [hmul]
          have s31 : -4 * (G.minDegree : ℤ) + 6 * (G.chromaticNumber.toNat : ℤ) + 4 * (G.indepNum : ℤ) ≥ 11 := by linarith [s9, s10, s23, s24, s13, s14, s19, s25, s28, s30]
          have s32 : -2 * (G.minDegree : ℤ) + 3 * (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) ≥ 6 := by have hr := s31; omega
          linarith [s32]
        · -- 1*m <= 1
          have s33 : -2 * (G.minDegree : ℤ) + 3 * (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) ≥ 5 := by
            by_cases hc33 : (2 : ℤ) ≤ (G.indepNum : ℤ)
            · -- 1*alpha >= 2
              have s34 : (G.maxDegree : ℤ) - (G.minDegree : ℤ) ≥ 0 := by
                have hw := min_le_max_int G
                try push_cast at hw
                linarith [hw]
              have s35 : (G.edgeFinset.card : ℤ) - (G.maxDegree : ℤ) ≥ 0 := by
                have hw := max_le_edges_int G
                try push_cast at hw
                linarith [hw]
              have s36 : (G.chromaticNumber.toNat : ℤ) ≥ 1 := by
                have hw := chi_ge_one_int' G
                try push_cast at hw
                linarith [hw]
              have s37 : (G.indepNum : ℤ) ≥ 2 := by have hcc := hc33; omega
              have s38 : -(G.edgeFinset.card : ℤ) ≥ -1 := by have hcc := hc8; omega
              have s39 : -2 * (G.minDegree : ℤ) + 3 * (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) ≥ 5 := by linarith [s34, s35, s36, s37, s38]
              linarith [s39]
            · -- 1*alpha <= 1
              have s40 : (G.maxDegree : ℤ) - (G.minDegree : ℤ) ≥ 0 := by
                have hw := min_le_max_int G
                try push_cast at hw
                linarith [hw]
              have s41 : (Fintype.card V : ℤ) - (G.maxDegree : ℤ) ≥ 1 := by
                have hw := max_lt_card_int' G
                try push_cast at hw
                linarith [hw]
              have s42 : (G.chromaticNumber.toNat : ℤ) ≥ 1 := by
                have hw := chi_ge_one_int' G
                try push_cast at hw
                linarith [hw]
              have s43 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
                have hw := card_le_alpha_chi_int G
                try push_cast at hw
                linarith [hw]
              have s44 : -(G.indepNum : ℤ) ≥ -1 := by have hcc := hc33; omega
              have s45 : (G.indepNum : ℤ) ≥ 1 := by
                have hw := alpha_ge_one_int' G
                try push_cast at hw
                linarith [hw]
              have s46 : -(G.chromaticNumber.toNat : ℤ) ≥ -2 := by have hcc := hc1; omega
              have s47 : (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 2 := by
                have hmul : (0 : ℤ) ≤ ((G.indepNum : ℤ) - 1) * (2 - (G.chromaticNumber.toNat : ℤ)) :=
                  mul_nonneg (by linarith [s45]) (by linarith [s46])
                ring_nf at hmul ⊢
                linarith [hmul]
              have s48 : -2 * (G.minDegree : ℤ) + 3 * (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) ≥ 5 := by linarith [s40, s41, s42, s43, s44, s47]
              linarith [s48]
          linarith [s33]
      linarith [s8]
  have heq_gallai := gallai_int G
  try push_cast at heq_gallai
  linarith [s1, heq_gallai]
