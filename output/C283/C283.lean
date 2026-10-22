import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C283 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hn1 : (G.maxDegree : ℤ) ≤ (G.chromaticNumber.toNat : ℤ)) (hn2 : (G.chromaticNumber.toNat : ℤ) ≤ 3) :
    (G.edgeFinset.card : ℤ) ≤ (Fintype.card V : ℤ) + 3 * (G.indepNum : ℤ) - 3 := by
  have s1 : (Fintype.card V : ℤ) - (G.edgeFinset.card : ℤ) + 3 * (G.indepNum : ℤ) ≥ 3 := by
    by_cases hc1 : (3 : ℤ) ≤ (G.chromaticNumber.toNat : ℤ)
    · -- 1*chi >= 3
      have s2 : (Fintype.card V : ℤ) - (G.edgeFinset.card : ℤ) + 3 * (G.indepNum : ℤ) ≥ 3 := by
        by_cases hc2 : (2 : ℤ) ≤ (G.indepNum : ℤ)
        · -- 1*alpha >= 2
          have s3 : (G.indepNum : ℤ) ≥ 2 := by have hcc := hc2; omega
          have s4 : -2 * (G.edgeFinset.card : ℤ) + (Fintype.card V : ℤ) * (G.maxDegree : ℤ) ≥ 0 := by
            have hw := handshake_max_int G
            try push_cast at hw
            linarith [hw]
          have s5 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
            have hw := card_le_alpha_chi_int G
            try push_cast at hw
            linarith [hw]
          have s6 : -(G.chromaticNumber.toNat : ℤ) ≥ -3 := by linarith [hn2]
          have s7 : 2 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 6 := by
            have hmul : (0 : ℤ) ≤ ((G.indepNum : ℤ) - 2) * (3 - (G.chromaticNumber.toNat : ℤ)) :=
              mul_nonneg (by linarith [s3]) (by linarith [s6])
            ring_nf at hmul ⊢
            linarith [hmul]
          have s8 : -(G.maxDegree : ℤ) + (G.chromaticNumber.toNat : ℤ) ≥ 0 := by linarith [hn1]
          have s9 : -(G.maxDegree : ℤ) ≥ -3 := by linarith [s8, s6]
          have s10 : (Fintype.card V : ℤ) - (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
            have hw := chi_le_n_int G
            try push_cast at hw
            linarith [hw]
          have s11 : (G.chromaticNumber.toNat : ℤ) ≥ 3 := by have hcc := hc1; omega
          have s12 : (Fintype.card V : ℤ) ≥ 3 := by linarith [s10, s11]
          have s13 : 3 * (Fintype.card V : ℤ) + 3 * (G.maxDegree : ℤ) - (Fintype.card V : ℤ) * (G.maxDegree : ℤ) ≥ 9 := by
            have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 3) * (3 - (G.maxDegree : ℤ)) :=
              mul_nonneg (by linarith [s12]) (by linarith [s9])
            ring_nf at hmul ⊢
            linarith [hmul]
          have s14 : (Fintype.card V : ℤ) - (G.edgeFinset.card : ℤ) + 3 * (G.indepNum : ℤ) ≥ 3 := by linarith [s3, s4, s5, s6, s7, s9, s13]
          linarith [s14]
        · -- 1*alpha <= 1
          have s15 : (G.indepNum : ℤ) ≥ 1 := by
            have hw := alpha_ge_one_int' G
            try push_cast at hw
            linarith [hw]
          have s16 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
            have hw := card_le_alpha_chi_int G
            try push_cast at hw
            linarith [hw]
          have s17 : -(G.chromaticNumber.toNat : ℤ) ≥ -3 := by linarith [hn2]
          have s18 : -(G.indepNum : ℤ) ≥ -1 := by have hcc := hc2; omega
          have s19 : (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 3 := by
            have hmul : (0 : ℤ) ≤ ((G.indepNum : ℤ) - 1) * (3 - (G.chromaticNumber.toNat : ℤ)) :=
              mul_nonneg (by linarith [s15]) (by linarith [s17])
            ring_nf at hmul ⊢
            linarith [hmul]
          have s20 : -(Fintype.card V : ℤ) ≥ -3 := by linarith [s16, s17, s18, s19]
          have s21 : (Fintype.card V : ℤ) - (G.maxDegree : ℤ) ≥ 1 := by
            have hw := max_lt_card_int' G
            try push_cast at hw
            linarith [hw]
          have s22 : (G.maxDegree : ℤ) - (G.cliqueNum : ℤ) ≥ -1 := by
            have hw := omega_le_maxdeg_add_one_int G
            try push_cast at hw
            linarith [hw]
          have s23 : -(G.cliqueNum : ℤ) ≥ -3 := by linarith [s21, s22, s16, s17, s18, s19]
          have s24 : -6 * (G.edgeFinset.card : ℤ) + 2 * (Fintype.card V : ℤ) * (Fintype.card V : ℤ) ≥ 0 := by
            have hw := turan_r3_int G (by linarith [s23])
            try push_cast at hw
            linarith [hw]
          have s25 : (Fintype.card V : ℤ) - (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
            have hw := chi_le_n_int G
            try push_cast at hw
            linarith [hw]
          have s26 : (G.chromaticNumber.toNat : ℤ) ≥ 3 := by have hcc := hc1; omega
          have s27 : (Fintype.card V : ℤ) ≥ 3 := by linarith [s25, s26]
          have s28 : 6 * (Fintype.card V : ℤ) - (Fintype.card V : ℤ) * (Fintype.card V : ℤ) ≥ 9 := by
            have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 3) * (3 - (Fintype.card V : ℤ)) :=
              mul_nonneg (by linarith [s27]) (by linarith [s20])
            ring_nf at hmul ⊢
            linarith [hmul]
          have s29 : (Fintype.card V : ℤ) - (G.edgeFinset.card : ℤ) + 3 * (G.indepNum : ℤ) ≥ 3 := by linarith [s15, s20, s24, s28]
          linarith [s29]
      linarith [s2]
    · -- 1*chi <= 2
      have s30 : (Fintype.card V : ℤ) - (G.maxDegree : ℤ) ≥ 1 := by
        have hw := max_lt_card_int' G
        try push_cast at hw
        linarith [hw]
      have s31 : (G.indepNum : ℤ) ≥ 1 := by
        have hw := alpha_ge_one_int' G
        try push_cast at hw
        linarith [hw]
      have s32 : -2 * (G.edgeFinset.card : ℤ) + (Fintype.card V : ℤ) * (G.maxDegree : ℤ) ≥ 0 := by
        have hw := handshake_max_int G
        try push_cast at hw
        linarith [hw]
      have s33 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
        have hw := card_le_alpha_chi_int G
        try push_cast at hw
        linarith [hw]
      have s34 : -(G.chromaticNumber.toNat : ℤ) ≥ -2 := by have hcc := hc1; omega
      have s35 : (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 2 := by
        have hmul : (0 : ℤ) ≤ ((G.indepNum : ℤ) - 1) * (2 - (G.chromaticNumber.toNat : ℤ)) :=
          mul_nonneg (by linarith [s31]) (by linarith [s34])
        ring_nf at hmul ⊢
        linarith [hmul]
      have s36 : (Fintype.card V : ℤ) ≥ 1 := by
        have hw := card_ge_one_int (V := V)
        try push_cast at hw
        linarith [hw]
      have s37 : -(G.maxDegree : ℤ) + (G.chromaticNumber.toNat : ℤ) ≥ 0 := by linarith [hn1]
      have s38 : -(G.maxDegree : ℤ) ≥ -2 := by linarith [s37, s34]
      have s39 : 2 * (Fintype.card V : ℤ) + (G.maxDegree : ℤ) - (Fintype.card V : ℤ) * (G.maxDegree : ℤ) ≥ 2 := by
        have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 1) * (2 - (G.maxDegree : ℤ)) :=
          mul_nonneg (by linarith [s36]) (by linarith [s38])
        ring_nf at hmul ⊢
        linarith [hmul]
      have s40 : 2 * (Fintype.card V : ℤ) - 2 * (G.edgeFinset.card : ℤ) + 6 * (G.indepNum : ℤ) ≥ 7 := by linarith [s30, s31, s32, s33, s34, s35, s39]
      have s41 : (Fintype.card V : ℤ) - (G.edgeFinset.card : ℤ) + 3 * (G.indepNum : ℤ) ≥ 4 := by have hr := s40; omega
      linarith [s41]
  have heq_gallai := gallai_int G
  try push_cast at heq_gallai
  linarith [s1, heq_gallai]
