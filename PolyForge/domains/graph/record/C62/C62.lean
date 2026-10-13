import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C62 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hn1 : (G.maxDegree : ℤ) ≤ 2) (hn2 : (G.chromaticNumber.toNat : ℤ) ≤ 2) :
    (G.edgeFinset.card : ℤ) ≤ 3 * (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) - 5 := by
  have s1 : -(G.edgeFinset.card : ℤ) + 3 * (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) ≥ 5 := by
    by_cases hc1 : (2 : ℤ) ≤ (G.indepNum : ℤ)
    · -- 1*alpha >= 2
      have s2 : -(G.edgeFinset.card : ℤ) + 3 * (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) ≥ 6 := by
        by_cases hc2 : (3 : ℤ) ≤ (G.indepNum : ℤ)
        · -- 1*alpha >= 3
          have s3 : -2 * (G.edgeFinset.card : ℤ) + (Fintype.card V : ℤ) * (G.maxDegree : ℤ) ≥ 0 := by
            have hw := handshake_max_int G
            try push_cast at hw
            linarith [hw]
          have s4 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
            have hw := card_le_alpha_chi_int G
            try push_cast at hw
            linarith [hw]
          have s5 : -(G.maxDegree : ℤ) ≥ -2 := by linarith [hn1]
          have s6 : -(G.chromaticNumber.toNat : ℤ) ≥ -2 := by linarith [hn2]
          have s7 : (G.indepNum : ℤ) ≥ 3 := by have hcc := hc2; omega
          have s8 : 3 * (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 6 := by
            have hmul : (0 : ℤ) ≤ ((G.indepNum : ℤ) - 3) * (2 - (G.chromaticNumber.toNat : ℤ)) :=
              mul_nonneg (by linarith [s7]) (by linarith [s6])
            ring_nf at hmul ⊢
            linarith [hmul]
          have s9 : (Fintype.card V : ℤ) ≥ 1 := by
            have hw := card_ge_one_int (V := V)
            try push_cast at hw
            linarith [hw]
          have s10 : 2 * (Fintype.card V : ℤ) + (G.maxDegree : ℤ) - (Fintype.card V : ℤ) * (G.maxDegree : ℤ) ≥ 2 := by
            have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 1) * (2 - (G.maxDegree : ℤ)) :=
              mul_nonneg (by linarith [s9]) (by linarith [s5])
            ring_nf at hmul ⊢
            linarith [hmul]
          have s11 : -(G.edgeFinset.card : ℤ) + 3 * (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) ≥ 6 := by linarith [s3, s4, s5, s8, s10]
          linarith [s11]
        · -- 1*alpha <= 2
          have s12 : (Fintype.card V : ℤ) - (G.maxDegree : ℤ) ≥ 1 := by
            have hw := max_lt_card_int' G
            try push_cast at hw
            linarith [hw]
          have s13 : -2 * (G.edgeFinset.card : ℤ) + (Fintype.card V : ℤ) * (G.maxDegree : ℤ) ≥ 0 := by
            have hw := handshake_max_int G
            try push_cast at hw
            linarith [hw]
          have s14 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
            have hw := card_le_alpha_chi_int G
            try push_cast at hw
            linarith [hw]
          have s15 : -(G.indepNum : ℤ) ≥ -2 := by have hcc := hc2; omega
          have s16 : -(G.chromaticNumber.toNat : ℤ) ≥ -2 := by linarith [hn2]
          have s17 : (G.indepNum : ℤ) ≥ 2 := by have hcc := hc2; omega
          have s18 : 2 * (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 4 := by
            have hmul : (0 : ℤ) ≤ ((G.indepNum : ℤ) - 2) * (2 - (G.chromaticNumber.toNat : ℤ)) :=
              mul_nonneg (by linarith [s17]) (by linarith [s16])
            ring_nf at hmul ⊢
            linarith [hmul]
          have s19 : (Fintype.card V : ℤ) ≥ 1 := by
            have hw := card_ge_one_int (V := V)
            try push_cast at hw
            linarith [hw]
          have s20 : -(G.maxDegree : ℤ) ≥ -2 := by linarith [hn1]
          have s21 : 2 * (Fintype.card V : ℤ) + (G.maxDegree : ℤ) - (Fintype.card V : ℤ) * (G.maxDegree : ℤ) ≥ 2 := by
            have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 1) * (2 - (G.maxDegree : ℤ)) :=
              mul_nonneg (by linarith [s19]) (by linarith [s20])
            ring_nf at hmul ⊢
            linarith [hmul]
          have s22 : -2 * (G.edgeFinset.card : ℤ) + 6 * (G.chromaticNumber.toNat : ℤ) + 4 * (G.indepNum : ℤ) ≥ 11 := by linarith [s12, s13, s14, s15, s18, s21]
          have s23 : -(G.edgeFinset.card : ℤ) + 3 * (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) ≥ 6 := by have hr := s22; omega
          linarith [s23]
      linarith [s2]
    · -- 1*alpha <= 1
      have s24 : (Fintype.card V : ℤ) - (G.maxDegree : ℤ) ≥ 1 := by
        have hw := max_lt_card_int' G
        try push_cast at hw
        linarith [hw]
      have s25 : (G.chromaticNumber.toNat : ℤ) ≥ 1 := by
        have hw := chi_ge_one_int' G
        try push_cast at hw
        linarith [hw]
      have s26 : -2 * (G.edgeFinset.card : ℤ) + (Fintype.card V : ℤ) * (G.maxDegree : ℤ) ≥ 0 := by
        have hw := handshake_max_int G
        try push_cast at hw
        linarith [hw]
      have s27 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
        have hw := card_le_alpha_chi_int G
        try push_cast at hw
        linarith [hw]
      have s28 : -(G.indepNum : ℤ) ≥ -1 := by have hcc := hc1; omega
      have s29 : (G.indepNum : ℤ) ≥ 1 := by
        have hw := alpha_ge_one_int' G
        try push_cast at hw
        linarith [hw]
      have s30 : -(G.chromaticNumber.toNat : ℤ) ≥ -2 := by linarith [hn2]
      have s31 : (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 2 := by
        have hmul : (0 : ℤ) ≤ ((G.indepNum : ℤ) - 1) * (2 - (G.chromaticNumber.toNat : ℤ)) :=
          mul_nonneg (by linarith [s29]) (by linarith [s30])
        ring_nf at hmul ⊢
        linarith [hmul]
      have s32 : (Fintype.card V : ℤ) ≥ 1 := by
        have hw := card_ge_one_int (V := V)
        try push_cast at hw
        linarith [hw]
      have s33 : -(G.maxDegree : ℤ) ≥ -2 := by linarith [hn1]
      have s34 : 2 * (Fintype.card V : ℤ) + (G.maxDegree : ℤ) - (Fintype.card V : ℤ) * (G.maxDegree : ℤ) ≥ 2 := by
        have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 1) * (2 - (G.maxDegree : ℤ)) :=
          mul_nonneg (by linarith [s32]) (by linarith [s33])
        ring_nf at hmul ⊢
        linarith [hmul]
      have s35 : -(G.edgeFinset.card : ℤ) + 3 * (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) ≥ 5 := by linarith [s24, s25, s26, s27, s28, s31, s34]
      linarith [s35]
  have heq_gallai := gallai_int G
  try push_cast at heq_gallai
  linarith [s1, heq_gallai]
