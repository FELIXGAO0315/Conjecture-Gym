import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C184 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hn1 : (G.vertexCoverNum.toNat : ℤ) ≥ 4) (hn2 : (G.minDegree : ℤ) ≥ 4) :
    (G.chromaticNumber.toNat : ℤ) ≥ -3 * (G.edgeFinset.card : ℤ) + 3 * (G.indepNum : ℤ) + 32 := by
  have s1 : 3 * (G.edgeFinset.card : ℤ) + (G.chromaticNumber.toNat : ℤ) - 3 * (G.indepNum : ℤ) ≥ 32 := by
    by_cases hc1 : (11 : ℤ) ≤ (G.edgeFinset.card : ℤ)
    · -- 1*m >= 11
      have s2 : 3 * (G.edgeFinset.card : ℤ) + (G.chromaticNumber.toNat : ℤ) - 3 * (G.indepNum : ℤ) ≥ 32 := by
        by_cases hc2 : (3 : ℤ) ≤ (G.chromaticNumber.toNat : ℤ)
        · -- 1*chi >= 3
          have s3 : (G.chromaticNumber.toNat : ℤ) ≥ 3 := by have hcc := hc2; omega
          have s4 : (G.edgeFinset.card : ℤ) ≥ 11 := by have hcc := hc1; omega
          have s5 : (G.minDegree : ℤ) ≥ 4 := by linarith [hn2]
          have s6 : (G.vertexCoverNum.toNat : ℤ) ≥ 4 := by linarith [hn1]
          have s7 : 2 * (G.edgeFinset.card : ℤ) - (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
            have hw := handshake_min_int G
            try push_cast at hw
            linarith [hw]
          have s8 : (Fintype.card V : ℤ) ≥ 1 := by
            have hw := card_ge_one_int (V := V)
            try push_cast at hw
            linarith [hw]
          have s9 : -4 * (Fintype.card V : ℤ) - (G.minDegree : ℤ) + (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ -4 := by
            have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 1) * ((G.minDegree : ℤ) - 4) :=
              mul_nonneg (by linarith [s8]) (by linarith [s5])
            ring_nf at hmul ⊢
            linarith [hmul]
          have s10 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
            have hw := gallai_int G
            try push_cast at hw
            linarith [hw]
          have s11 : 6 * (G.edgeFinset.card : ℤ) + 2 * (G.chromaticNumber.toNat : ℤ) - 6 * (G.indepNum : ℤ) ≥ 63 := by linarith [s3, s4, s5, s6, s7, s9, s10]
          have s12 : 3 * (G.edgeFinset.card : ℤ) + (G.chromaticNumber.toNat : ℤ) - 3 * (G.indepNum : ℤ) ≥ 32 := by have hr := s11; omega
          linarith [s12]
        · -- 1*chi <= 2
          have s13 : (G.minDegree : ℤ) ≥ 4 := by linarith [hn2]
          have s14 : (G.vertexCoverNum.toNat : ℤ) ≥ 4 := by linarith [hn1]
          have s15 : 2 * (G.edgeFinset.card : ℤ) - (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
            have hw := handshake_min_int G
            try push_cast at hw
            linarith [hw]
          have s16 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
            have hw := card_le_alpha_chi_int G
            try push_cast at hw
            linarith [hw]
          have s17 : -(G.chromaticNumber.toNat : ℤ) ≥ -2 := by have hcc := hc2; omega
          have s18 : (G.indepNum : ℤ) ≥ 1 := by
            have hw := alpha_ge_one_int' G
            try push_cast at hw
            linarith [hw]
          have s19 : (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 2 := by
            have hmul : (0 : ℤ) ≤ ((G.indepNum : ℤ) - 1) * (2 - (G.chromaticNumber.toNat : ℤ)) :=
              mul_nonneg (by linarith [s18]) (by linarith [s17])
            ring_nf at hmul ⊢
            linarith [hmul]
          have s20 : (Fintype.card V : ℤ) ≥ 1 := by
            have hw := card_ge_one_int (V := V)
            try push_cast at hw
            linarith [hw]
          have s21 : -4 * (Fintype.card V : ℤ) - (G.minDegree : ℤ) + (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ -4 := by
            have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 1) * ((G.minDegree : ℤ) - 4) :=
              mul_nonneg (by linarith [s20]) (by linarith [s13])
            ring_nf at hmul ⊢
            linarith [hmul]
          have s22 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
            have hw := gallai_int G
            try push_cast at hw
            linarith [hw]
          have s23 : 3 * (G.edgeFinset.card : ℤ) + (G.chromaticNumber.toNat : ℤ) - 3 * (G.indepNum : ℤ) ≥ 38 := by linarith [s13, s14, s15, s16, s17, s19, s21, s22]
          linarith [s23]
      linarith [s2]
    · -- 1*m <= 10
      have s24 : (G.maxDegree : ℤ) - (G.minDegree : ℤ) ≥ 0 := by
        have hw := min_le_max_int G
        try push_cast at hw
        linarith [hw]
      have s25 : (Fintype.card V : ℤ) - (G.maxDegree : ℤ) ≥ 1 := by
        have hw := max_lt_card_int' G
        try push_cast at hw
        linarith [hw]
      have s26 : (G.minDegree : ℤ) ≥ 4 := by linarith [hn2]
      have s27 : (Fintype.card V : ℤ) ≥ 5 := by linarith [s24, s25, s26]
      have s28 : (G.indepNum : ℤ) ≥ 1 := by
        have hw := alpha_ge_one_int' G
        try push_cast at hw
        linarith [hw]
      have s29 : (G.vertexCoverNum.toNat : ℤ) ≥ 4 := by linarith [hn1]
      have s30 : 2 * (G.edgeFinset.card : ℤ) - (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
        have hw := handshake_min_int G
        try push_cast at hw
        linarith [hw]
      have s31 : (Fintype.card V : ℤ) ≥ 1 := by
        have hw := card_ge_one_int (V := V)
        try push_cast at hw
        linarith [hw]
      have s32 : -4 * (Fintype.card V : ℤ) - (G.minDegree : ℤ) + (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ -4 := by
        have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 1) * ((G.minDegree : ℤ) - 4) :=
          mul_nonneg (by linarith [s31]) (by linarith [s26])
        ring_nf at hmul ⊢
        linarith [hmul]
      have s33 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
        have hw := gallai_int G
        try push_cast at hw
        linarith [hw]
      have s34 : (G.edgeFinset.card : ℤ) ≥ 10 := by linarith [s28, s26, s29, s30, s32, s33]
      have s35 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
        have hw := card_le_alpha_chi_int G
        try push_cast at hw
        linarith [hw]
      have s36 : -(G.edgeFinset.card : ℤ) ≥ -10 := by have hcc := hc1; omega
      have s37 : -(G.indepNum : ℤ) ≥ -1 := by linarith [s26, s29, s30, s36, s32, s33]
      have s38 : (G.chromaticNumber.toNat : ℤ) ≥ 1 := by
        have hw := chi_ge_one_int' G
        try push_cast at hw
        linarith [hw]
      have s39 : (G.chromaticNumber.toNat : ℤ) + (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 1 := by
        have hmul : (0 : ℤ) ≤ (1 - (G.indepNum : ℤ)) * ((G.chromaticNumber.toNat : ℤ) - 1) :=
          mul_nonneg (by linarith [s37]) (by linarith [s38])
        ring_nf at hmul ⊢
        linarith [hmul]
      have s40 : 3 * (G.edgeFinset.card : ℤ) + (G.chromaticNumber.toNat : ℤ) - 3 * (G.indepNum : ℤ) ≥ 32 := by linarith [s27, s34, s35, s37, s39]
      linarith [s40]
  have heq_gallai := gallai_int G
  try push_cast at heq_gallai
  linarith [s1, heq_gallai]
