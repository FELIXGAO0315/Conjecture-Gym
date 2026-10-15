import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C108 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hn1 : (G.chromaticNumber.toNat : ℤ) ≤ (G.maxDegree : ℤ)) (hn2 : (G.maxDegree : ℤ) ≥ 2 * (G.minDegree : ℤ)) :
    2 * (G.indepNum : ℤ) ≥ -2 * (G.edgeFinset.card : ℤ) + 3 * (G.minDegree : ℤ) + 5 := by
  have s1 : 2 * (G.edgeFinset.card : ℤ) - 3 * (G.minDegree : ℤ) + 2 * (G.indepNum : ℤ) ≥ 5 := by
    by_cases hc1 : (3 : ℤ) ≤ (G.chromaticNumber.toNat : ℤ)
    · -- 1*chi >= 3
      have s2 : 2 * (G.edgeFinset.card : ℤ) - 3 * (G.minDegree : ℤ) + 2 * (G.indepNum : ℤ) ≥ 5 := by
        by_cases hc2 : (2 : ℤ) ≤ (G.minDegree : ℤ)
        · -- 1*min_deg >= 2
          have s3 : (Fintype.card V : ℤ) - (G.maxDegree : ℤ) ≥ 1 := by
            have hw := max_lt_card_int' G
            try push_cast at hw
            linarith [hw]
          have s4 : (G.indepNum : ℤ) ≥ 1 := by
            have hw := alpha_ge_one_int' G
            try push_cast at hw
            linarith [hw]
          have s5 : (G.minDegree : ℤ) ≥ 2 := by have hcc := hc2; omega
          have s6 : 2 * (G.edgeFinset.card : ℤ) - (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
            have hw := handshake_min_int G
            try push_cast at hw
            linarith [hw]
          have s7 : (G.maxDegree : ℤ) - 2 * (G.minDegree : ℤ) ≥ 0 := by linarith [hn2]
          have s8 : (Fintype.card V : ℤ) ≥ 1 := by
            have hw := card_ge_one_int (V := V)
            try push_cast at hw
            linarith [hw]
          have s9 : -2 * (Fintype.card V : ℤ) - (G.minDegree : ℤ) + (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ -2 := by
            have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 1) * ((G.minDegree : ℤ) - 2) :=
              mul_nonneg (by linarith [s8]) (by linarith [s5])
            ring_nf at hmul ⊢
            linarith [hmul]
          have s10 : 2 * (G.edgeFinset.card : ℤ) - 3 * (G.minDegree : ℤ) + 2 * (G.indepNum : ℤ) ≥ 6 := by linarith [s3, s4, s5, s6, s7, s9]
          linarith [s10]
        · -- 1*min_deg <= 1
          have s11 : (G.edgeFinset.card : ℤ) - (G.maxDegree : ℤ) ≥ 0 := by
            have hw := max_le_edges_int G
            try push_cast at hw
            linarith [hw]
          have s12 : (G.chromaticNumber.toNat : ℤ) ≥ 3 := by have hcc := hc1; omega
          have s13 : (G.indepNum : ℤ) ≥ 1 := by
            have hw := alpha_ge_one_int' G
            try push_cast at hw
            linarith [hw]
          have s14 : (G.maxDegree : ℤ) - (G.chromaticNumber.toNat : ℤ) ≥ 0 := by linarith [hn1]
          have s15 : -(G.minDegree : ℤ) ≥ -1 := by have hcc := hc2; omega
          have s16 : 2 * (G.edgeFinset.card : ℤ) - 3 * (G.minDegree : ℤ) + 2 * (G.indepNum : ℤ) ≥ 5 := by linarith [s11, s12, s13, s14, s15]
          linarith [s16]
      linarith [s2]
    · -- 1*chi <= 2
      have s17 : (G.edgeFinset.card : ℤ) - (G.maxDegree : ℤ) ≥ 0 := by
        have hw := max_le_edges_int G
        try push_cast at hw
        linarith [hw]
      have s18 : (Fintype.card V : ℤ) - (G.maxDegree : ℤ) ≥ 1 := by
        have hw := max_lt_card_int' G
        try push_cast at hw
        linarith [hw]
      have s19 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
        have hw := card_le_alpha_chi_int G
        try push_cast at hw
        linarith [hw]
      have s20 : (G.maxDegree : ℤ) - (G.chromaticNumber.toNat : ℤ) ≥ 0 := by linarith [hn1]
      have s21 : (G.indepNum : ℤ) ≥ 1 := by
        have hw := alpha_ge_one_int' G
        try push_cast at hw
        linarith [hw]
      have s22 : -(G.chromaticNumber.toNat : ℤ) ≥ -2 := by have hcc := hc1; omega
      have s23 : (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 2 := by
        have hmul : (0 : ℤ) ≤ ((G.indepNum : ℤ) - 1) * (2 - (G.chromaticNumber.toNat : ℤ)) :=
          mul_nonneg (by linarith [s21]) (by linarith [s22])
        ring_nf at hmul ⊢
        linarith [hmul]
      have s24 : 2 * (G.indepNum : ℤ) ≥ 3 := by linarith [s18, s19, s20, s23]
      have s25 : (G.indepNum : ℤ) ≥ 2 := by have hr := s24; omega
      have s26 : (G.chromaticNumber.toNat : ℤ) ≥ 1 := by
        have hw := chi_ge_one_int' G
        try push_cast at hw
        linarith [hw]
      have s27 : (G.edgeFinset.card : ℤ) ≥ 1 := by linarith [s17, s26, s20]
      have s28 : (G.maxDegree : ℤ) - 2 * (G.minDegree : ℤ) ≥ 0 := by linarith [hn2]
      have s29 : 4 * (G.edgeFinset.card : ℤ) - 6 * (G.minDegree : ℤ) + 4 * (G.indepNum : ℤ) ≥ 9 := by linarith [s17, s25, s27, s28]
      have s30 : 2 * (G.edgeFinset.card : ℤ) - 3 * (G.minDegree : ℤ) + 2 * (G.indepNum : ℤ) ≥ 5 := by have hr := s29; omega
      linarith [s30]
  have heq_gallai := gallai_int G
  try push_cast at heq_gallai
  linarith [s1, heq_gallai]
