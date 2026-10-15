import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C234 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hp1 : G.IsBipartite) (hn1 : (G.edgeFinset.card : ℤ) ≤ 6) :
    (G.chromaticNumber.toNat : ℤ) ≤ -3 * (G.minDegree : ℤ) + 3 * (G.indepNum : ℤ) + 2 := by
  have s1 : -3 * (G.minDegree : ℤ) - (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) ≥ -2 := by
    by_cases hc1 : (7 : ℤ) ≤ (Fintype.card V : ℤ)
    · -- 1*n >= 7
      have s2 : (Fintype.card V : ℤ) ≥ 7 := by have hcc := hc1; omega
      have s3 : -(G.chromaticNumber.toNat : ℤ) ≥ -2 := by
        have hw := bipartite_chi_int G hp1
        try push_cast at hw
        linarith [hw]
      have s4 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
        have hw := card_le_alpha_chi_int G
        try push_cast at hw
        linarith [hw]
      have s5 : (G.indepNum : ℤ) ≥ 1 := by
        have hw := alpha_ge_one_int' G
        try push_cast at hw
        linarith [hw]
      have s6 : (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 2 := by
        have hmul : (0 : ℤ) ≤ ((G.indepNum : ℤ) - 1) * (2 - (G.chromaticNumber.toNat : ℤ)) :=
          mul_nonneg (by linarith [s5]) (by linarith [s3])
        ring_nf at hmul ⊢
        linarith [hmul]
      have s7 : 2 * (G.indepNum : ℤ) ≥ 7 := by linarith [s2, s3, s4, s6]
      have s8 : (G.indepNum : ℤ) ≥ 4 := by have hr := s7; omega
      have s9 : 2 * (G.edgeFinset.card : ℤ) - (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
        have hw := handshake_min_int G
        try push_cast at hw
        linarith [hw]
      have s10 : -(G.edgeFinset.card : ℤ) ≥ -6 := by linarith [hn1]
      have s11 : (G.minDegree : ℤ) ≥ 0 := by positivity
      have s12 : -7 * (G.minDegree : ℤ) + (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
        have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 7) * ((G.minDegree : ℤ) - 0) :=
          mul_nonneg (by linarith [s2]) (by linarith [s11])
        ring_nf at hmul ⊢
        linarith [hmul]
      have s13 : -7 * (G.minDegree : ℤ) ≥ -12 := by linarith [s9, s10, s12]
      have s14 : -(G.minDegree : ℤ) ≥ -1 := by have hr := s13; omega
      have s15 : -3 * (G.minDegree : ℤ) - (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) ≥ 7 := by linarith [s8, s3, s14]
      linarith [s15]
    · -- 1*n <= 6
      have s16 : -3 * (G.minDegree : ℤ) - (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) ≥ -2 := by
        by_cases hc16 : (3 : ℤ) ≤ (Fintype.card V : ℤ)
        · -- 1*n >= 3
          have s17 : (Fintype.card V : ℤ) ≥ 3 := by have hcc := hc16; omega
          have s18 : -(G.chromaticNumber.toNat : ℤ) ≥ -2 := by
            have hw := bipartite_chi_int G hp1
            try push_cast at hw
            linarith [hw]
          have s19 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
            have hw := card_le_alpha_chi_int G
            try push_cast at hw
            linarith [hw]
          have s20 : (G.indepNum : ℤ) ≥ 1 := by
            have hw := alpha_ge_one_int' G
            try push_cast at hw
            linarith [hw]
          have s21 : (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 2 := by
            have hmul : (0 : ℤ) ≤ ((G.indepNum : ℤ) - 1) * (2 - (G.chromaticNumber.toNat : ℤ)) :=
              mul_nonneg (by linarith [s20]) (by linarith [s18])
            ring_nf at hmul ⊢
            linarith [hmul]
          have s22 : 2 * (G.indepNum : ℤ) ≥ 3 := by linarith [s17, s18, s19, s21]
          have s23 : (G.indepNum : ℤ) ≥ 2 := by have hr := s22; omega
          have s24 : 2 * (G.edgeFinset.card : ℤ) - (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
            have hw := handshake_min_int G
            try push_cast at hw
            linarith [hw]
          have s25 : -4 * (G.edgeFinset.card : ℤ) + (Fintype.card V : ℤ) * (Fintype.card V : ℤ) ≥ 0 := by
            have hw := bipartite_four_mul_edges_int G hp1
            try push_cast at hw
            linarith [hw]
          have s26 : -(G.edgeFinset.card : ℤ) ≥ -6 := by linarith [hn1]
          have s27 : -(Fintype.card V : ℤ) ≥ -6 := by have hcc := hc16; omega
          have s28 : 9 * (Fintype.card V : ℤ) - (Fintype.card V : ℤ) * (Fintype.card V : ℤ) ≥ 18 := by
            have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 3) * (6 - (Fintype.card V : ℤ)) :=
              mul_nonneg (by linarith [s17]) (by linarith [s27])
            ring_nf at hmul ⊢
            linarith [hmul]
          have s29 : (G.minDegree : ℤ) ≥ 0 := by positivity
          have s30 : -3 * (G.minDegree : ℤ) + (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
            have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 3) * ((G.minDegree : ℤ) - 0) :=
              mul_nonneg (by linarith [s17]) (by linarith [s29])
            ring_nf at hmul ⊢
            linarith [hmul]
          have s31 : -(G.minDegree : ℤ) ≥ -4 := by linarith [s24, s26, s30]
          have s32 : -4 * (Fintype.card V : ℤ) - 6 * (G.minDegree : ℤ) + (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ -24 := by
            have hmul : (0 : ℤ) ≤ (6 - (Fintype.card V : ℤ)) * (4 - (G.minDegree : ℤ)) :=
              mul_nonneg (by linarith [s27]) (by linarith [s31])
            ring_nf at hmul ⊢
            linarith [hmul]
          have s33 : -9 * (G.minDegree : ℤ) ≥ -26 := by linarith [s24, s25, s26, s28, s32]
          have s34 : -(G.minDegree : ℤ) ≥ -2 := by have hr := s33; omega
          have s35 : -3 * (G.minDegree : ℤ) - (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) ≥ -2 := by linarith [s23, s18, s34]
          linarith [s35]
        · -- 1*n <= 2
          have s36 : (G.maxDegree : ℤ) - (G.minDegree : ℤ) ≥ 0 := by
            have hw := min_le_max_int G
            try push_cast at hw
            linarith [hw]
          have s37 : (G.edgeFinset.card : ℤ) - (G.maxDegree : ℤ) ≥ 0 := by
            have hw := max_le_edges_int G
            try push_cast at hw
            linarith [hw]
          have s38 : (G.indepNum : ℤ) ≥ 1 := by
            have hw := alpha_ge_one_int' G
            try push_cast at hw
            linarith [hw]
          have s39 : -(G.chromaticNumber.toNat : ℤ) ≥ -2 := by
            have hw := bipartite_chi_int G hp1
            try push_cast at hw
            linarith [hw]
          have s40 : -4 * (G.edgeFinset.card : ℤ) + (Fintype.card V : ℤ) * (Fintype.card V : ℤ) ≥ 0 := by
            have hw := bipartite_four_mul_edges_int G hp1
            try push_cast at hw
            linarith [hw]
          have s41 : -(Fintype.card V : ℤ) ≥ -2 := by have hcc := hc16; omega
          have s42 : (Fintype.card V : ℤ) ≥ 1 := by
            have hw := card_ge_one_int (V := V)
            try push_cast at hw
            linarith [hw]
          have s43 : 3 * (Fintype.card V : ℤ) - (Fintype.card V : ℤ) * (Fintype.card V : ℤ) ≥ 2 := by
            have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 1) * (2 - (Fintype.card V : ℤ)) :=
              mul_nonneg (by linarith [s42]) (by linarith [s41])
            ring_nf at hmul ⊢
            linarith [hmul]
          have s44 : -3 * (G.minDegree : ℤ) - (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) ≥ -2 := by linarith [s36, s37, s38, s39, s40, s41, s43]
          linarith [s44]
      linarith [s16]
  have heq_gallai := gallai_int G
  try push_cast at heq_gallai
  linarith [s1, heq_gallai]
