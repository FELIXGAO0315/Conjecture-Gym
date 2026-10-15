import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C167 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hn1 : (G.vertexCoverNum.toNat : ℤ) ≥ 2) (hn2 : (G.chromaticNumber.toNat : ℤ) ≤ 5) :
    (G.chromaticNumber.toNat : ℤ) ≤ 2 * (G.edgeFinset.card : ℤ) - 3 * (G.minDegree : ℤ) + 3 := by
  have s1 : 2 * (G.edgeFinset.card : ℤ) - 3 * (G.minDegree : ℤ) - (G.chromaticNumber.toNat : ℤ) ≥ -3 := by
    by_cases hc1 : (4 : ℤ) ≤ (Fintype.card V : ℤ)
    · -- 1*n >= 4
      have s2 : 2 * (G.edgeFinset.card : ℤ) - 3 * (G.minDegree : ℤ) - (G.chromaticNumber.toNat : ℤ) ≥ -3 := by
        by_cases hc2 : (3 : ℤ) ≤ (G.edgeFinset.card : ℤ)
        · -- 1*m >= 3
          have s3 : (G.edgeFinset.card : ℤ) ≥ 3 := by have hcc := hc2; omega
          have s4 : 2 * (G.edgeFinset.card : ℤ) - (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
            have hw := handshake_min_int G
            try push_cast at hw
            linarith [hw]
          have s5 : -(G.chromaticNumber.toNat : ℤ) ≥ -5 := by linarith [hn2]
          have s6 : (G.minDegree : ℤ) ≥ 0 := by positivity
          have s7 : (Fintype.card V : ℤ) ≥ 4 := by have hcc := hc1; omega
          have s8 : -4 * (G.minDegree : ℤ) + (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
            have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 4) * ((G.minDegree : ℤ) - 0) :=
              mul_nonneg (by linarith [s7]) (by linarith [s6])
            ring_nf at hmul ⊢
            linarith [hmul]
          have s9 : 4 * (G.edgeFinset.card : ℤ) - 6 * (G.minDegree : ℤ) - 2 * (G.chromaticNumber.toNat : ℤ) ≥ -7 := by linarith [s3, s4, s5, s8]
          have s10 : 2 * (G.edgeFinset.card : ℤ) - 3 * (G.minDegree : ℤ) - (G.chromaticNumber.toNat : ℤ) ≥ -3 := by have hr := s9; omega
          linarith [s10]
        · -- 1*m <= 2
          have s11 : 2 * (G.edgeFinset.card : ℤ) - 3 * (G.minDegree : ℤ) - (G.chromaticNumber.toNat : ℤ) ≥ -3 := by
            by_cases hc11 : (5 : ℤ) ≤ (Fintype.card V : ℤ)
            · -- 1*n >= 5
              have s12 : (G.edgeFinset.card : ℤ) - (G.vertexCoverNum.toNat : ℤ) ≥ 0 := by
                have hw := tau_le_edges_int G
                try push_cast at hw
                linarith [hw]
              have s13 : (G.vertexCoverNum.toNat : ℤ) ≥ 2 := by linarith [hn1]
              have s14 : (G.edgeFinset.card : ℤ) ≥ 2 := by linarith [s12, s13]
              have s15 : -(G.chromaticNumber.toNat : ℤ) ≥ -5 := by linarith [hn2]
              have s16 : 2 * (G.edgeFinset.card : ℤ) - (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
                have hw := handshake_min_int G
                try push_cast at hw
                linarith [hw]
              have s17 : -(G.edgeFinset.card : ℤ) ≥ -2 := by have hcc := hc2; omega
              have s18 : (G.minDegree : ℤ) ≥ 0 := by positivity
              have s19 : (Fintype.card V : ℤ) ≥ 5 := by have hcc := hc11; omega
              have s20 : -5 * (G.minDegree : ℤ) + (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
                have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 5) * ((G.minDegree : ℤ) - 0) :=
                  mul_nonneg (by linarith [s19]) (by linarith [s18])
                ring_nf at hmul ⊢
                linarith [hmul]
              have s21 : -5 * (G.minDegree : ℤ) ≥ -4 := by linarith [s16, s17, s20]
              have s22 : -(G.minDegree : ℤ) ≥ 0 := by have hr := s21; omega
              have s23 : 2 * (G.edgeFinset.card : ℤ) - 3 * (G.minDegree : ℤ) - (G.chromaticNumber.toNat : ℤ) ≥ -1 := by linarith [s14, s15, s22]
              linarith [s23]
            · -- 1*n <= 4
              have s24 : (Fintype.card V : ℤ) - (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
                have hw := chi_le_n_int G
                try push_cast at hw
                linarith [hw]
              have s25 : (G.edgeFinset.card : ℤ) - (G.vertexCoverNum.toNat : ℤ) ≥ 0 := by
                have hw := tau_le_edges_int G
                try push_cast at hw
                linarith [hw]
              have s26 : (G.vertexCoverNum.toNat : ℤ) ≥ 2 := by linarith [hn1]
              have s27 : 2 * (G.edgeFinset.card : ℤ) - (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
                have hw := handshake_min_int G
                try push_cast at hw
                linarith [hw]
              have s28 : -(Fintype.card V : ℤ) ≥ -4 := by have hcc := hc11; omega
              have s29 : (G.minDegree : ℤ) ≥ 0 := by positivity
              have s30 : (Fintype.card V : ℤ) ≥ 4 := by have hcc := hc11; omega
              have s31 : -4 * (G.minDegree : ℤ) + (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
                have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 4) * ((G.minDegree : ℤ) - 0) :=
                  mul_nonneg (by linarith [s30]) (by linarith [s29])
                ring_nf at hmul ⊢
                linarith [hmul]
              have s32 : 2 * (G.edgeFinset.card : ℤ) - 3 * (G.minDegree : ℤ) - (G.chromaticNumber.toNat : ℤ) ≥ -3 := by linarith [s24, s25, s26, s27, s28, s31]
              linarith [s32]
          linarith [s11]
      linarith [s2]
    · -- 1*n <= 3
      have s33 : 2 * (G.edgeFinset.card : ℤ) - (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
        have hw := handshake_min_int G
        try push_cast at hw
        linarith [hw]
      have s34 : (Fintype.card V : ℤ) - (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
        have hw := chi_le_n_int G
        try push_cast at hw
        linarith [hw]
      have s35 : -(Fintype.card V : ℤ) ≥ -3 := by have hcc := hc1; omega
      have s36 : -(G.chromaticNumber.toNat : ℤ) ≥ -3 := by linarith [s34, s35]
      have s37 : (G.minDegree : ℤ) ≥ 0 := by positivity
      have s38 : (G.indepNum : ℤ) ≥ 1 := by
        have hw := alpha_ge_one_int' G
        try push_cast at hw
        linarith [hw]
      have s39 : (G.vertexCoverNum.toNat : ℤ) ≥ 2 := by linarith [hn1]
      have s40 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
        have hw := gallai_int G
        try push_cast at hw
        linarith [hw]
      have s41 : (Fintype.card V : ℤ) ≥ 3 := by linarith [s38, s39, s40]
      have s42 : -3 * (G.minDegree : ℤ) + (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
        have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 3) * ((G.minDegree : ℤ) - 0) :=
          mul_nonneg (by linarith [s41]) (by linarith [s37])
        ring_nf at hmul ⊢
        linarith [hmul]
      have s43 : 2 * (G.edgeFinset.card : ℤ) - 3 * (G.minDegree : ℤ) - (G.chromaticNumber.toNat : ℤ) ≥ -3 := by linarith [s33, s36, s42]
      linarith [s43]
  have heq_gallai := gallai_int G
  try push_cast at heq_gallai
  linarith [s1, heq_gallai]
