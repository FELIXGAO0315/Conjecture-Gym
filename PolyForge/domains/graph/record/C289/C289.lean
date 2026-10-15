import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C289 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hp1 : G.Connected) (hn1 : (Fintype.card V : ℤ) ≥ 3) :
    (G.chromaticNumber.toNat : ℤ) ≤ 3 * (G.edgeFinset.card : ℤ) - 3 * (G.minDegree : ℤ) := by
  have s1 : 3 * (G.edgeFinset.card : ℤ) - 3 * (G.minDegree : ℤ) - (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
    by_cases hc1 : (3 : ℤ) ≤ (G.chromaticNumber.toNat : ℤ)
    · -- 1*chi >= 3
      have s2 : 3 * (G.edgeFinset.card : ℤ) - 3 * (G.minDegree : ℤ) - (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
        by_cases hc2 : (3 : ℤ) ≤ (G.cliqueNum : ℤ)
        · -- 1*omega >= 3
          have s3 : 3 * (G.edgeFinset.card : ℤ) - 3 * (G.minDegree : ℤ) - (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
            by_cases hc3 : (2 : ℤ) ≤ (G.minDegree : ℤ)
            · -- 1*min_deg >= 2
              have s4 : (Fintype.card V : ℤ) - (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
                have hw := chi_le_n_int G
                try push_cast at hw
                linarith [hw]
              have s5 : (Fintype.card V : ℤ) - (G.maxDegree : ℤ) ≥ 1 := by
                have hw := max_lt_card_int' G
                try push_cast at hw
                linarith [hw]
              have s6 : (G.cliqueNum : ℤ) ≥ 3 := by have hcc := hc2; omega
              have s7 : (G.maxDegree : ℤ) - (G.cliqueNum : ℤ) ≥ -1 := by
                have hw := omega_le_maxdeg_add_one_int G
                try push_cast at hw
                linarith [hw]
              have s8 : (G.minDegree : ℤ) ≥ 2 := by have hcc := hc3; omega
              have s9 : 2 * (G.edgeFinset.card : ℤ) - (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
                have hw := handshake_min_int G
                try push_cast at hw
                linarith [hw]
              have s10 : (Fintype.card V : ℤ) ≥ 3 := by linarith [hn1]
              have s11 : -2 * (Fintype.card V : ℤ) - 3 * (G.minDegree : ℤ) + (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ -6 := by
                have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 3) * ((G.minDegree : ℤ) - 2) :=
                  mul_nonneg (by linarith [s10]) (by linarith [s8])
                ring_nf at hmul ⊢
                linarith [hmul]
              have s12 : 3 * (G.edgeFinset.card : ℤ) - 3 * (G.minDegree : ℤ) - (G.chromaticNumber.toNat : ℤ) ≥ 0 := by linarith [s4, s5, s6, s7, s8, s9, s11]
              linarith [s12]
            · -- 1*min_deg <= 1
              have s13 : (Fintype.card V : ℤ) - (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
                have hw := chi_le_n_int G
                try push_cast at hw
                linarith [hw]
              have s14 : (G.edgeFinset.card : ℤ) - (G.maxDegree : ℤ) ≥ 0 := by
                have hw := max_le_edges_int G
                try push_cast at hw
                linarith [hw]
              have s15 : (G.cliqueNum : ℤ) ≥ 3 := by have hcc := hc2; omega
              have s16 : -(Fintype.card V : ℤ) + (G.edgeFinset.card : ℤ) ≥ -1 := by
                have hw := connected_edges_int G hp1
                try push_cast at hw
                linarith [hw]
              have s17 : (G.maxDegree : ℤ) - (G.cliqueNum : ℤ) ≥ -1 := by
                have hw := omega_le_maxdeg_add_one_int G
                try push_cast at hw
                linarith [hw]
              have s18 : -(G.minDegree : ℤ) ≥ -1 := by have hcc := hc3; omega
              have s19 : 3 * (G.edgeFinset.card : ℤ) - 3 * (G.minDegree : ℤ) - (G.chromaticNumber.toNat : ℤ) ≥ 0 := by linarith [s13, s14, s15, s16, s17, s18]
              linarith [s19]
          linarith [s3]
        · -- 1*omega <= 2
          have s20 : 3 * (G.edgeFinset.card : ℤ) - 3 * (G.minDegree : ℤ) - (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
            by_cases hc20 : (2 : ℤ) ≤ (G.minDegree : ℤ)
            · -- 1*min_deg >= 2
              have s21 : (Fintype.card V : ℤ) - (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
                have hw := chi_le_n_int G
                try push_cast at hw
                linarith [hw]
              have s22 : (G.maxDegree : ℤ) - (G.minDegree : ℤ) ≥ 0 := by
                have hw := min_le_max_int G
                try push_cast at hw
                linarith [hw]
              have s23 : (Fintype.card V : ℤ) - (G.maxDegree : ℤ) ≥ 1 := by
                have hw := max_lt_card_int' G
                try push_cast at hw
                linarith [hw]
              have s24 : (G.minDegree : ℤ) ≥ 2 := by have hcc := hc20; omega
              have s25 : 2 * (G.edgeFinset.card : ℤ) - (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
                have hw := handshake_min_int G
                try push_cast at hw
                linarith [hw]
              have s26 : (Fintype.card V : ℤ) ≥ 3 := by linarith [hn1]
              have s27 : -2 * (Fintype.card V : ℤ) - 3 * (G.minDegree : ℤ) + (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ -6 := by
                have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 3) * ((G.minDegree : ℤ) - 2) :=
                  mul_nonneg (by linarith [s26]) (by linarith [s24])
                ring_nf at hmul ⊢
                linarith [hmul]
              have s28 : 3 * (G.edgeFinset.card : ℤ) - 3 * (G.minDegree : ℤ) - (G.chromaticNumber.toNat : ℤ) ≥ 0 := by linarith [s21, s22, s23, s24, s25, s27]
              linarith [s28]
            · -- 1*min_deg <= 1
              have s29 : (Fintype.card V : ℤ) - (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
                have hw := chi_le_n_int G
                try push_cast at hw
                linarith [hw]
              have s30 : -(Fintype.card V : ℤ) + (G.edgeFinset.card : ℤ) ≥ -1 := by
                have hw := connected_edges_int G hp1
                try push_cast at hw
                linarith [hw]
              have s31 : (Fintype.card V : ℤ) ≥ 3 := by linarith [hn1]
              have s32 : -(G.minDegree : ℤ) ≥ -1 := by have hcc := hc20; omega
              have s33 : 3 * (G.edgeFinset.card : ℤ) - 3 * (G.minDegree : ℤ) - (G.chromaticNumber.toNat : ℤ) ≥ 0 := by linarith [s29, s30, s31, s32]
              linarith [s33]
          linarith [s20]
      linarith [s2]
    · -- 1*chi <= 2
      have s34 : 3 * (G.edgeFinset.card : ℤ) - 3 * (G.minDegree : ℤ) - (G.chromaticNumber.toNat : ℤ) ≥ 1 := by
        by_cases hc34 : (3 : ℤ) ≤ (G.indepNum : ℤ)
        · -- 1*alpha >= 3
          have s35 : 3 * (G.edgeFinset.card : ℤ) - 3 * (G.minDegree : ℤ) - (G.chromaticNumber.toNat : ℤ) ≥ 1 := by
            by_cases hc35 : (2 : ℤ) ≤ (G.minDegree : ℤ)
            · -- 1*min_deg >= 2
              have s36 : (G.indepNum : ℤ) ≥ 3 := by have hcc := hc34; omega
              have s37 : (G.minDegree : ℤ) ≥ 2 := by have hcc := hc35; omega
              have s38 : (G.vertexCoverNum.toNat : ℤ) ≥ 0 := by positivity
              have s39 : 2 * (G.edgeFinset.card : ℤ) - (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
                have hw := handshake_min_int G
                try push_cast at hw
                linarith [hw]
              have s40 : -(G.chromaticNumber.toNat : ℤ) ≥ -2 := by have hcc := hc1; omega
              have s41 : (Fintype.card V : ℤ) ≥ 3 := by linarith [hn1]
              have s42 : -2 * (Fintype.card V : ℤ) - 3 * (G.minDegree : ℤ) + (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ -6 := by
                have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 3) * ((G.minDegree : ℤ) - 2) :=
                  mul_nonneg (by linarith [s41]) (by linarith [s37])
                ring_nf at hmul ⊢
                linarith [hmul]
              have s43 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
                have hw := gallai_int G
                try push_cast at hw
                linarith [hw]
              have s44 : 3 * (G.edgeFinset.card : ℤ) - 3 * (G.minDegree : ℤ) - (G.chromaticNumber.toNat : ℤ) ≥ 1 := by linarith [s36, s37, s38, s39, s40, s42, s43]
              linarith [s44]
            · -- 1*min_deg <= 1
              have s45 : (G.indepNum : ℤ) ≥ 3 := by have hcc := hc34; omega
              have s46 : -(Fintype.card V : ℤ) + (G.edgeFinset.card : ℤ) ≥ -1 := by
                have hw := connected_edges_int G hp1
                try push_cast at hw
                linarith [hw]
              have s47 : (G.vertexCoverNum.toNat : ℤ) ≥ 0 := by positivity
              have s48 : -(G.chromaticNumber.toNat : ℤ) ≥ -2 := by have hcc := hc1; omega
              have s49 : -(G.minDegree : ℤ) ≥ -1 := by have hcc := hc35; omega
              have s50 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
                have hw := gallai_int G
                try push_cast at hw
                linarith [hw]
              have s51 : 3 * (G.edgeFinset.card : ℤ) - 3 * (G.minDegree : ℤ) - (G.chromaticNumber.toNat : ℤ) ≥ 1 := by linarith [s45, s46, s47, s48, s49, s50]
              linarith [s51]
          linarith [s35]
        · -- 1*alpha <= 2
          have s52 : 3 * (G.edgeFinset.card : ℤ) - 3 * (G.minDegree : ℤ) - (G.chromaticNumber.toNat : ℤ) ≥ 1 := by
            by_cases hc52 : (2 : ℤ) ≤ (G.minDegree : ℤ)
            · -- 1*min_deg >= 2
              have s53 : (G.minDegree : ℤ) ≥ 2 := by have hcc := hc52; omega
              have s54 : 2 * (G.edgeFinset.card : ℤ) - (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
                have hw := handshake_min_int G
                try push_cast at hw
                linarith [hw]
              have s55 : -(G.chromaticNumber.toNat : ℤ) ≥ -2 := by have hcc := hc1; omega
              have s56 : (Fintype.card V : ℤ) ≥ 3 := by linarith [hn1]
              have s57 : -2 * (Fintype.card V : ℤ) - 3 * (G.minDegree : ℤ) + (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ -6 := by
                have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 3) * ((G.minDegree : ℤ) - 2) :=
                  mul_nonneg (by linarith [s56]) (by linarith [s53])
                ring_nf at hmul ⊢
                linarith [hmul]
              have s58 : (G.chromaticNumber.toNat : ℤ) - (G.cliqueNum : ℤ) ≥ 0 := by
                have hw := omega_le_chi_int G
                try push_cast at hw
                linarith [hw]
              have s59 : -(G.cliqueNum : ℤ) ≥ -2 := by linarith [s58, s55]
              have s60 : -4 * (G.edgeFinset.card : ℤ) + (Fintype.card V : ℤ) * (Fintype.card V : ℤ) ≥ 0 := by
                have hw := turan_r2_int G (by linarith [s59])
                try push_cast at hw
                linarith [hw]
              have s61 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
                have hw := card_le_alpha_chi_int G
                try push_cast at hw
                linarith [hw]
              have s62 : -(G.indepNum : ℤ) ≥ -2 := by have hcc := hc34; omega
              have s63 : (G.chromaticNumber.toNat : ℤ) ≥ 1 := by
                have hw := chi_ge_one_int' G
                try push_cast at hw
                linarith [hw]
              have s64 : 2 * (G.chromaticNumber.toNat : ℤ) + (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 2 := by
                have hmul : (0 : ℤ) ≤ (2 - (G.indepNum : ℤ)) * ((G.chromaticNumber.toNat : ℤ) - 1) :=
                  mul_nonneg (by linarith [s62]) (by linarith [s63])
                ring_nf at hmul ⊢
                linarith [hmul]
              have s65 : -(Fintype.card V : ℤ) ≥ -4 := by linarith [s61, s55, s62, s64]
              have s66 : 7 * (Fintype.card V : ℤ) - (Fintype.card V : ℤ) * (Fintype.card V : ℤ) ≥ 12 := by
                have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 3) * (4 - (Fintype.card V : ℤ)) :=
                  mul_nonneg (by linarith [s56]) (by linarith [s65])
                ring_nf at hmul ⊢
                linarith [hmul]
              have s67 : 3 * (G.edgeFinset.card : ℤ) - 3 * (G.minDegree : ℤ) - (G.chromaticNumber.toNat : ℤ) ≥ 4 := by linarith [s53, s54, s55, s57, s60, s66]
              linarith [s67]
            · -- 1*min_deg <= 1
              have s68 : -(Fintype.card V : ℤ) + (G.edgeFinset.card : ℤ) ≥ -1 := by
                have hw := connected_edges_int G hp1
                try push_cast at hw
                linarith [hw]
              have s69 : (Fintype.card V : ℤ) ≥ 3 := by linarith [hn1]
              have s70 : -(G.chromaticNumber.toNat : ℤ) ≥ -2 := by have hcc := hc1; omega
              have s71 : -(G.minDegree : ℤ) ≥ -1 := by have hcc := hc52; omega
              have s72 : 3 * (G.edgeFinset.card : ℤ) - 3 * (G.minDegree : ℤ) - (G.chromaticNumber.toNat : ℤ) ≥ 1 := by linarith [s68, s69, s70, s71]
              linarith [s72]
          linarith [s52]
      linarith [s34]
  have heq_gallai := gallai_int G
  try push_cast at heq_gallai
  linarith [s1, heq_gallai]
