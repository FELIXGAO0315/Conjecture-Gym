import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C79 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hn1 : (Fintype.card V : ℤ) ≤ 3) (hn2 : (G.edgeFinset.card : ℤ) - (G.cliqueNum : ℤ) ≥ 0) :
    -(Fintype.card V : ℤ) + 2 * (G.cliqueNum : ℤ) - (G.indepNum : ℤ) ≤ 2 := by
  have s1 : (Fintype.card V : ℤ) - 2 * (G.cliqueNum : ℤ) + (G.indepNum : ℤ) ≥ -2 := by
    by_cases hc1 : (3 : ℤ) ≤ (G.chromaticNumber.toNat : ℤ)
    · -- 1*chi >= 3
      have s2 : (Fintype.card V : ℤ) - (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
        have hw := chi_le_n_int G
        linarith [hw]
      have s3 : (G.chromaticNumber.toNat : ℤ) ≥ 3 := by have hcc := hc1; omega
      have s4 : (Fintype.card V : ℤ) ≥ 3 := by linarith [s2, s3]
      have s5 : (G.chromaticNumber.toNat : ℤ) - (G.cliqueNum : ℤ) ≥ 0 := by
        have hw := omega_le_chi_int G
        linarith [hw]
      have s6 : -(Fintype.card V : ℤ) ≥ -3 := by linarith [hn1]
      have s7 : -(G.cliqueNum : ℤ) ≥ -3 := by linarith [s5, s2, s6]
      have s8 : (Fintype.card V : ℤ) - (G.vertexCoverNum.toNat : ℤ) ≥ 1 := by
        have hw := tau_le_card_sub_one_int G (by omega)
        linarith [hw]
      have s9 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
        have hw := gallai_int G
        linarith [hw]
      have s10 : (Fintype.card V : ℤ) - 2 * (G.cliqueNum : ℤ) + (G.indepNum : ℤ) ≥ -2 := by linarith [s4, s7, s8, s9]
      linarith [s10]
    · -- 1*chi <= 2
      have s11 : (G.chromaticNumber.toNat : ℤ) - (G.cliqueNum : ℤ) ≥ 0 := by
        have hw := omega_le_chi_int G
        linarith [hw]
      have s12 : (Fintype.card V : ℤ) - (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
        have hw := chi_le_n_int G
        linarith [hw]
      have s13 : (G.indepNum : ℤ) ≥ 0 := by positivity
      have s14 : -(G.chromaticNumber.toNat : ℤ) ≥ -2 := by have hcc := hc1; omega
      have s15 : (Fintype.card V : ℤ) - 2 * (G.cliqueNum : ℤ) + (G.indepNum : ℤ) ≥ -2 := by linarith [s11, s12, s13, s14]
      linarith [s15]
  linarith [s1]
