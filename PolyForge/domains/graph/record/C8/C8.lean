import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C8 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hn1 : (Fintype.card V : ℤ) ≤ 5) :
    (G.cliqueNum : ℤ) - (G.indepNum : ℤ) ≤ 4 := by
  have s1 : -(G.cliqueNum : ℤ) + (G.indepNum : ℤ) ≥ -4 := by
    by_cases hc1 : (3 : ℤ) ≤ (G.chromaticNumber.toNat : ℤ)
    · -- 1*chi >= 3
      have s2 : (G.chromaticNumber.toNat : ℤ) - (G.cliqueNum : ℤ) ≥ 0 := by
        have hw := omega_le_chi_int G
        linarith [hw]
      have s3 : (Fintype.card V : ℤ) - (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
        have hw := chi_le_n_int G
        linarith [hw]
      have s4 : -(Fintype.card V : ℤ) ≥ -5 := by linarith [hn1]
      have s5 : -(G.chromaticNumber.toNat : ℤ) ≥ -5 := by linarith [s3, s4]
      have s6 : (G.chromaticNumber.toNat : ℤ) ≥ 3 := by have hcc := hc1; omega
      have s7 : (Fintype.card V : ℤ) ≥ 3 := by linarith [s3, s6]
      have s8 : (Fintype.card V : ℤ) - (G.vertexCoverNum.toNat : ℤ) ≥ 1 := by
        have hw := tau_le_card_sub_one_int G (by omega)
        linarith [hw]
      have s9 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
        have hw := gallai_int G
        linarith [hw]
      have s10 : -2 * (G.cliqueNum : ℤ) + 2 * (G.indepNum : ℤ) ≥ -8 := by linarith [s2, s5, s8, s9]
      linarith [s10]
    · -- 1*chi <= 2
      have s11 : (G.chromaticNumber.toNat : ℤ) - (G.cliqueNum : ℤ) ≥ 0 := by
        have hw := omega_le_chi_int G
        linarith [hw]
      have s12 : (G.indepNum : ℤ) ≥ 0 := by positivity
      have s13 : -(G.chromaticNumber.toNat : ℤ) ≥ -2 := by have hcc := hc1; omega
      have s14 : -2 * (G.cliqueNum : ℤ) + 2 * (G.indepNum : ℤ) ≥ -4 := by linarith [s11, s12, s13]
      linarith [s14]
  linarith [s1]
