import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C42 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hp1 : 2 ≤ Fintype.card V) (hn1 : (G.edgeFinset.card : ℤ) - 2 * (G.cliqueNum : ℤ) ≥ 0) (hn2 : (G.cliqueNum : ℤ) ≤ 6) :
    -(G.chromaticNumber.toNat : ℤ) + 2 * (G.cliqueNum : ℤ) - (G.indepNum : ℤ) ≤ 5 := by
  have s1 : (G.chromaticNumber.toNat : ℤ) - 2 * (G.cliqueNum : ℤ) + (G.indepNum : ℤ) ≥ -5 := by
    by_cases hc1 : (3 : ℤ) ≤ (G.chromaticNumber.toNat : ℤ)
    · -- 1*chi >= 3
      have s2 : (G.chromaticNumber.toNat : ℤ) - (G.cliqueNum : ℤ) ≥ 0 := by
        have hw := omega_le_chi_int G
        linarith [hw]
      have s3 : (Fintype.card V : ℤ) - (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
        have hw := chi_le_n_int G
        linarith [hw]
      have s4 : (G.chromaticNumber.toNat : ℤ) ≥ 3 := by have hcc := hc1; omega
      have s5 : (Fintype.card V : ℤ) ≥ 3 := by linarith [s3, s4]
      have s6 : (G.indepNum : ℤ) ≥ 1 := by
        have hw := alpha_ge_one_int G (by omega)
        linarith [hw]
      have s7 : -(G.cliqueNum : ℤ) ≥ -6 := by linarith [hn2]
      have s8 : (G.chromaticNumber.toNat : ℤ) - 2 * (G.cliqueNum : ℤ) + (G.indepNum : ℤ) ≥ -5 := by linarith [s2, s6, s7]
      linarith [s8]
    · -- 1*chi <= 2
      have s9 : (G.chromaticNumber.toNat : ℤ) - (G.cliqueNum : ℤ) ≥ 0 := by
        have hw := omega_le_chi_int G
        linarith [hw]
      have s10 : (G.indepNum : ℤ) ≥ 0 := by positivity
      have s11 : -(G.chromaticNumber.toNat : ℤ) ≥ -2 := by have hcc := hc1; omega
      have s12 : (G.chromaticNumber.toNat : ℤ) - 2 * (G.cliqueNum : ℤ) + (G.indepNum : ℤ) ≥ -2 := by linarith [s9, s10, s11]
      linarith [s12]
  linarith [s1]
