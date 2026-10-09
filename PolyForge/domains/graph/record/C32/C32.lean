import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C32 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hn1 : (Fintype.card V : ℤ) ≤ 4) :
    2 * (G.cliqueNum : ℤ) ≤ (G.chromaticNumber.toNat : ℤ) + (G.indepNum : ℤ) + 3 := by
  have s1 : (G.chromaticNumber.toNat : ℤ) - 2 * (G.cliqueNum : ℤ) + (G.indepNum : ℤ) ≥ -3 := by
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
      have s7 : -(Fintype.card V : ℤ) ≥ -4 := by linarith [hn1]
      have s8 : -(G.cliqueNum : ℤ) ≥ -4 := by linarith [s2, s3, s7]
      have s9 : (G.chromaticNumber.toNat : ℤ) - 2 * (G.cliqueNum : ℤ) + (G.indepNum : ℤ) ≥ -3 := by linarith [s2, s6, s8]
      linarith [s9]
    · -- 1*chi <= 2
      have s10 : (G.chromaticNumber.toNat : ℤ) - (G.cliqueNum : ℤ) ≥ 0 := by
        have hw := omega_le_chi_int G
        linarith [hw]
      have s11 : (G.indepNum : ℤ) ≥ 0 := by positivity
      have s12 : -(G.chromaticNumber.toNat : ℤ) ≥ -2 := by have hcc := hc1; omega
      have s13 : (G.chromaticNumber.toNat : ℤ) - 2 * (G.cliqueNum : ℤ) + (G.indepNum : ℤ) ≥ -2 := by linarith [s10, s11, s12]
      linarith [s13]
  linarith [s1]
