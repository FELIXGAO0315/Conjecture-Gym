import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C59 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hn1 : (G.chromaticNumber.toNat : ℤ) ≤ 5) :
    -(Fintype.card V : ℤ) + 2 * (G.cliqueNum : ℤ) - 2 * (G.indepNum : ℤ) ≤ 3 := by
  have s1 : (Fintype.card V : ℤ) - 2 * (G.cliqueNum : ℤ) + 2 * (G.indepNum : ℤ) ≥ -3 := by
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
      have s7 : -(G.chromaticNumber.toNat : ℤ) ≥ -5 := by linarith [hn1]
      have s8 : (Fintype.card V : ℤ) - 2 * (G.cliqueNum : ℤ) + 2 * (G.indepNum : ℤ) ≥ -3 := by linarith [s2, s3, s6, s7]
      linarith [s8]
    · -- 1*chi <= 2
      have s9 : (G.chromaticNumber.toNat : ℤ) - (G.cliqueNum : ℤ) ≥ 0 := by
        have hw := omega_le_chi_int G
        linarith [hw]
      have s10 : (Fintype.card V : ℤ) - (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
        have hw := chi_le_n_int G
        linarith [hw]
      have s11 : (G.indepNum : ℤ) ≥ 0 := by positivity
      have s12 : -(G.chromaticNumber.toNat : ℤ) ≥ -2 := by have hcc := hc1; omega
      have s13 : (Fintype.card V : ℤ) - 2 * (G.cliqueNum : ℤ) + 2 * (G.indepNum : ℤ) ≥ -2 := by linarith [s9, s10, s11, s12]
      linarith [s13]
  linarith [s1]
