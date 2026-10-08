import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C61 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hp1 : 2 ≤ Fintype.card V) (hp2 : G.IsTree) (hn1 : (G.diam : ℤ) ≥ 3) :
    -(G.chromaticNumber.toNat : ℤ) + 2 * (G.cliqueNum : ℤ) - 2 * (G.radius.toNat : ℤ) ≤ -2 := by
  have s1 : -(G.diam : ℤ) + 2 * (G.radius.toNat : ℤ) ≥ 0 := by
    have hw := diam_le_two_radius_int G (isTree_connected G hp2)
    linarith [hw]
  have s2 : (G.diam : ℤ) ≥ 3 := by linarith [hn1]
  have s3 : 2 * (G.radius.toNat : ℤ) ≥ 3 := by linarith [s1, s2]
  have s4 : (G.radius.toNat : ℤ) ≥ 2 := by have hr := s3; omega
  have s5 : (G.chromaticNumber.toNat : ℤ) - (G.cliqueNum : ℤ) ≥ 0 := by
    have hw := omega_le_chi_int G
    linarith [hw]
  have s6 : -(G.chromaticNumber.toNat : ℤ) ≥ -2 := by
    have hw := acyclic_chi_int G (isTree_acyclic G hp2)
    linarith [hw]
  have s7 : (G.chromaticNumber.toNat : ℤ) - 2 * (G.cliqueNum : ℤ) ≥ -2 := by linarith [s5, s6]
  have s8 : (G.chromaticNumber.toNat : ℤ) - 2 * (G.cliqueNum : ℤ) + 2 * (G.radius.toNat : ℤ) ≥ 2 := by linarith [s4, s7]
  linarith [s8]
