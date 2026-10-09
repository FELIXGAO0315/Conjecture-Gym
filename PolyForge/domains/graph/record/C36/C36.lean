import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C36 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hp1 : ¬ G.IsAcyclic) (hp2 : G.Connected) (hn1 : (G.diam : ℤ) ≥ 3) (hn2 : (G.maxDegree : ℤ) ≥ 4) :
    (G.cliqueNum : ℤ) ≤ (G.chromaticNumber.toNat : ℤ) + 2 * (G.radius.toNat : ℤ) - 4 := by
  have s1 : (G.chromaticNumber.toNat : ℤ) - (G.cliqueNum : ℤ) ≥ 0 := by
    have hw := omega_le_chi_int G
    linarith [hw]
  have s2 : -(G.diam : ℤ) + 2 * (G.radius.toNat : ℤ) ≥ 0 := by
    have hw := diam_le_two_radius_int G hp2
    linarith [hw]
  have s3 : (G.diam : ℤ) ≥ 3 := by linarith [hn1]
  have s4 : 2 * (G.radius.toNat : ℤ) ≥ 3 := by linarith [s2, s3]
  have s5 : (G.radius.toNat : ℤ) ≥ 2 := by have hr := s4; omega
  have s6 : (G.chromaticNumber.toNat : ℤ) - (G.cliqueNum : ℤ) + 2 * (G.radius.toNat : ℤ) ≥ 4 := by linarith [s1, s5]
  linarith [s6]
