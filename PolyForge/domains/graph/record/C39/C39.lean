import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C39 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hp1 : G.Connected) (hp2 : ¬ G.IsAcyclic) (hn1 : (G.minDegree : ℤ) ≤ 3) :
    (G.cliqueNum : ℤ) ≤ (Fintype.card V : ℤ) + 2 * (G.radius.toNat : ℤ) - 2 := by
  have s1 : -(G.diam : ℤ) + 2 * (G.radius.toNat : ℤ) ≥ 0 := by
    have hw := diam_le_two_radius_int G hp1
    linarith [hw]
  have s2 : 2 * (G.diam : ℤ) - (G.girth : ℤ) ≥ -1 := by
    have hw := girth_le_diam_int G hp1 hp2
    linarith [hw]
  have s3 : (G.girth : ℤ) ≥ 3 := by
    have hw := girth_ge_three_int G hp2
    linarith [hw]
  have s4 : 2 * (G.radius.toNat : ℤ) ≥ 1 := by linarith [s1, s2, s3]
  have s5 : (G.radius.toNat : ℤ) ≥ 1 := by have hr := s4; omega
  have s6 : (G.chromaticNumber.toNat : ℤ) - (G.cliqueNum : ℤ) ≥ 0 := by
    have hw := omega_le_chi_int G
    linarith [hw]
  have s7 : (Fintype.card V : ℤ) - (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
    have hw := chi_le_n_int G
    linarith [hw]
  have s8 : (Fintype.card V : ℤ) - (G.cliqueNum : ℤ) ≥ 0 := by linarith [s6, s7]
  have s9 : (Fintype.card V : ℤ) - (G.cliqueNum : ℤ) + 2 * (G.radius.toNat : ℤ) ≥ 2 := by linarith [s5, s8]
  linarith [s9]
