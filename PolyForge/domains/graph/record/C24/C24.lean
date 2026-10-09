import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C24 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hp1 : ¬ G.IsBipartite) (hp2 : G.Connected) (hn1 : (G.diam : ℤ) ≥ 1) :
    (G.maxDegree : ℤ) ≤ 2 * (Fintype.card V : ℤ) + 2 * (G.radius.toNat : ℤ) - 6 := by
  have s1 : (Fintype.card V : ℤ) - (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
    have hw := chi_le_n_int G
    linarith [hw]
  have s2 : (G.chromaticNumber.toNat : ℤ) ≥ 3 := by
    have hw := not_bipartite_chi_int G hp1
    linarith [hw]
  have s3 : (Fintype.card V : ℤ) ≥ 3 := by linarith [s1, s2]
  have s4 : -(G.diam : ℤ) + 2 * (G.radius.toNat : ℤ) ≥ 0 := by
    have hw := diam_le_two_radius_int G hp2
    linarith [hw]
  have s5 : (G.diam : ℤ) ≥ 1 := by linarith [hn1]
  have s6 : 2 * (G.radius.toNat : ℤ) ≥ 1 := by linarith [s4, s5]
  have s7 : (G.radius.toNat : ℤ) ≥ 1 := by have hr := s6; omega
  have s8 : (Fintype.card V : ℤ) - (G.maxDegree : ℤ) ≥ 1 := by
    have hw := max_lt_card_int G (by omega)
    linarith [hw]
  have s9 : 2 * (Fintype.card V : ℤ) - (G.maxDegree : ℤ) + 2 * (G.radius.toNat : ℤ) ≥ 6 := by linarith [s3, s7, s8]
  linarith [s9]
