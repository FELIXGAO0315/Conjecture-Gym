import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C50 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hp1 : ¬ G.IsBipartite) (hp2 : G.Connected) (hn1 : -2 * (G.minDegree : ℤ) + (G.indepNum : ℤ) ≤ 0) (hn2 : -(G.indepNum : ℤ) + (G.diam : ℤ) ≤ 0) :
    2 * (G.radius.toNat : ℤ) ≥ -2 * (G.minDegree : ℤ) + (G.diam : ℤ) + 2 := by
  have s1 : -(G.diam : ℤ) + 2 * (G.radius.toNat : ℤ) ≥ 0 := by
    have hw := diam_le_two_radius_int G hp2
    linarith [hw]
  have s2 : (Fintype.card V : ℤ) - (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
    have hw := chi_le_n_int G
    linarith [hw]
  have s3 : (G.chromaticNumber.toNat : ℤ) ≥ 3 := by
    have hw := not_bipartite_chi_int G hp1
    linarith [hw]
  have s4 : (Fintype.card V : ℤ) ≥ 3 := by linarith [s2, s3]
  have s5 : (G.indepNum : ℤ) ≥ 1 := by
    have hw := alpha_ge_one_int G (by omega)
    linarith [hw]
  have s6 : 2 * (G.minDegree : ℤ) - (G.indepNum : ℤ) ≥ 0 := by linarith [hn1]
  have s7 : 2 * (G.minDegree : ℤ) ≥ 1 := by linarith [s5, s6]
  have s8 : (G.minDegree : ℤ) ≥ 1 := by have hr := s7; omega
  have s9 : 2 * (G.minDegree : ℤ) - (G.diam : ℤ) + 2 * (G.radius.toNat : ℤ) ≥ 2 := by linarith [s1, s8]
  linarith [s9]
