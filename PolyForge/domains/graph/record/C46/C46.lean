import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C46 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hp1 : G.IsTree) (hp2 : G.IsBipartite) (hn1 : -2 * (G.maxDegree : ℤ) + (G.chromaticNumber.toNat : ℤ) ≥ 0) :
    2 * (G.maxDegree : ℤ) - 2 * (G.chromaticNumber.toNat : ℤ) - (G.radius.toNat : ℤ) ≤ -2 := by
  have s1 : (G.radius.toNat : ℤ) ≥ 0 := by positivity
  have s2 : (G.edgeFinset.card : ℤ) ≥ 0 := by positivity
  have s3 : -(Fintype.card V : ℤ) + (G.edgeFinset.card : ℤ) = -1 := by
    have hw := tree_edges_int G hp1
    linarith [hw]
  have s4 : (Fintype.card V : ℤ) ≥ 1 := by linarith [s2, s3]
  have s5 : (G.chromaticNumber.toNat : ℤ) ≥ 1 := by
    have hw := chi_ge_one_int G (by omega)
    linarith [hw]
  have s6 : -2 * (G.maxDegree : ℤ) + (G.chromaticNumber.toNat : ℤ) ≥ 0 := by linarith [hn1]
  have s7 : -2 * (G.maxDegree : ℤ) + 2 * (G.chromaticNumber.toNat : ℤ) ≥ 1 := by linarith [s5, s6]
  have s8 : -(G.maxDegree : ℤ) + (G.chromaticNumber.toNat : ℤ) ≥ 1 := by have hr := s7; omega
  have s9 : -2 * (G.maxDegree : ℤ) + 2 * (G.chromaticNumber.toNat : ℤ) + (G.radius.toNat : ℤ) ≥ 2 := by linarith [s1, s8]
  linarith [s9]
