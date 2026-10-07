# HexForge — 10 example conjectures (hardness gradient)


## 1. C96

**formula**

```
if ((is_simple) and (f_2>=_9) and (sum_pk_after_p6 <= 2) and (3*p_3 - 2*p_5 >= 0)), then p6 >= ((((-2 * p4) + (-1 * p5)) + 3))
```

**natural_language**

Let M be a simple 3-polytope (a simple 3-connected planar map), with p_k the number of k-gonal faces, f_2 the total number of faces, and sum_{k>=7} p_k the number of faces of size at least 7. Suppose f_2 >= 9, sum_pk_after_p6 <= 2, 3*p_3 - 2*p_5 >= 0. Then p_6 >= -2*p_4 - p_5 + 3.


## 2. C12

**formula**

```
if ((is_simple) and (-p_3 + 2*p_5 >= 0) and (p_4 >= 2)), then p6 >= ((((-2 * p4) + (-2 * p5)) + 8))
```

**natural_language**

Let M be a simple 3-polytope (a simple 3-connected planar map), with p_k the number of k-gonal faces, f_2 the total number of faces, and sum_{k>=7} p_k the number of faces of size at least 7. Suppose -p_3 + 2*p_5 >= 0, p_4 >= 2. Then p_6 >= -2*p_4 - 2*p_5 + 8.


## 3. C206

**formula**

```
if ((is_simple) and (f_2>=_11) and (p_4 = 0) and (f_2<=_34)), then p6 >= ((((-0.5 * p5) + (-0.5 * sum_pk_after_p6)) + 3))
```

**natural_language**

Let M be a simple 3-polytope (a simple 3-connected planar map), with p_k the number of k-gonal faces, f_2 the total number of faces, and sum_{k>=7} p_k the number of faces of size at least 7. Suppose f_2 >= 11, p_4 = 0, f_2 <= 34. Then 2*p_6 >= -p_5 - sum_pk_after_p6 + 6.


## 4. C98

**formula**

```
if ((is_simple) and (f_2>=_16) and (-3*p_4 + 2*p_5 >= 0) and (sum_pk_after_p6 >= 3)), then p6 >= ((((-1 * p3) + (-0.5 * p5)) + 4))
```

**natural_language**

Let M be a simple 3-polytope (a simple 3-connected planar map), with p_k the number of k-gonal faces, f_2 the total number of faces, and sum_{k>=7} p_k the number of faces of size at least 7. Suppose f_2 >= 16, -3*p_4 + 2*p_5 >= 0, sum_pk_after_p6 >= 3. Then 2*p_6 >= -2*p_3 - p_5 + 8.


## 5. C63

**formula**

```
if ((is_simple) and (f_2>=_12) and (p_4 <= 2)), then p6 >= ((((-2 * p3) + (-2 * p5)) + 10))
```

**natural_language**

Let M be a simple 3-polytope (a simple 3-connected planar map), with p_k the number of k-gonal faces, f_2 the total number of faces, and sum_{k>=7} p_k the number of faces of size at least 7. Suppose f_2 >= 12, p_4 <= 2. Then p_6 >= -2*p_3 - 2*p_5 + 10.


## 6. C48

**formula**

```
if ((is_simple) and (f_2>=_12) and (sum_pk_after_p6 <= 6) and (p_4 <= 4)), then p6 >= ((((0.5 * p3) + (-1 * p5)) + -4))
```

**natural_language**

Let M be a simple 3-polytope (a simple 3-connected planar map), with p_k the number of k-gonal faces, f_2 the total number of faces, and sum_{k>=7} p_k the number of faces of size at least 7. Suppose f_2 >= 12, sum_pk_after_p6 <= 6, p_4 <= 4. Then 2*p_6 >= p_3 - 2*p_5 - 8.


## 7. C173

**formula**

```
if ((is_simple) and (f_2>=_10) and (sum_pk_after_p6 <= 3) and (f_2<=_15)), then p6 >= ((((-0.5 * p4) + (-0.5 * p5)) + 1.5))
```

**natural_language**

Let M be a simple 3-polytope (a simple 3-connected planar map), with p_k the number of k-gonal faces, f_2 the total number of faces, and sum_{k>=7} p_k the number of faces of size at least 7. Suppose f_2 >= 10, sum_pk_after_p6 <= 3, f_2 <= 15. Then 2*p_6 >= -p_4 - p_5 + 3.


## 8. C97

**formula**

```
if ((is_simple) and (f_2>=_16) and (sum_pk_after_p6 <= 4) and (p_3 >= 2)), then p6 >= ((((-0.5 * p4) + (-1 * p5)) + 3))
```

**natural_language**

Let M be a simple 3-polytope (a simple 3-connected planar map), with p_k the number of k-gonal faces, f_2 the total number of faces, and sum_{k>=7} p_k the number of faces of size at least 7. Suppose f_2 >= 16, sum_pk_after_p6 <= 4, p_3 >= 2. Then 2*p_6 >= -p_4 - 2*p_5 + 6.


## 9. C56

**formula**

```
if ((is_simple) and (f_2>=_8) and (p_3 - p_4 >= 0)), then p6 >= ((((-1 * p3) + (-1 * p5)) + 4))
```

**natural_language**

Let M be a simple 3-polytope (a simple 3-connected planar map), with p_k the number of k-gonal faces, f_2 the total number of faces, and sum_{k>=7} p_k the number of faces of size at least 7. Suppose f_2 >= 8, p_3 - p_4 >= 0. Then p_6 >= -p_3 - p_5 + 4.


## 10. C168

**formula**

```
if ((is_simple) and (p_5 = 0) and (sum_pk_after_p6 <= 3)), then p6 >= ((((-0.5 * p4) + sum_pk_after_p6) + -1))
```

**natural_language**

Let M be a simple 3-polytope (a simple 3-connected planar map), with p_k the number of k-gonal faces, f_2 the total number of faces, and sum_{k>=7} p_k the number of faces of size at least 7. Suppose p_5 = 0, sum_pk_after_p6 <= 3. Then 2*p_6 >= -p_4 + 2*sum_pk_after_p6 - 2.
