# Common workflows

[← Back to README](../README.md)

## Workflow Guide

Typical calls:

- topology only:
  `result = scReebTower(X)`
- topology plus raw graph:
  `result = scReebTower(X, return_raw=True)`
- topology plus persistence:
  `result = scReebTower(X, return_simp_persistence=True)`
- topology plus node ownership:
  `result = scReebTower(X, return_point_assignment=True)`
- topology plus edge ownership:
  `result = scReebTower(X, return_edge_assignment=True)`
- topology plus plotting support:
  `result = scReebTower(X, return_raw=True, return_intermediates=True)`

## Common Patterns

Simplified graph plus raw graph:

```python
result = scReebTower(X, return_raw=True)

simplified = result["simplified"]
raw = result["raw"]
```

Simplified graph plus persistence:

```python
result = scReebTower(X, return_simp_persistence=True)

h1 = result["simplified"]["persistence"]["h1"]
```

Use the second nontrivial diffusion eigenfunction:

```python
result = scReebTower(X, diffusion_eigen_index=2)
```

Use the rooted potential-distance filter:

```python
result = scReebTower(
    X,
    filter_method="rooted_potential_distance",
    diffusion_time="auto",
)
```

Use rooted diffusion shortest-path:

```python
result = scReebTower(
    X,
    filter_method="rooted_diffusion_shortest_path",
)
```

Use a custom scalar filter:

```python
result = scReebTower(W=affinity_matrix, filter_values=my_filter)
```

Simplified graph plus node assignment:

```python
result = scReebTower(X, return_point_assignment=True)

point_assignment = result["simplified"]["point_assignment"]
node_points = result["simplified"]["node_points"]
node_support_points = result["simplified"]["node_support_points"]
```

Simplified graph plus edge assignment:

```python
result = scReebTower(X, return_edge_assignment=True)

edge_points = result["simplified"]["edge_points"]
edge_support_points = result["simplified"]["edge_support_points"]
point_edge_assignment = result["simplified"]["point_edge_assignment"]
point_edges = result["simplified"]["point_edges"]
```

Simplified graph plus cellular decomposition:

```python
result = scReebTower(X, return_cellular_decomposition=True)

cell_kind = result["simplified"]["cell_assignment_kind"]
cell_id = result["simplified"]["cell_assignment_id"]
node_cells = result["simplified"]["node_cells"]
edge_cells = result["simplified"]["edge_cells"]
```

Raw persistence without returning raw edges explicitly:

```python
result = scReebTower(X, return_raw_persistence=True)

raw_pd = result["raw"]["persistence"]
```

Inspect the filter metadata used during construction:

```python
result = scReebTower(
    X,
    filter_method="rooted_potential_distance",
    return_intermediates=True,
)

meta = result["intermediates"]["filter_metadata"]
root_ids = meta["component_root_indices"]
root_pairs = meta["component_root_pairs"]
times = result["intermediates"]["filter_aux_values"]
```

For the default diffusion-eigenfunction filter, `filter_aux_values` contains
the selected per-component diffusion eigenvalues and is also available as
`result["intermediates"]["diffusion_eigenvalues"]`. For the rooted
potential-distance filter, `filter_aux_values` contains the selected
per-component diffusion times.
