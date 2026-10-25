# Assignments, cellular decomposition, and persistence

[← Back to README](../README.md)

## Point Assignment

Point assignment is opt-in via `return_point_assignment=True`.

There are two related but different node-level outputs:

- `node_points`: an ownership partition, one simplified/raw node id per point
- `node_support_points`: the intrinsic local support of each node

If you want the points supporting a trajectory through the simplified graph,
use `edge_support_points` together with a graph path in
`result["simplified"]["edges"]` and take the union of the edge supports along
that path.

When `simplify=True`:

- `node_support_points` are inherited from the kept raw nodes
- `node_points` are a full ownership partition of the dataset onto simplified
  nodes
- ownership is computed by graph Voronoi on the original point graph using
  shortest-path distance on the symmetrized diffusion operator

When `simplify=False`:

- points are assigned to raw Reeb nodes

Returned fields:

- `point_assignment`: node index per point
- `node_points`: ownership partition of points per node
- `node_support_points`: intrinsic support points per node

## Edge Assignment

Edge assignment is opt-in via `return_edge_assignment=True`.

Returned fields:

- `edge_points`: ownership partition of points per edge
- `point_edge_assignment`: one edge id per point
- `edge_support_points`: intrinsic support points per edge
- `point_edges`: overlapping edge-support memberships per point

Raw edge assignment rule:

- for a raw edge connecting `(step s, comp c)` to `(step s+1, comp c_next)`,
  points are assigned if they lie in the connected bridging region across
  levels `s, s+1, s+2` that touches both endpoint node supports

Simplified edge assignment rule:

- simplified edge support is inherited from the contracted raw path behind that
  simplified edge
- inherited support includes raw edge supports on that path plus the support
  points of contracted interior raw nodes
- simplified edge ownership is a full partition of the dataset onto simplified
  edges
- ownership is computed by graph Voronoi on the original point graph using
  shortest-path distance on the symmetrized diffusion operator

## Cellular Decomposition

Cellular decomposition is opt-in via `return_cellular_decomposition=True` and
is only defined on the simplified graph.

It is a mixed disjoint partition of the whole dataset onto:

- simplified node cells, corresponding to 0-cells
- simplified edge cells, corresponding to 1-cells

Returned fields:

- `cell_assignment_kind`: per-point `"node"` or `"edge"`
- `cell_assignment_id`: per-point simplified node id or simplified edge id
- `node_cells`: list of point index arrays, one per simplified node
- `edge_cells`: list of point index arrays, one per simplified edge

This decomposition uses the same graph metric as the ownership assignments:
shortest-path distance on the symmetrized diffusion operator, comparing node
supports against edge supports directly.

Helper for extracting points from selected cells:

```python
from sc_reeb_tower import extract_cellular_trajectory

result = scReebTower(X, return_cellular_decomposition=True)
simplified = result["simplified"]

# Mixed cell indexing: nodes first, then edges.
points = extract_cellular_trajectory(simplified, cell_indices=[0, 3, 7])
```

If there are `n` simplified nodes, then:

- cell indices `0 .. n-1` are node cells
- cell indices `n .. n + m - 1` are edge cells

Helper for enumerating terminal cellular trajectories:

```python
from sc_reeb_tower import enumerate_terminal_cellular_trajectories

result = scReebTower(
    X,
    return_edge_lengths=True,
    return_cellular_decomposition=True,
)
trajectories = enumerate_terminal_cellular_trajectories(result["simplified"])

top = trajectories[0]
top["node_path"]
top["edge_path"]
top["cell_indices"]
top["graph_length"]
```

Here, a terminal simplified node means a node whose multigraph degree is not
equal to `2`, so trajectories run between leaf tips, branch points, isolated
nodes, or loop anchors.

## Edge Lengths

Edge lengths are opt-in via `return_edge_lengths=True`.

- `result["simplified"]["edge_lengths"]`: one filter-space length per simplified edge
- `result["raw"]["edge_lengths"]`: one filter-space length per raw edge

For an edge `(u, v)`, the length is the absolute difference between the
midpoint slice values of its endpoint nodes.

## Persistence

Persistence is opt-in via `return_simp_persistence=True` and
`return_raw_persistence=True`.

This is graph-filtration persistence on the returned multigraph:

- all vertices are born at filtration value `0`
- edges are added in nondecreasing order of edge length
- an edge that merges two connected components creates an `H0` death
- an edge that closes a cycle creates an essential `H1` class with death `inf`

Returned dictionary format:

- `h0`: finite `H0` pairs with shape `(m, 2)`
- `h0_essential`: essential `H0` pairs with shape `(c, 2)`
- `h1`: essential `H1` pairs with shape `(k, 2)`

Example:

```python
result = scReebTower(X, return_simp_persistence=True)
pd = result["simplified"]["persistence"]

h0 = pd["h0"]
h1 = pd["h1"]
```

This is not higher-dimensional simplicial persistence; it is persistence of the
edge-weighted graph itself.
