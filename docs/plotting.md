# Plotting

[← Back to README](../README.md)

`plot_scReebTower()` overlays the simplified graph on a 2D or 3D embedding that you
compute separately. It requires the `[plot]` extra
(`pip install "sc-reeb-tower[plot]"`), which installs `matplotlib` and `networkx`.

```python
from sc_reeb_tower import scReebTower, plot_scReebTower

result = scReebTower(X, return_raw=True, return_intermediates=True)

fig, node_pos = plot_scReebTower(
    pts=embedding_2d,
    simp_edges=result["simplified"]["edges"],
    keep_ids=result["simplified"]["keep_ids"],
    reeb_nodes=result["raw"]["nodes"],
    step_vertices=result["intermediates"]["step_vertices"],
    step_comp_ids=result["intermediates"]["step_comp_ids"],
    uniq_v=result["intermediates"]["prep_state"]["uniq_v"],
)
```

Practical notes:

- `pts` must be a 2D or 3D embedding in the same row order as `X`
- if you ran `scReebTower(W=...)`, `pts` must instead match the row order of `W`
- 2D multiedges are drawn as curved arcs so parallel edges are legible
- cycle edges are colored crimson when `color_cycles=True`
- node labels show multigraph degree when `label_degree=True`
- the function returns `(fig, node_pos)` so you can save or modify the figure

## Index alignment

`plot_scReebTower()` assumes the embedding array `pts` is aligned row-for-row with the
nodes of the graph passed to `scReebTower()`: the rows of `X` when using `X=...`, or
the rows of `W` when using `W=...`.

How node membership is recovered for plotting:

- each raw Reeb node is identified by `(step, comp)` in `reeb_nodes`
- `step_vertices[step]` gives the compacted active vertex indices in that slice
- `step_comp_ids[step]` gives the component id for each active vertex
- compacted indices map back to original point indices through
  `prep_state["uniq_v"]`
- those original indices are used to index into `pts` and compute node centroids

If you shuffle or subset your data before embedding, apply the same
transformation to both `X` and `pts`, or remap indices accordingly.
