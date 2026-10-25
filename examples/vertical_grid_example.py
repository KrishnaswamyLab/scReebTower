"""Run the midpoint Reeb construction on a four-neighbor square grid."""

from __future__ import annotations

import argparse
import json
from pathlib import Path

import matplotlib.pyplot as plt
import numpy as np
import scipy.sparse as sp

from sc_reeb_tower.reeb import build_reeb_graph, prepare_reeb
from sc_reeb_tower.simplify import simplify_reeb_graph


def four_neighbor_square(side: int) -> tuple[np.ndarray, sp.csr_matrix]:
    """Return an evenly spaced square lattice and its four-neighbor graph."""
    if side < 3:
        raise ValueError("side must be at least 3")

    axis = np.linspace(0.0, 1.0, side)
    xx, yy = np.meshgrid(axis, axis)
    points = np.column_stack((xx.ravel(), yy.ravel()))

    rows: list[int] = []
    cols: list[int] = []

    def vertex(row: int, col: int) -> int:
        return row * side + col

    for row in range(side):
        for col in range(side):
            u = vertex(row, col)
            if col + 1 < side:
                v = vertex(row, col + 1)
                rows.extend((u, v))
                cols.extend((v, u))
            if row + 1 < side:
                v = vertex(row + 1, col)
                rows.extend((u, v))
                cols.extend((v, u))

    data = np.ones(len(rows), dtype=float)
    adjacency = sp.csr_matrix(
        (data, (np.asarray(rows), np.asarray(cols))),
        shape=(side * side, side * side),
    )
    return points, adjacency


def raw_node_positions(
    nodes: list[dict],
    step_vertices: list[np.ndarray],
    step_comp_ids: list[np.ndarray],
    prep: dict,
    points: np.ndarray,
) -> np.ndarray:
    """Position a raw node at the mean x-coordinate of its component support."""
    positions = np.empty((len(nodes), 2), dtype=float)
    for node in nodes:
        node_id = int(node["id"])
        step = int(node["step"])
        component = int(node["comp"])
        compact_vertices = step_vertices[step][step_comp_ids[step] == component]
        original_vertices = prep["uniq_v"][compact_vertices]
        positions[node_id] = (
            float(np.mean(points[original_vertices, 0])),
            float(prep["t_vals"][step]),
        )
    return positions


def plot_edges(ax, positions: np.ndarray, edges, **kwargs) -> None:
    for u, v in edges:
        segment = positions[[int(u), int(v)]]
        ax.plot(segment[:, 0], segment[:, 1], **kwargs)


def plot_crossing_slices(ax, points: np.ndarray, adjacency: sp.csr_matrix, prep: dict) -> None:
    """Show several support-induced slice graphs inside the original grid."""
    upper = sp.triu(adjacency, k=1).tocoo()
    for u, v in zip(upper.row, upper.col):
        segment = points[[u, v]]
        ax.plot(segment[:, 0], segment[:, 1], color="#dfe5e1", lw=0.35, zorder=0)
    ax.scatter(points[:, 0], points[:, 1], color="#a8b5ad", s=4, zorder=1)

    slice_indices = np.linspace(0, int(prep["S"]) - 1, 5, dtype=int)[1:-1]
    colors = ("#d65f3c", "#2d7fa3", "#d99a22")
    for step, color in zip(slice_indices, colors):
        active = (prep["lmin"] <= step) & (step < prep["lmax"])
        active_compact = np.unique(
            np.concatenate((prep["ei_c"][active], prep["ej_c"][active]))
        )
        active_original = np.zeros(points.shape[0], dtype=bool)
        active_original[prep["uniq_v"][active_compact]] = True

        support_edges = active_original[upper.row] & active_original[upper.col]
        for edge_index, (u, v) in enumerate(
            zip(upper.row[support_edges], upper.col[support_edges])
        ):
            segment = points[[u, v]]
            label = f"$t={prep['t_vals'][step]:.3f}$" if edge_index == 0 else None
            ax.plot(
                segment[:, 0], segment[:, 1], color=color, lw=1.15,
                alpha=0.8, label=label, zorder=2,
            )

        original_u = prep["uniq_v"][prep["ei_c"][active]]
        original_v = prep["uniq_v"][prep["ej_c"][active]]
        for u, v in zip(original_u, original_v):
            segment = points[[u, v]]
            ax.plot(
                segment[:, 0], segment[:, 1], color=color, lw=2.5,
                zorder=3,
            )

    ax.set_title("Example support-induced slices\n1 connected component per slice")
    ax.set_xlabel("$x$")
    ax.set_ylabel("$f=y$")
    ax.set_aspect("equal")
    ax.legend(loc="lower right", frameon=True, fontsize=8)


def make_figure(
    output: Path,
    points: np.ndarray,
    adjacency: sp.csr_matrix,
    prep: dict,
    raw_nodes: list[dict],
    raw_edges: list[tuple[int, int]],
    raw_positions: np.ndarray,
    simplified_edges: list[tuple[int, int]],
    keep_ids: np.ndarray,
    component_count: int,
) -> None:
    fig, axes = plt.subplots(1, 5, figsize=(21, 5.1), constrained_layout=True)
    grid_ax, slices_ax, raw_ax, simple_ax, target_ax = axes

    upper = sp.triu(adjacency, k=1).tocoo()
    for u, v in zip(upper.row, upper.col):
        segment = points[[u, v]]
        grid_ax.plot(segment[:, 0], segment[:, 1], color="#a8b5ad", lw=0.45)
    grid_ax.scatter(
        points[:, 0], points[:, 1], c=points[:, 1], cmap="viridis",
        s=7, zorder=2,
    )
    grid_ax.set_title("Input: four-neighbor grid\n$f(x,y)=y$")
    grid_ax.set_xlabel("$x$")
    grid_ax.set_ylabel("$f=y$")
    grid_ax.set_aspect("equal")

    plot_crossing_slices(slices_ax, points, adjacency, prep)

    plot_edges(raw_ax, raw_positions, raw_edges, color="#d65f3c", lw=0.8, alpha=0.8)
    raw_ax.scatter(
        raw_positions[:, 0], raw_positions[:, 1],
        color="#253b36", s=7, zorder=2,
    )
    raw_ax.set_title(
        f"Actual raw output\n{len(raw_nodes)} nodes, {len(raw_edges)} edges"
    )

    simplified_positions = raw_positions[keep_ids]
    plot_edges(
        simple_ax, simplified_positions, simplified_edges,
        color="#d65f3c", lw=2.0,
    )
    simple_ax.scatter(
        simplified_positions[:, 0], simplified_positions[:, 1],
        color="#253b36", s=18, zorder=2,
    )
    simple_ax.set_title(
        f"After degree-two suppression\n{component_count} interval"
    )

    target_ax.plot([0.5, 0.5], [0.0, 1.0], color="#168a75", lw=5)
    target_ax.scatter([0.5, 0.5], [0.0, 1.0], color="#253b36", s=35, zorder=2)
    target_ax.set_title("Continuum Reeb graph\n1 interval")

    for ax in (raw_ax, simple_ax):
        ax.set_xlabel("mean support $x$")
        ax.set_ylabel("slice height")
        ax.set_xlim(-0.04, 1.04)
        ax.set_ylim(-0.04, 1.04)
        ax.grid(color="#dfe5e1", lw=0.5)

    target_ax.set_xlim(0.0, 1.0)
    target_ax.set_ylim(-0.04, 1.04)
    target_ax.set_xticks([])
    target_ax.set_ylabel("Reeb height")
    target_ax.grid(axis="y", color="#dfe5e1", lw=0.5)

    fig.suptitle(
        "Support-induced midpoint construction on a square lattice",
        fontsize=15,
        fontweight="bold",
    )
    fig.savefig(output, dpi=220, bbox_inches="tight")
    plt.close(fig)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--side", type=int, default=21)
    parser.add_argument(
        "--output",
        type=Path,
        default=Path("artifacts/vertical_grid_reeb_output.png"),
    )
    args = parser.parse_args()

    points, adjacency = four_neighbor_square(args.side)
    filter_values = points[:, 1]

    prep = prepare_reeb(adjacency, filter_values)
    raw_nodes, raw_edges, step_vertices, step_comp_ids = build_reeb_graph(prep)
    (
        simplified_edges,
        keep_ids,
        beta1,
        component_count,
    ) = simplify_reeb_graph(raw_nodes, raw_edges)
    positions = raw_node_positions(
        raw_nodes, step_vertices, step_comp_ids, prep, points
    )

    assert all(np.unique(ids).size == 1 for ids in step_comp_ids)
    assert component_count == 1
    assert len(raw_nodes) == args.side - 1
    assert len(raw_edges) == args.side - 2
    assert keep_ids.size == 2
    assert len(simplified_edges) == 1
    assert beta1 == 0

    args.output.parent.mkdir(parents=True, exist_ok=True)
    make_figure(
        args.output,
        points,
        adjacency,
        prep,
        raw_nodes,
        raw_edges,
        positions,
        simplified_edges,
        keep_ids,
        component_count,
    )

    summary = {
        "grid_side": args.side,
        "sample_points": int(points.shape[0]),
        "mesh_size": 1.0 / (args.side - 1),
        "slice_connectivity": "original graph induced by crossing endpoints",
        "midpoint_slices": int(prep["S"]),
        "components_per_slice": [
            int(np.unique(component_ids).size) for component_ids in step_comp_ids
        ],
        "raw_nodes": len(raw_nodes),
        "raw_edges": len(raw_edges),
        "simplified_nodes": int(keep_ids.size),
        "simplified_edges": len(simplified_edges),
        "simplified_connected_components": int(component_count),
        "simplified_beta1": int(beta1),
        "expected_continuum_components": 1,
        "figure": str(args.output),
    }
    summary_path = args.output.with_suffix(".json")
    summary_path.write_text(json.dumps(summary, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(summary, indent=2))


if __name__ == "__main__":
    main()
