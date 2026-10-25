"""Run the midpoint Reeb construction with a diagonal square-grid filter."""

from __future__ import annotations

import argparse
import json
from pathlib import Path

import matplotlib.pyplot as plt
import numpy as np
import scipy.sparse as sp

from vertical_grid_example import (
    four_neighbor_square,
    plot_edges,
    raw_node_positions,
)
from sc_reeb_tower.reeb import build_reeb_graph, prepare_reeb
from sc_reeb_tower.simplify import simplify_reeb_graph


def diagonal_filter(side: int) -> np.ndarray:
    """Compute tied diagonal levels from integer indices before normalizing."""
    columns, rows = np.meshgrid(np.arange(side), np.arange(side))
    return (columns + rows).ravel().astype(float) / (2 * (side - 1))


def draw_grid(ax, points: np.ndarray, adjacency: sp.csr_matrix, color_values) -> None:
    upper = sp.triu(adjacency, k=1).tocoo()
    for u, v in zip(upper.row, upper.col):
        segment = points[[u, v]]
        ax.plot(segment[:, 0], segment[:, 1], color="#a8b5ad", lw=0.45)
    ax.scatter(
        points[:, 0], points[:, 1], c=color_values, cmap="viridis",
        s=7, zorder=2,
    )
    ax.set_xlim(-0.04, 1.04)
    ax.set_ylim(-0.04, 1.04)
    ax.set_xlabel("$x$")
    ax.set_ylabel("$y$")
    ax.set_aspect("equal")


def draw_crossing_slices(
    ax,
    points: np.ndarray,
    adjacency: sp.csr_matrix,
    prep: dict,
) -> None:
    upper = sp.triu(adjacency, k=1).tocoo()
    for u, v in zip(upper.row, upper.col):
        segment = points[[u, v]]
        ax.plot(segment[:, 0], segment[:, 1], color="#dfe5e1", lw=0.35, zorder=0)
    ax.scatter(points[:, 0], points[:, 1], color="#a8b5ad", s=4, zorder=1)

    slice_indices = np.linspace(0, int(prep["S"]) - 1, 5, dtype=int)[1:-1]
    colors = ("#d65f3c", "#2d7fa3", "#d99a22")
    for step, color in zip(slice_indices, colors):
        active = (prep["lmin"] <= step) & (step < prep["lmax"])
        original_u = prep["uniq_v"][prep["ei_c"][active]]
        original_v = prep["uniq_v"][prep["ej_c"][active]]
        for edge_index, (u, v) in enumerate(zip(original_u, original_v)):
            segment = points[[u, v]]
            label = f"$t={prep['t_vals'][step]:.3f}$" if edge_index == 0 else None
            ax.plot(
                segment[:, 0], segment[:, 1], color=color, lw=2.3,
                label=label, zorder=2,
            )

    ax.set_title("Example crossing subgraphs\n1 connected staircase per slice")
    ax.set_xlim(-0.04, 1.04)
    ax.set_ylim(-0.04, 1.04)
    ax.set_xlabel("$x$")
    ax.set_ylabel("$y$")
    ax.set_aspect("equal")
    ax.legend(loc="upper right", frameon=True, fontsize=8)


def make_figure(
    output: Path,
    points: np.ndarray,
    adjacency: sp.csr_matrix,
    filter_values: np.ndarray,
    prep: dict,
    raw_nodes: list[dict],
    raw_edges: list[tuple[int, int]],
    raw_positions: np.ndarray,
    simplified_edges: list[tuple[int, int]],
    keep_ids: np.ndarray,
) -> None:
    fig, axes = plt.subplots(1, 5, figsize=(21, 5.1), constrained_layout=True)
    grid_ax, slices_ax, raw_ax, simple_ax, target_ax = axes

    draw_grid(grid_ax, points, adjacency, filter_values)
    grid_ax.set_title("Input: four-neighbor grid\n$f(x,y)=(x+y)/2$")
    draw_crossing_slices(slices_ax, points, adjacency, prep)

    plot_edges(raw_ax, raw_positions, raw_edges, color="#d65f3c", lw=1.3)
    raw_ax.scatter(
        raw_positions[:, 0], raw_positions[:, 1],
        color="#253b36", s=13, zorder=2,
    )
    raw_ax.set_title(
        f"Actual raw output\n{len(raw_nodes)} nodes, {len(raw_edges)} edges"
    )

    simplified_positions = raw_positions[keep_ids]
    plot_edges(
        simple_ax, simplified_positions, simplified_edges,
        color="#d65f3c", lw=4.0,
    )
    simple_ax.scatter(
        simplified_positions[:, 0], simplified_positions[:, 1],
        color="#253b36", s=35, zorder=2,
    )
    simple_ax.set_title("After degree-two suppression\n1 interval")

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
        "Diagonal filter on a square lattice",
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
        default=Path("artifacts/diagonal_grid_reeb_output.png"),
    )
    args = parser.parse_args()

    points, adjacency = four_neighbor_square(args.side)
    filter_values = diagonal_filter(args.side)
    prep = prepare_reeb(adjacency, filter_values)
    raw_nodes, raw_edges, step_vertices, step_comp_ids = build_reeb_graph(prep)
    simplified_edges, keep_ids, beta1, component_count = simplify_reeb_graph(
        raw_nodes, raw_edges
    )
    positions = raw_node_positions(
        raw_nodes, step_vertices, step_comp_ids, prep, points
    )

    assert all(np.unique(ids).size == 1 for ids in step_comp_ids)
    assert len(raw_nodes) == 2 * (args.side - 1)
    assert len(raw_edges) == len(raw_nodes) - 1
    assert keep_ids.size == 2
    assert len(simplified_edges) == 1
    assert component_count == 1
    assert beta1 == 0

    args.output.parent.mkdir(parents=True, exist_ok=True)
    make_figure(
        args.output,
        points,
        adjacency,
        filter_values,
        prep,
        raw_nodes,
        raw_edges,
        positions,
        simplified_edges,
        keep_ids,
    )

    summary = {
        "grid_side": args.side,
        "sample_points": int(points.shape[0]),
        "filter": "(integer column + integer row) / (2 * (side - 1))",
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
