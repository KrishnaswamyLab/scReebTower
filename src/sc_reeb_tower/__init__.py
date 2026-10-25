from .sc_reeb_tower import scReebTower
from .graph import build_affinity_matrix, build_diffusion_operator, validate_affinity_matrix
from .filter import compute_diffusion_filter
from .persistence import compute_edge_lengths, compute_graph_persistence
from .reeb import prepare_reeb, build_reeb_graph
from .io import save_reeb, load_reeb
try:
    from .visualize import plot_scReebTower
except ImportError:  # Optional dependency for numerical-only environments.
    def plot_scReebTower(*args, **kwargs):
        raise ImportError(
            "plot_scReebTower requires matplotlib and networkx. "
            "Install them with: pip install 'sc-reeb-tower[plot]'"
        )
from .simplify import (
    simplify_reeb_graph,
    assign_points_to_simplified_nodes,
    assign_points_to_raw_nodes,
    assign_points_to_raw_edges,
    assign_points_to_simplified_edges,
    extract_cellular_trajectory,
    enumerate_terminal_cellular_trajectories,
)

__all__ = [
    "scReebTower",
    "plot_scReebTower",
    "save_reeb",
    "load_reeb",
    "extract_cellular_trajectory",
    "enumerate_terminal_cellular_trajectories",
    "build_affinity_matrix",
    "validate_affinity_matrix",
    "build_diffusion_operator",
    "compute_diffusion_filter",
    "compute_edge_lengths",
    "compute_graph_persistence",
    "prepare_reeb",
    "build_reeb_graph",
    "simplify_reeb_graph",
    "assign_points_to_simplified_nodes",
    "assign_points_to_raw_nodes",
    "assign_points_to_raw_edges",
    "assign_points_to_simplified_edges",
]
