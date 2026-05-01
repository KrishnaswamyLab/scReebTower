import numpy as np
import scipy.sparse as sp
from scipy.sparse.csgraph import connected_components

from .graph import build_affinity_matrix, build_diffusion_operator, validate_affinity_matrix
from .filter import compute_diffusion_filter, _quantize_filter_values, _select_diffusion_time
from .reeb import prepare_reeb, build_reeb_graph
from .persistence import compute_edge_lengths, compute_graph_persistence
from .simplify import (
    simplify_reeb_graph,
    assign_points_to_simplified_nodes,
    assign_points_to_raw_nodes,
    assign_points_to_raw_edges,
    assign_points_to_simplified_edges,
    build_simplified_cellular_decomposition,
)


def dreeb(
    X=None,
    W=None,
    filter_values=None,
    k=80,
    k_smooth=None,
    precision=1.0,
    t=0,
    t_max=100,
    diffusion_eigen_index=1,
    filter_method="diffusion_eigenfunction",
    diffusion_time="auto",
    diffusion_time_max=40,
    simplify=True,
    return_raw=False,
    return_edge_lengths=False,
    return_simp_persistence=False,
    return_raw_persistence=False,
    return_point_assignment=False,
    return_edge_assignment=False,
    return_cellular_decomposition=False,
    return_intermediates=False,
):
    """
    Run the full dReeb pipeline.

    Parameters
    ----------
    X : array-like, shape (n_samples, n_features), optional
        Input point cloud data. Provide exactly one of `X` or `W`.
    W : array-like or scipy.sparse matrix, shape (n_samples, n_samples), optional
        Precomputed affinity matrix. Larger values represent stronger
        connections. Provide exactly one of `X` or `W`.
    filter_values : array-like, shape (n_samples,), optional
        User-supplied scalar filter on graph vertices. When provided,
        `dreeb` uses this filter directly instead of constructing one
        with `filter_method`.
    k : int, optional (default: 80)
        Number of nearest neighbors
    k_smooth : int, optional
        Neighborhood size used only for diffusion smoothing when
        `t != 0` or `t="auto"`. If omitted, defaults to
        `ceil(sqrt(n_samples))` for the input point cloud.
    precision : float, optional (default: 1.0)
        Controls filter quantization. 1.0 = no quantization,
        0.1 = 10% of unique levels
    t : int or "auto", optional (default: 0)
        Diffusion smoothing time applied to the point cloud before graph
        construction. `0` disables smoothing. When `"auto"`, select a
        diffusion time from the Von Neumann entropy elbow of the kNN
        diffusion operator.
    t_max : int, optional (default: 100)
        Maximum time tested by the entropy-knee heuristic when `t="auto"`.
    diffusion_eigen_index : int, optional (default: 1)
        One-based index of the nontrivial diffusion eigenfunction to use
        per connected component. `1` means the first nontrivial
        diffusion eigenfunction, `2` the second, and so on. Ignored when
        `filter_values` is provided.
    filter_method : {"diffusion_eigenfunction", "rooted_potential_distance",
                     "rooted_diffusion_shortest_path"}, optional
        Scalar filter construction method. The default uses a single
        nontrivial diffusion eigenfunction. The rooted potential-distance
        option uses a PHATE-style potential distance from an automatically
        selected root in each connected component. The rooted diffusion
        shortest-path option uses Dijkstra distance from an automatically
        selected root on the diffusion cost graph built directly from `P`.
        Ignored when `filter_values` is provided.
    diffusion_time : {"auto"} or int, optional (default: "auto")
        Diffusion time for `filter_method="rooted_potential_distance"`.
        Ignored for `diffusion_eigenfunction`,
        `rooted_diffusion_shortest_path`, and when `filter_values` is
        provided.
    diffusion_time_max : int, optional (default: 40)
        Maximum time tested by the entropy-knee heuristic when
        `diffusion_time="auto"` and
        `filter_method="rooted_potential_distance"`. Ignored for
        `rooted_diffusion_shortest_path` and when `filter_values` is
        provided.
    simplify : bool, optional (default: True)
        If True, simplify the Reeb graph by contracting degree-2 chains.
    return_raw : bool, optional (default: False)
        If True, include the raw Reeb graph in the returned result.
    return_edge_lengths : bool, optional (default: False)
        If True, compute and return edge lengths in filter space for
        whichever graph outputs are returned.
    return_simp_persistence : bool, optional (default: False)
        If True, compute and return an edge-length persistence summary
        for the simplified graph.
    return_raw_persistence : bool, optional (default: False)
        If True, compute and return an edge-length persistence summary
        for the raw Reeb graph.
    return_point_assignment : bool, optional (default: False)
        If True, assign points to nodes by filter-distance. When
        simplify=True, assigns to simplified nodes; otherwise assigns
        to raw nodes.
    return_edge_assignment : bool, optional (default: False)
        If True, assign points to raw and/or simplified edges using
        adjacent-slice bridging regions.
    return_cellular_decomposition : bool, optional (default: False)
        If True and simplify=True, return a mixed disjoint partition of
        all points onto simplified node cells and simplified edge cells.
    return_intermediates : bool, optional (default: False)
        If True, include intermediate matrices and arrays used during
        construction.

    Returns
    -------
    dict
        Structured result with keys:

        - primary_graph : "simplified" or "raw"
        - simplified    : simplified graph section, when requested/primary
        - raw           : raw graph section, when requested/primary
        - intermediates : intermediate construction outputs, when requested
    """
    if return_cellular_decomposition and not simplify:
        raise ValueError(
            "return_cellular_decomposition=True requires simplify=True."
        )

    if (X is None) == (W is None):
        raise ValueError("Provide exactly one of X or W.")

    W_initial = None
    P_initial = None

    if W is None:
        if sp.isspmatrix(X):
            X = X.toarray()
        X = np.asarray(X, dtype=float)
        if X.ndim != 2:
            raise ValueError("X must be a 2D array-like point cloud.")

        smoothing_k = k_smooth
        if t == "auto":
            if int(t_max) < 3:
                raise ValueError("t_max must be >= 3 when t='auto'.")
            if smoothing_k is None:
                smoothing_k = int(np.ceil(np.sqrt(X.shape[0])))
            smoothing_k = int(max(1, smoothing_k))
            W_initial = build_affinity_matrix(X, k=smoothing_k)
            P_initial = build_diffusion_operator(W_initial)
            t_resolved = _select_diffusion_time(
                P_initial.toarray(),
                diffusion_time="auto",
                diffusion_time_max=int(t_max),
            )
        else:
            t_resolved = int(t)
            if t_resolved < 0:
                raise ValueError("t must be >= 0 or 'auto'.")
            if t_resolved > 0:
                if smoothing_k is None:
                    smoothing_k = int(np.ceil(np.sqrt(X.shape[0])))
                smoothing_k = int(max(1, smoothing_k))
                W_initial = build_affinity_matrix(X, k=smoothing_k)
            else:
                W_initial = None
            P_initial = build_diffusion_operator(W_initial) if W_initial is not None else None

        if t_resolved > 0:
            X_smoothed = X.copy()
            for _ in range(int(t_resolved)):
                X_smoothed = P_initial @ X_smoothed
            X_smoothed = np.asarray(X_smoothed, dtype=float)
            W = build_affinity_matrix(X_smoothed, k=k)
            smoothing_applied = True
        else:
            X_smoothed = X.copy()
            W = build_affinity_matrix(X, k=k)
            smoothing_applied = False
        num_points = int(X.shape[0])
    else:
        W = validate_affinity_matrix(W)
        num_points = int(W.shape[0])
        if t == "auto":
            raise ValueError("t='auto' requires X so diffusion smoothing can be applied to the point cloud.")
        t_resolved = int(t)
        if t_resolved != 0:
            raise ValueError("t != 0 is only supported when X is provided.")
        X_smoothed = None
        smoothing_applied = False

    if filter_values is None:
        (
            filter_values,
            components,
            filter_aux_values,
            filter_metadata,
        ) = compute_diffusion_filter(
            W,
            diffusion_eigen_index=diffusion_eigen_index,
            precision=precision,
            filter_method=filter_method,
            diffusion_time=diffusion_time,
            diffusion_time_max=diffusion_time_max,
            return_metadata=True,
        )
        filter_method_used = filter_method
    else:
        filter_values = np.asarray(filter_values, dtype=float)
        if filter_values.ndim != 1 or filter_values.shape[0] != num_points:
            raise ValueError(
                "filter_values must be a 1D array with length equal to the number "
                "of graph vertices."
            )
        if not np.all(np.isfinite(filter_values)):
            raise ValueError("filter_values must contain only finite values.")

        filter_values = _quantize_filter_values(filter_values, precision)
        A = ((W + W.T) > 0).astype(np.int8).tocsr()
        A.setdiag(0)
        A.eliminate_zeros()
        ncomp, comp_labels = connected_components(A, directed=False)
        components = [np.where(comp_labels == c)[0] for c in range(ncomp)]
        filter_aux_values = np.full(len(components), np.nan, dtype=float)
        filter_metadata = {
            "filter_method": "custom",
            "component_root_indices": np.full(len(components), -1, dtype=int),
            "component_root_pairs": np.full((len(components), 2), -1, dtype=int),
        }
        filter_method_used = "custom"

    prep_state = prepare_reeb(W, filter_values)
    reeb_nodes, reeb_edges, step_vertices, step_comp_ids = build_reeb_graph(prep_state)
    t_vals = prep_state["t_vals"]

    result = {
        "primary_graph": "simplified" if simplify else "raw",
    }

    raw_section = None
    simp_section = None
    raw_edge_lengths = None
    raw_point_edges = None
    raw_edge_points = None

    if simplify:
        if return_edge_assignment or return_point_assignment or return_cellular_decomposition:
            (
                simp_edges,
                keep_ids,
                beta1,
                comp_count,
                simp_edge_paths,
                simp_node_paths,
            ) = simplify_reeb_graph(
                reeb_nodes, reeb_edges, return_paths=True
            )
        else:
            simp_edges, keep_ids, beta1, comp_count = simplify_reeb_graph(reeb_nodes, reeb_edges)
        simp_nodes = [reeb_nodes[int(i)] for i in keep_ids]

        simp_section = {
            "nodes": simp_nodes,
            "edges": simp_edges,
            "keep_ids": keep_ids,
            "beta1": beta1,
            "comp_count": comp_count,
        }

        if return_edge_lengths or return_simp_persistence:
            simp_edge_lengths = compute_edge_lengths(simp_nodes, simp_edges, t_vals)

        if return_edge_lengths:
            simp_section["edge_lengths"] = simp_edge_lengths

        if return_simp_persistence:
            simp_section["persistence"] = compute_graph_persistence(
                num_nodes=len(simp_nodes),
                edges=simp_edges,
                edge_lengths=simp_edge_lengths,
            )

        if return_point_assignment:
            point_assignment, node_points, node_support_points = assign_points_to_simplified_nodes(
                W=W,
                reeb_nodes=reeb_nodes,
                keep_ids=keep_ids,
                simp_node_paths=simp_node_paths,
                step_vertices=step_vertices,
                step_comp_ids=step_comp_ids,
                uniq_v=prep_state["uniq_v"],
            )
            simp_section["point_assignment"] = point_assignment
            simp_section["node_points"] = node_points
            simp_section["node_support_points"] = node_support_points

        if return_edge_assignment:
            raw_point_edges, raw_edge_points = assign_points_to_raw_edges(
                W=W,
                reeb_nodes=reeb_nodes,
                reeb_edges=reeb_edges,
                step_vertices=step_vertices,
                step_comp_ids=step_comp_ids,
                uniq_v=prep_state["uniq_v"],
                level_of=prep_state["level_of"],
            )
            (
                simp_point_edge_assignment,
                simp_edge_points,
                simp_point_edges,
                simp_edge_support_points,
            ) = assign_points_to_simplified_edges(
                W=W,
                reeb_nodes=reeb_nodes,
                keep_ids=keep_ids,
                simp_edges=simp_edges,
                simp_edge_paths=simp_edge_paths,
                simp_node_paths=simp_node_paths,
                raw_edge_points=raw_edge_points,
                step_vertices=step_vertices,
                step_comp_ids=step_comp_ids,
                uniq_v=prep_state["uniq_v"],
                num_points=num_points,
            )
            simp_section["point_edge_assignment"] = simp_point_edge_assignment
            simp_section["point_edges"] = simp_point_edges
            simp_section["edge_points"] = simp_edge_points
            simp_section["edge_support_points"] = simp_edge_support_points
            if raw_section is None:
                raw_section = {
                    "nodes": reeb_nodes,
                    "edges": reeb_edges,
                }
            else:
                raw_section.setdefault("nodes", reeb_nodes)
                raw_section.setdefault("edges", reeb_edges)
            raw_section["point_edges"] = raw_point_edges
            raw_section["edge_points"] = raw_edge_points

        if return_cellular_decomposition:
            if "node_support_points" not in simp_section:
                point_assignment, node_points, node_support_points = assign_points_to_simplified_nodes(
                    W=W,
                    reeb_nodes=reeb_nodes,
                    keep_ids=keep_ids,
                    simp_node_paths=simp_node_paths,
                    step_vertices=step_vertices,
                    step_comp_ids=step_comp_ids,
                    uniq_v=prep_state["uniq_v"],
                )
                simp_section["point_assignment"] = point_assignment
                simp_section["node_points"] = node_points
                simp_section["node_support_points"] = node_support_points

            if "edge_support_points" not in simp_section:
                raw_point_edges, raw_edge_points = assign_points_to_raw_edges(
                    W=W,
                    reeb_nodes=reeb_nodes,
                    reeb_edges=reeb_edges,
                    step_vertices=step_vertices,
                    step_comp_ids=step_comp_ids,
                    uniq_v=prep_state["uniq_v"],
                    level_of=prep_state["level_of"],
                )
                (
                    simp_point_edge_assignment,
                    simp_edge_points,
                    simp_point_edges,
                    simp_edge_support_points,
                ) = assign_points_to_simplified_edges(
                    W=W,
                    reeb_nodes=reeb_nodes,
                    keep_ids=keep_ids,
                    simp_edges=simp_edges,
                    simp_edge_paths=simp_edge_paths,
                    simp_node_paths=simp_node_paths,
                    raw_edge_points=raw_edge_points,
                    step_vertices=step_vertices,
                    step_comp_ids=step_comp_ids,
                    uniq_v=prep_state["uniq_v"],
                    num_points=num_points,
                )
                simp_section["point_edge_assignment"] = simp_point_edge_assignment
                simp_section["point_edges"] = simp_point_edges
                simp_section["edge_points"] = simp_edge_points
                simp_section["edge_support_points"] = simp_edge_support_points

            (
                cell_assignment_kind,
                cell_assignment_id,
                node_cells,
                edge_cells,
            ) = build_simplified_cellular_decomposition(
                W=W,
                node_support_points=simp_section["node_support_points"],
                edge_support_points=simp_section["edge_support_points"],
            )
            simp_section["cell_assignment_kind"] = cell_assignment_kind
            simp_section["cell_assignment_id"] = cell_assignment_id
            simp_section["node_cells"] = node_cells
            simp_section["edge_cells"] = edge_cells

        if return_raw_persistence:
            raw_edge_lengths = compute_edge_lengths(reeb_nodes, reeb_edges, t_vals)
            if raw_section is None:
                raw_section = {}
            raw_section["persistence"] = compute_graph_persistence(
                num_nodes=len(reeb_nodes),
                edges=reeb_edges,
                edge_lengths=raw_edge_lengths,
            )
    else:
        raw_section = {
            "nodes": reeb_nodes,
            "edges": reeb_edges,
        }

        if return_edge_lengths or return_raw_persistence:
            raw_edge_lengths = compute_edge_lengths(reeb_nodes, reeb_edges, t_vals)

        if return_edge_lengths:
            raw_section["edge_lengths"] = raw_edge_lengths

        if return_raw_persistence:
            raw_section["persistence"] = compute_graph_persistence(
                num_nodes=len(reeb_nodes),
                edges=reeb_edges,
                edge_lengths=raw_edge_lengths,
            )

        if return_point_assignment:
            point_assignment, node_points, node_support_points = assign_points_to_raw_nodes(
                reeb_nodes=reeb_nodes,
                step_vertices=step_vertices,
                step_comp_ids=step_comp_ids,
                uniq_v=prep_state["uniq_v"],
                filter_values=filter_values,
                t_vals=prep_state["t_vals"],
            )
            raw_section["point_assignment"] = point_assignment
            raw_section["node_points"] = node_points
            raw_section["node_support_points"] = node_support_points

        if return_edge_assignment:
            raw_point_edges, raw_edge_points = assign_points_to_raw_edges(
                W=W,
                reeb_nodes=reeb_nodes,
                reeb_edges=reeb_edges,
                step_vertices=step_vertices,
                step_comp_ids=step_comp_ids,
                uniq_v=prep_state["uniq_v"],
                level_of=prep_state["level_of"],
            )
            raw_section["point_edges"] = raw_point_edges
            raw_section["edge_points"] = raw_edge_points

    if simplify and return_raw:
        if raw_section is None:
            raw_section = {
                "nodes": reeb_nodes,
                "edges": reeb_edges,
            }
        else:
            raw_section.setdefault("nodes", reeb_nodes)
            raw_section.setdefault("edges", reeb_edges)

        if return_edge_lengths:
            if "edge_lengths" not in raw_section:
                if raw_edge_lengths is None:
                    raw_edge_lengths = compute_edge_lengths(reeb_nodes, reeb_edges, t_vals)
                raw_section["edge_lengths"] = raw_edge_lengths

        if return_edge_assignment:
            if raw_point_edges is None or raw_edge_points is None:
                raw_point_edges, raw_edge_points = assign_points_to_raw_edges(
                    W=W,
                    reeb_nodes=reeb_nodes,
                    reeb_edges=reeb_edges,
                    step_vertices=step_vertices,
                    step_comp_ids=step_comp_ids,
                    uniq_v=prep_state["uniq_v"],
                    level_of=prep_state["level_of"],
                )
            raw_section["point_edges"] = raw_point_edges
            raw_section["edge_points"] = raw_edge_points

    if simp_section is not None:
        result["simplified"] = simp_section
    if raw_section is not None:
        result["raw"] = raw_section

    if return_intermediates:
        intermediates = {
            "W": W,
            "components": components,
            "filter_method": filter_method_used,
            "diffusion_eigen_index": int(diffusion_eigen_index),
            "filter_aux_values": filter_aux_values,
            "filter_metadata": filter_metadata,
            "filter_values": filter_values,
            "prep_state": prep_state,
            "step_vertices": step_vertices,
            "step_comp_ids": step_comp_ids,
            "smoothing_t": int(t_resolved),
            "smoothing_t_requested": t,
            "smoothing_k": int(smoothing_k) if W_initial is not None else None,
            "smoothing_applied": bool(smoothing_applied),
        }
        if X_smoothed is not None:
            intermediates["X_smoothed"] = X_smoothed
        if W_initial is not None:
            intermediates["W_initial"] = W_initial
            intermediates["P_initial"] = P_initial
        if filter_method_used == "diffusion_eigenfunction":
            intermediates["diffusion_eigenvalues"] = filter_aux_values
        result["intermediates"] = intermediates

    return result
