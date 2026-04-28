import numpy as np

from dreeb import dreeb, extract_cellular_trajectory, build_affinity_matrix
import scipy.sparse as sp


def sample_line(n=41):
    x = np.linspace(0.0, 1.0, n)
    return np.column_stack([x, np.zeros_like(x)])


def sample_cycle_with_stick_graph(cycle_nodes=18, stick_nodes=8):
    theta = np.linspace(0.0, 2.0 * np.pi, cycle_nodes, endpoint=False)
    cycle_pts = np.column_stack([np.cos(theta), np.sin(theta)])
    stick_pts = np.array(
        [[1.0 + 0.2 * i, 0.0] for i in range(1, stick_nodes + 1)],
        dtype=float,
    )
    pts = np.vstack([cycle_pts, stick_pts])

    edges = []
    for i in range(cycle_nodes):
        edges.append((i, (i + 1) % cycle_nodes))

    prev = 0
    for j in range(stick_nodes):
        curr = cycle_nodes + j
        edges.append((prev, curr))
        prev = curr

    rows = []
    cols = []
    data = []
    for u, v in edges:
        rows.extend([u, v])
        cols.extend([v, u])
        data.extend([1.0, 1.0])

    n = pts.shape[0]
    W = sp.csr_matrix((data, (rows, cols)), shape=(n, n))
    return W, pts


def test_simplified_node_and_edge_assignments_cover_dataset():
    X = sample_line()
    result = dreeb(
        X,
        k=8,
        simplify=True,
        return_point_assignment=True,
        return_edge_assignment=True,
        return_cellular_decomposition=True,
    )

    simplified = result["simplified"]
    num_points = X.shape[0]

    assert simplified["point_assignment"].shape == (num_points,)
    assert simplified["point_edge_assignment"].shape == (num_points,)
    assert len(simplified["node_points"]) == len(simplified["nodes"])
    assert len(simplified["node_support_points"]) == len(simplified["nodes"])
    assert len(simplified["edge_points"]) == len(simplified["edges"])
    assert len(simplified["edge_support_points"]) == len(simplified["edges"])
    assert len(simplified["point_edges"]) == num_points
    assert simplified["cell_assignment_kind"].shape == (num_points,)
    assert simplified["cell_assignment_id"].shape == (num_points,)
    assert len(simplified["node_cells"]) == len(simplified["nodes"])
    assert len(simplified["edge_cells"]) == len(simplified["edges"])

    node_owned = np.concatenate(simplified["node_points"])
    edge_owned = np.concatenate(simplified["edge_points"])

    assert np.array_equal(np.sort(node_owned), np.arange(num_points))
    assert np.array_equal(np.sort(edge_owned), np.arange(num_points))
    cell_owned = np.concatenate(simplified["node_cells"] + simplified["edge_cells"])
    assert np.array_equal(np.sort(cell_owned), np.arange(num_points))

    extracted = extract_cellular_trajectory(simplified, [0, len(simplified["nodes"])])
    expected = np.unique(
        np.concatenate([simplified["node_cells"][0], simplified["edge_cells"][0]])
    )
    assert np.array_equal(extracted, expected)
    assert np.array_equal(
        np.sort(simplified["point_assignment"]),
        np.repeat(np.arange(len(simplified["nodes"])), [len(x) for x in simplified["node_points"]]),
    )
    assert np.array_equal(
        np.sort(simplified["point_edge_assignment"]),
        np.repeat(np.arange(len(simplified["edges"])), [len(x) for x in simplified["edge_points"]]),
    )


def test_rooted_potential_distance_filter_runs_through_main_api():
    X = sample_line()
    result = dreeb(
        X,
        k=8,
        filter_method="rooted_potential_distance",
        return_intermediates=True,
    )

    simplified = result["simplified"]
    intermediates = result["intermediates"]

    assert result["primary_graph"] == "simplified"
    assert len(simplified["nodes"]) >= 1
    assert len(simplified["edges"]) >= 0
    assert intermediates["filter_method"] == "rooted_potential_distance"
    assert "diffusion_eigenvalues" not in intermediates
    assert intermediates["filter_values"].shape == (X.shape[0],)

    filter_metadata = intermediates["filter_metadata"]
    assert filter_metadata["filter_method"] == "rooted_potential_distance"
    assert filter_metadata["component_root_indices"].shape[0] == len(intermediates["components"])
    assert filter_metadata["component_root_pairs"].shape == (len(intermediates["components"]), 2)


def test_rooted_diffusion_shortest_path_filter_runs_through_main_api():
    X = sample_line()
    result = dreeb(
        X,
        k=8,
        filter_method="rooted_diffusion_shortest_path",
        return_intermediates=True,
    )

    simplified = result["simplified"]
    intermediates = result["intermediates"]

    assert result["primary_graph"] == "simplified"
    assert len(simplified["nodes"]) >= 1
    assert len(simplified["edges"]) >= 0
    assert intermediates["filter_method"] == "rooted_diffusion_shortest_path"
    assert "diffusion_eigenvalues" not in intermediates
    assert intermediates["filter_values"].shape == (X.shape[0],)

    filter_metadata = intermediates["filter_metadata"]
    assert filter_metadata["filter_method"] == "rooted_diffusion_shortest_path"
    assert filter_metadata["component_root_indices"].shape[0] == len(intermediates["components"])
    assert filter_metadata["component_root_pairs"].shape == (len(intermediates["components"]), 2)


def test_precomputed_affinity_matrix_runs_through_main_api():
    X = sample_line()
    W = build_affinity_matrix(X, k=8)

    result = dreeb(
        W=W,
        simplify=True,
        return_raw=True,
        return_intermediates=True,
    )

    assert result["primary_graph"] == "simplified"
    assert len(result["simplified"]["nodes"]) >= 1
    assert len(result["raw"]["nodes"]) >= len(result["simplified"]["nodes"])
    assert result["intermediates"]["W"].shape == (X.shape[0], X.shape[0])
    assert result["intermediates"]["filter_values"].shape == (X.shape[0],)


def test_dreeb_requires_exactly_one_of_x_or_w():
    X = sample_line()
    W = build_affinity_matrix(X, k=8)

    try:
        dreeb()
        assert False, "expected ValueError when neither X nor W is provided"
    except ValueError as exc:
        assert "exactly one of X or W" in str(exc)

    try:
        dreeb(X=X, W=W)
        assert False, "expected ValueError when both X and W are provided"
    except ValueError as exc:
        assert "exactly one of X or W" in str(exc)


def test_cycle_with_stick_graph_simplifies_without_self_loops():
    W, _ = sample_cycle_with_stick_graph()
    result = dreeb(W=W, return_raw=True, return_intermediates=True)

    simplified = result["simplified"]
    edges = simplified["edges"]

    assert len(edges) >= 3
    assert simplified["beta1"] == 1
    assert all(int(u) != int(v) for u, v in edges)


def test_custom_filter_values_run_through_main_api():
    W, _ = sample_cycle_with_stick_graph()
    n = W.shape[0]
    custom_filter = np.linspace(0.0, 1.0, n)

    result = dreeb(
        W=W,
        filter_values=custom_filter,
        return_raw=True,
        return_intermediates=True,
    )

    intermediates = result["intermediates"]
    assert result["primary_graph"] == "simplified"
    assert intermediates["filter_method"] == "custom"
    assert intermediates["filter_metadata"]["filter_method"] == "custom"
    assert intermediates["filter_values"].shape == (n,)
    assert np.allclose(intermediates["filter_values"], custom_filter)
    assert "diffusion_eigenvalues" not in intermediates
