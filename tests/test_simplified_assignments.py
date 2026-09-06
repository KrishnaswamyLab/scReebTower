import numpy as np

from sc_reeb_tower import scReebTower, extract_cellular_trajectory, build_affinity_matrix
from sc_reeb_tower.reeb import _build_reeb_graph, build_reeb_graph, prepare_reeb
from sc_reeb_tower.simplify import simplify_reeb_graph
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


def test_raw_reeb_graph_retains_isolated_slice_components():
    step_vertices = [
        np.array([0], dtype=np.int32),
        np.array([1], dtype=np.int32),
    ]
    step_comp_ids = [
        np.array([0], dtype=np.int32),
        np.array([0], dtype=np.int32),
    ]

    nodes, edges = _build_reeb_graph(2, 2, step_vertices, step_comp_ids)

    assert [(node["step"], node["comp"]) for node in nodes] == [(0, 0), (1, 0)]
    assert edges == []


def test_support_induced_slices_connect_four_neighbor_grid_levels():
    side = 7
    rows = []
    cols = []
    for row in range(side):
        for col in range(side):
            u = row * side + col
            if col + 1 < side:
                v = u + 1
                rows.extend((u, v))
                cols.extend((v, u))
            if row + 1 < side:
                v = u + side
                rows.extend((u, v))
                cols.extend((v, u))

    adjacency = sp.csr_matrix(
        (np.ones(len(rows)), (rows, cols)),
        shape=(side * side, side * side),
    )
    filter_values = np.repeat(np.arange(side, dtype=float), side)

    prep = prepare_reeb(adjacency, filter_values)
    nodes, edges, _, component_ids = build_reeb_graph(prep)
    simplified_edges, keep_ids, beta1, component_count = simplify_reeb_graph(
        nodes, edges
    )

    assert all(np.unique(ids).size == 1 for ids in component_ids)
    assert len(nodes) == side - 1
    assert len(edges) == side - 2
    assert keep_ids.size == 2
    assert simplified_edges == [(0, 1)]
    assert component_count == 1
    assert beta1 == 0


def test_interval_sweep_matches_naive_support_induced_components():
    rng = np.random.default_rng(7)
    vertex_count = 18
    upper = rng.random((vertex_count, vertex_count)) < 0.16
    upper = np.triu(upper, k=1)
    upper[np.arange(vertex_count - 1), np.arange(1, vertex_count)] = True
    adjacency = sp.csr_matrix(upper | upper.T, dtype=float)
    filter_values = rng.permutation(vertex_count).astype(float)

    prep = prepare_reeb(adjacency, filter_values)
    _, _, step_vertices, step_comp_ids = build_reeb_graph(prep)
    support_graph = sp.csr_matrix(
        (
            np.ones(2 * prep["base_ei_c"].size),
            (
                np.concatenate((prep["base_ei_c"], prep["base_ej_c"])),
                np.concatenate((prep["base_ej_c"], prep["base_ei_c"])),
            ),
        ),
        shape=(prep["M"], prep["M"]),
    )

    for vertices, component_ids in zip(step_vertices, step_comp_ids):
        _, expected_ids = sp.csgraph.connected_components(
            support_graph[vertices][:, vertices], directed=False
        )
        expected_same = expected_ids[:, None] == expected_ids[None, :]
        actual_same = component_ids[:, None] == component_ids[None, :]
        assert np.array_equal(actual_same, expected_same)


def test_simplified_node_and_edge_assignments_cover_dataset():
    X = sample_line()
    result = scReebTower(
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
    result = scReebTower(
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
    result = scReebTower(
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

    result = scReebTower(
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


def test_scReebTower_requires_exactly_one_of_x_or_w():
    X = sample_line()
    W = build_affinity_matrix(X, k=8)

    try:
        scReebTower()
        assert False, "expected ValueError when neither X nor W is provided"
    except ValueError as exc:
        assert "exactly one of X or W" in str(exc)

    try:
        scReebTower(X=X, W=W)
        assert False, "expected ValueError when both X and W are provided"
    except ValueError as exc:
        assert "exactly one of X or W" in str(exc)


def test_cycle_with_stick_graph_simplifies_without_self_loops():
    W, _ = sample_cycle_with_stick_graph()
    result = scReebTower(W=W, return_raw=True, return_intermediates=True)

    simplified = result["simplified"]
    edges = simplified["edges"]

    assert len(edges) >= 3
    assert simplified["beta1"] == 1
    assert all(int(u) != int(v) for u, v in edges)


def test_custom_filter_values_run_through_main_api():
    W, _ = sample_cycle_with_stick_graph()
    n = W.shape[0]
    custom_filter = np.linspace(0.0, 1.0, n)

    result = scReebTower(
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


def test_diffusion_smoothing_t_zero_is_a_noop():
    X = sample_line()
    expected_W = build_affinity_matrix(X, k=8)

    result = scReebTower(
        X,
        k=8,
        t=0,
        return_intermediates=True,
    )

    intermediates = result["intermediates"]

    assert intermediates["smoothing_t"] == 0
    assert intermediates["smoothing_applied"] is False
    assert intermediates["smoothing_k"] is None
    assert np.allclose(intermediates["X_smoothed"], X)
    assert (intermediates["W"] != expected_W).nnz == 0


def test_diffusion_smoothing_auto_rebuilds_affinity_from_smoothed_points():
    X = sample_line()

    result = scReebTower(
        X,
        k=8,
        t="auto",
        return_intermediates=True,
    )

    intermediates = result["intermediates"]
    rebuilt_W = build_affinity_matrix(intermediates["X_smoothed"], k=8)
    expected_k_smooth = int(np.ceil(np.sqrt(X.shape[0])))

    assert 1 <= intermediates["smoothing_t"] <= 100
    assert intermediates["smoothing_applied"] is True
    assert intermediates["smoothing_k"] == expected_k_smooth
    assert not np.allclose(intermediates["X_smoothed"], X)
    assert (intermediates["W"] != rebuilt_W).nnz == 0


def test_diffusion_smoothing_accepts_explicit_k_smooth():
    X = sample_line()

    result = scReebTower(
        X,
        k=8,
        k_smooth=12,
        t=1,
        return_intermediates=True,
    )

    intermediates = result["intermediates"]

    assert intermediates["smoothing_k"] == 12
    assert intermediates["smoothing_t"] == 1
    assert intermediates["smoothing_applied"] is True


def test_diffusion_smoothing_is_rejected_for_precomputed_affinity():
    W, _ = sample_cycle_with_stick_graph()

    try:
        scReebTower(W=W, t=1)
        assert False, "expected ValueError when t>0 is used with W"
    except ValueError as exc:
        assert "only supported when X is provided" in str(exc)

    try:
        scReebTower(W=W, t="auto")
        assert False, "expected ValueError when t='auto' is used with W"
    except ValueError as exc:
        assert "requires X" in str(exc)
