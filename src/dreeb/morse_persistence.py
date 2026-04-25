import numpy as np

def compute_morse_persistence(nodes, edges, t_vals):
    """
    Compute persistence via a Morse function sweep on a Reeb graph.

    Parameters
    ----------
    nodes : list of dict
        Each node must have key 'step' — index into t_vals giving
        the filter value at which this node enters the filtration.
    edges : list of tuple
        Edge list as (u, v) pairs.
    t_vals : np.ndarray
        Filter values (diffusion geodesic distances) at each step.
        
    Returns
    -------
    dict
        h0         : finite H0 pairs [birth, death]
        h0_essential : essential H0 pairs (last surviving component)
        h1         : H1 pairs [birth, inf] (cycles)
    """
    n = len(nodes)
    
    node_steps = np.array([node["step"] for node in nodes], dtype=int)
    node_filter_vals = t_vals[node_steps]       

    # Edge filter value = max of its two endpoint filter values
    edge_filter_vals = []
    for u, v in edges:
        fu = node_filter_vals[int(u)]
        fv = node_filter_vals[int(v)]
        edge_filter_vals.append(max(fu, fv))
    edge_filter_vals = np.array(edge_filter_vals, dtype=float)

    events = []
    for i in range(n):
        events.append((node_filter_vals[i], 0, 'node', i))   
    for i, fval in enumerate(edge_filter_vals):
        events.append((fval, 1, 'edge', i))                  

    events.sort(key=lambda e: (e[0], e[1]))

    parent = np.arange(n, dtype=int)
    size   = np.ones(n, dtype=int)
    birth  = np.full(n, np.inf)     
    active_nodes = np.zeros(n, dtype=bool)  

    def find(x):
        while parent[x] != x:
            parent[x] = parent[parent[x]]
            x = parent[x]
        return x

    h0 = []
    h1 = []

    for event in events:
        fval, _, kind, idx = event

        if kind == 'node':
            active_nodes[idx] = True
            birth[idx] = fval      

        elif kind == 'edge':
            u, v = edges[idx]
            u, v = int(u), int(v)

            if not (active_nodes[u] and active_nodes[v]):
                continue

            #Self loop
            if u == v:
                h1.append((fval, np.inf))
                continue

            ru = find(u)
            rv = find(v)

            #Merge connected components - dying root has a lower morse function value
            if ru != rv:
                birth_ru = birth[ru]
                birth_rv = birth[rv]

                if birth_ru >= birth_rv:
                    dying_root   = ru
                    surviving_root = rv
                else:
                    dying_root   = rv
                    surviving_root = ru

                h0.append((birth[dying_root], fval))

                parent[dying_root] = surviving_root
                size[surviving_root] += size[dying_root]
                birth[surviving_root] = min(birth[ru], birth[rv])

            else:
                h1.append((fval, np.inf))

    roots = {find(i) for i in range(n) if active_nodes[i]}
    h0_essential = np.array([(birth[r], np.inf) for r in roots], dtype=float)

    return {
        "h0":          np.array(h0, dtype=float).reshape(-1, 2),
        "h0_essential": h0_essential.reshape(-1, 2),
        "h1":          np.array(h1, dtype=float).reshape(-1, 2),
    }