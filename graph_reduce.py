import networkx as nx
from matplotlib import pyplot as plt
import networkx.algorithms.isomorphism as iso
import itertools

SP_TEMPLATE_GRAPH = (
    None  # Placeholder for the SP kernel template graph, to be defined later.
)
SP_TEMPLATE_GRAPH = nx.Graph()  # Initialize the graph for the SP kernel template.
SP_TEMPLATE_GRAPH.add_edges_from(
    [("v1", "v2"), ("v2", "v3"), ("v3", "v4"), ("v4", "v1")]
)  # Example edges for the SP template.

NSP_TEMPLATE_GRAPH = (
    None  # Placeholder for the NSP kernel template graph, to be defined later.
)
NSP_TEMPLATE_GRAPH = nx.Graph()  # Initialize the graph for the NSP kernel template.
NSP_TEMPLATE_GRAPH.add_edges_from(
    [("v1", "v2"), ("v2", "v3"), ("v3", "v4"), ("v4", "v1"), ("v2", "v4")]
)  # Example edges for the NSP template.

SORT_CUBE = lambda x: (x.replace("!", ""), not x.startswith("!"))
GRAPH_ID = 0

class Cube(set):
    """A custom set class for representing cubes that prints in sorted order"""

    def __str__(self):
        return str(sorted(list(self), key=SORT_CUBE))

    def __repr__(self):
        return str(self)


class TransistorGraph:
    def __init__(self, F_str):
        self.F_str = F_str
        self.cubes = self.parse_function(F_str)
        self.cube_id_to_cubes = {}
        self.graph, edges, incident_literals = self.construct_graph(self.cubes)
        print(f"edges: {len(edges)}")
        # Extract all literals from all cubes into a single set
        self.all_literals = set()
        for _, node_data in self.graph.nodes(data=True):
            self.all_literals.update(node_data["cube"])
        # self.plot_graph(edges)  # TODO: idont like this needs input
        print(f"All unique literals: {self.all_literals}")
        graphs = self.kernel_identification()
        self.network_composition(graphs)

    def is_complete(self, G):
        n = G.order()
        return n * (n - 1) / 2 == G.size()

    def get_unique_mappings(self, mappings, graphs=None):
        """
        Get unique mappings from a list of mappings.
        Args:
            mappings (list): A list of mappings to filter.
            graphs (list): A list of graphs corresponding to the mappings.
        Returns:
            list: A list of unique mappings
        """
        seen = set()
        unique = []
        if graphs:
            unique_graphs = []
            # remove mappings with their corresponding graphs
            for m, g in zip(mappings, graphs):
                # Convert the dictionary to a frozenset of (key, value) pairs,
                # which is hashable and ignores the order of the items.
                key = frozenset(m.items())
                if key not in seen:
                    seen.add(key)
                    unique.append(m)
                    unique_graphs.append(g)
            return unique, unique_graphs
        else:
            for m in mappings:
                # Convert the dictionary to a frozenset of (key, value) pairs,
                # which is hashable and ignores the order of the items. 
                key = frozenset(m.items())
                if key not in seen:
                    seen.add(key)
                    unique.append(m)
            return unique

    def graph_equal(self, G1, G2):
        """
        Check if two graphs are equal.
        """
        # Check if they have the same number of nodes and edges
        if G1.number_of_nodes() != G2.number_of_nodes():
            return False
        if G1.number_of_edges() != G2.number_of_edges():
            return False
        try:
            # if there exisit cubes in node data, then check if the cubes are equal
            set_of_cubes_1 = set(frozenset(G1.nodes[n]["cube"]) for n in G1.nodes)
            set_of_cubes_2 = set(frozenset(G2.nodes[n]["cube"]) for n in G2.nodes)
            if set_of_cubes_1 != set_of_cubes_2:
                return False
        except KeyError:
            pass
        try:
            # Check if the transistor nodes are equal
            set_of_transistors_net_1 = set(
                frozenset(G1.nodes[n]["net"])
                for n in [n for n in G1.nodes if G1.nodes[n]["type"] == "transistor"]
            )
            set_of_transistors_net_2 = set(
                frozenset(G2.nodes[n]["net"])
                for n in [n for n in G2.nodes if G2.nodes[n]["type"] == "transistor"]
            )
            if set_of_transistors_net_1 != set_of_transistors_net_2:
                return False
        except KeyError:
            pass
        return True

    def transistor_graph_has_new_nets(self, G1, G2):
        """
        In two transistor graphs, check if there are any new nets in G2 that are not present in G1.
        """
        tran_1 = [n for n in G1.nodes if G1.nodes[n]["type"] == "transistor"]
        tran_2 = [n for n in G2.nodes if G2.nodes[n]["type"] == "transistor"]
        nets_1 = set(G1.nodes[n]["net"] for n in tran_1)
        nets_2 = set(G2.nodes[n]["net"] for n in tran_2)
        # Check if there are any new nets in G2 that are not in G1
        new_nets = nets_2 - nets_1
        if new_nets:
            print(f"New nets in G2: {new_nets}")
            return True
        else:
            print("No new nets in G2")
            return False

    def get_transistor_net_paths(self, G, source, target):
        """
        Get all paths from source to target in the graph.
        """
        simple_paths = nx.all_simple_paths(G, source=source, target=target)
        net_paths = []
        transistor_paths = []
        for path in simple_paths:
            tmp_net_path = []
            tmp_path = []
            tmp_net_path.append(path[0])  # add the source node
            # if path has a transistor node, extract the transistor net
            for node in path:
                if G.nodes[node]["type"] == "transistor":
                    net = G.nodes[node]["net"]
                    tmp_net_path.append(net)
                    tmp_path.append(node)
            tmp_net_path.append(path[-1])  # add the target node
            net_paths.append(tmp_net_path)
            transistor_paths.append(tmp_path)
        return net_paths, transistor_paths

    def get_transistor_switch_count(self, G):
        """
        Get the number of switches in the graph.
        """
        count = 0
        for node in G.nodes:
            if G.nodes[node]["type"] == "transistor":
                count += 1
        return count

    def swap_nodes(self, G, node1, node2):
        """
        Swap two nodes in the graph.
        """
        new_G = G.copy()

        # Save node attributes before removing nodes
        node1_type = new_G.nodes[node1].get("type")
        node1_net = new_G.nodes[node1].get("net")
        node2_type = new_G.nodes[node2].get("type")
        node2_net = new_G.nodes[node2].get("net")

        # Get the neighbors of both nodes
        neighbors1 = list(new_G.neighbors(node1))
        neighbors2 = list(new_G.neighbors(node2))

        # Remove the nodes
        new_G.remove_node(node1)
        new_G.remove_node(node2)

        # Add the nodes back with swapped attributes
        new_G.add_node(node1, type=node2_type, net=node2_net)
        new_G.add_node(node2, type=node1_type, net=node1_net)

        # Add the edges, connecting each node to the other's former neighbors
        for neighbor in neighbors2:
            if neighbor != node1:  # Avoid self-loops
                new_G.add_edge(node1, neighbor)

        for neighbor in neighbors1:
            if neighbor != node2:  # Avoid self-loops
                new_G.add_edge(node2, neighbor)

        return new_G

    def merge_node(self, G, node1, node2):
        """
        Merge two nodes in the graph.
        Conditions applied
        """
        if node1 == node2:
            print("[MERGE NODE] Nodes are the same, no merge needed")
            return G
        if (
            G.nodes[node1]["type"] != G.nodes[node2]["type"]
            and G.nodes[node1]["net"] != G.nodes[node2]["net"]
        ):
            print("[MERGE NODE] Nodes are not of the same type or net, no merge needed")
            return G
        # Keep the node with more # paths
        paths_through_node1 = self.simple_paths_through_node(G, source="VSS", target="OUT", v=node1)
        node1_total_paths = len(paths_through_node1)
        paths_through_node2 = self.simple_paths_through_node(G, source="VSS", target="OUT", v=node2)
        node2_total_paths = len(paths_through_node2)
        if node1_total_paths > node2_total_paths:
            node_to_keep = node1
            paths_to_keep = paths_through_node1
            node_to_remove = node2
            paths_to_remove = paths_through_node2
        else:
            node_to_keep = node2
            paths_to_keep = paths_through_node2
            node_to_remove = node1
            paths_to_remove = paths_through_node1
        print(
            f"[MERGE NODE] Keeping node {node_to_keep} ({node1_total_paths} paths) and removing node {node_to_remove} ({node2_total_paths} paths)"
        )
        # along the path, remove each node conditionally
        neighbors_of_node_to_keep = list(G.neighbors(node_to_keep))
        for path in paths_to_remove:
            for node in path:
                degree = G.degree(node)
                if node == "VSS" or node == "OUT":
                    continue
                elif G.nodes[node]["type"] == "transistor":
                    if degree == 1 or node == node_to_remove: # remove disconnected transistor
                        G.remove_node(node)
                        print(f"[MERGE NODE] Removed node {node} with degree {degree}")
                    else:
                        continue
                elif G.nodes[node]["type"] == "net":
                    if degree == 2:
                        G.remove_node(node)
                        print(f"[MERGE NODE] Removed node {node} with degree {degree}")
                    elif degree >= 2 and node in neighbors_of_node_to_keep: # remove bc it upstream node is removed
                        G.remove_node(node)
                        print(f"[MERGE NODE] Removed node {node} with degree {degree}")
                    elif degree >= 2 and not node in neighbors_of_node_to_keep: # do not remove bc it has another path
                        continue
                    else:
                        assert degree != 0, f"Node {node} has degree 0"
                        assert degree != 1, f"Node {node} has degree 1"
        # # add back the net_path_to_keep along node_to_keep
        # for pkp in paths_to_keep:
        #     for prm in paths_to_remove:
        #         # if set(pkp) == set(prm):
        #         #     print(f"[MERGE NODE] No need to add back {prm} as {pkp} already exists")
        #         #     continue
        #         # check global path
        #         if self.graph_has_equal_path(G, path):
        #             print(f"[MERGE NODE] No need to add back {prm} as {pkp} already exists")
        #             continue
        #         DISCREPANCY_FLAG = False
        #         for node_kept in pkp:
        #             for node_add_back in prm:
        #                 pass
        
    def graph_has_equal_path(self, G, path):
        """
        Check if the graph has the same path as the given path in terms of net set.
        """
        # extract the net set from the path
        path_net_set = set()
        for node in path:
            if G.nodes[node]["type"] == "transistor":
                path_net_set.add(G.nodes[node]["net"])
        cutoff = len(path_net_set)
        # check all simple paths in the graph
        for p in nx.all_simple_paths(G, source="VSS", target="OUT", cutoff=cutoff):
            # extract the net set from the path
            p_net_set = set()
            for node in p:
                if G.nodes[node]["type"] == "transistor":
                    p_net_set.add(G.nodes[node]["net"])
            if path_net_set == p_net_set:
                print(f"[GRAPH HAS EQUAL PATH] Found equal path: {p}")
                return True
        
        

    # TODO: Not sure how to merge d and g
    def simple_sharing(self, G):
        """
        Check if two graphs share any transistor nodes.
        Do not destroy any existing paths present in G1 or G2.
        Return a merged graph with the shared transistor nodes.
        """
        net_paths_in_G, transistor_paths_in_G = self.get_transistor_net_paths(G, source="VSS", target="OUT")
        inital_switch_count = self.get_transistor_switch_count(G)
        print(f"[SIMPLE SHARING] Initial switch count: {inital_switch_count}")
        tmp_switch_count = -1
        tmp_G = G.copy()
        # keep track that at each depth, what is the majority switch
        depth_to_majority_switch = {}
        while inital_switch_count > tmp_switch_count:
            # find equivalent switche set E
            equivalent_switches = set()
            for path1 in net_paths_in_G:
                # record the majority switch
                for i, node in enumerate(path1):
                    if node == "VSS" or node == "OUT":
                        continue
                    if i not in depth_to_majority_switch:
                        depth_to_majority_switch[i] = [node]
                    else:
                        depth_to_majority_switch[i].append(node)
                # check other paths for equivalent switches
                for path2 in net_paths_in_G:
                    if path1 == path2:
                        continue
                    equivalent_switches.update(set(path1).intersection(path2) - set(["VSS", "OUT"]))
            print(
                f"[SIMPLE SHARING] Found {len(equivalent_switches)} equivalent switches"
            )
            print(f"[SIMPLE SHARING] Equivalent switches: {equivalent_switches}")
            # reduce the list to majority switches
            for depth, switches in depth_to_majority_switch.items():
                # count the number of switches
                switch_count = {}
                for switch in switches:
                    if switch not in switch_count:
                        switch_count[switch] = 1
                    else:
                        switch_count[switch] += 1
                # find the majority switch
                majority_switch = max(switch_count, key=switch_count.get)
                depth_to_majority_switch[depth] = majority_switch
            print(
                f"[SIMPLE SHARING] Depth to majority switch: {depth_to_majority_switch}"
            ) # TODO: use this to determine swaping
            # if no equivalent switches are found, no need to swap and merge
            if equivalent_switches == set():
                break
            # swap the switches
            # for node1, node2 in itertools.combinations(equivalent_switches, 2):
            #     # Check if the nodes are not already swapped
            #     if node1 != node2:
            #         tmp_G = self.swap_nodes(tmp_G, node1, node2)
            # TODO: logic equivalence check
            for path1, tran1 in zip(net_paths_in_G, transistor_paths_in_G):
                for path2, tran2 in zip(net_paths_in_G, transistor_paths_in_G):
                    if path1 == path2:
                        continue
                    # check if the depth 1 nodes have the same net
                    if path1[1] == path2[1] and tran1[1] != tran2[1]:
                        node1 = tran1[1]
                        node2 = tran2[1]
                        print(f"[SIMPLE SHARING] Merging nodes {node1} and {node2}")
                        self.merge_node(tmp_G, node1, node2)
                    else:
                        print(f"[SIMPLE SHARING] No need to merge nodes: {path1} and {path2}")
            break # TODO: remove this
            tmp_switch_count = self.get_transistor_switch_count(tmp_G)
        return tmp_G

    def network_composition(self, graphs):
        final_graph = nx.Graph()
        visited_literals = set()
        print(f"Network composition for {len(graphs)} graphs")
        # make parallel association
        for i, g in enumerate(graphs):
            print(f"Graph {i}: {g.nodes()}")
            # add seen_nets to visited_literals
            seen_nets = [
                d["net"] for n, d in g.nodes(data=True) if d["type"] == "transistor"
            ]
            if i == 0 or self.transistor_graph_has_new_nets(final_graph, g):
                final_graph.add_nodes_from(g.nodes(data=True))
                final_graph.add_edges_from(g.edges(data=True))
            # get the net from transistor nodes
            visited_literals.update(seen_nets)
            # stop condition
            if len(visited_literals) == len(self.all_literals):
                print("Break early; All literals have been visited")
                break
        assert len(visited_literals) == len(
            self.all_literals
        ), f"Did not visit all literals: {visited_literals} != {self.all_literals}"
        for node in final_graph.nodes():
            print(f"Node {node}", f"Attributes: {final_graph.nodes[node]}")
        for edge in final_graph.edges():
            print(f"Edge {edge}")
        # fix VDD to the top, OUT in the middle, and VSS to the bottom
        # fixed_positions = {"VDD": (0, 200), "OUT": (0, 0), "VSS": (0, -200)}
        # pos = nx.spring_layout(final_graph, pos=fixed_positions, fixed=fixed_positions, iterations=10000)
        # self.__plot_graph__(
        #     final_graph,
        #     pos=pos,
        #     node_attribute_keys=["type", "net"],
        #     edge_attribute_keys=[],
        #     title="Final graph",
        # )
        #print all simple paths in the graph
        for path in nx.all_simple_paths(final_graph, source="VSS", target="OUT"):
            print(f"Simple path: {path}")
        self.simple_sharing(final_graph)
        # based on nmos graph, produce dual graph for pmos
        nmos_faces = self.get_faces_from_nmos_graph(final_graph)
        print(f"Found {len(nmos_faces)} faces in the NMOS graph: {nmos_faces}")
        # add pmos dual graph
        pmos_graph = self.add_pmos_dual_graph(nmos_faces, final_graph.nodes(data=True))
        final_graph.add_nodes_from(pmos_graph.nodes(data=True))
        final_graph.add_edges_from(pmos_graph.edges(data=True))
        self.to_netlist(final_graph, "final", "./output/netlist/final.cdl")
        print("Testing equivalence of the final graph with the original graph ...")
        # sg = SchematicGraph(
        #     cdl_file="/home/dinple/SMTCell/CellDiego/output/netlist/final.cdl",
        #     boolean_func=self.F_str,
        #     circuit_name="final",
        # )
        
    def simple_paths_through_node(self, G, source, target, v, cutoff=None):
        paths = []
        for path in nx.all_simple_paths(G, source=source, target=target, cutoff=cutoff):
            if v in path:
                paths.append(path)
        return paths

    def add_pmos_dual_graph(self, faces, nodes):
        pmos_graph = nx.Graph()
        pmos_nets = set()
        for i, f in enumerate(faces):
            # if a face has "OUT" next to "VSS", then this face forms an OUT net
            net_name = None
            if (
                "OUT" in f
                and "VSS" in f
                and (
                    f.index("OUT") == f.index("VSS") + 1
                    or f.index("OUT") == f.index("VSS") - 1
                )
            ):
                net_name = "OUT"
            elif i == len(faces) - 1:
                assert (
                    "OUT" in f and "VSS" in f
                ), "Last face should have OUT and VSS as it is the outer face"
                net_name = "VDD"
            else:
                net_name = "NET" + str(len(pmos_nets))
            assert net_name is not None, "Net name is None"
            assert net_name not in pmos_nets, f"Net {net_name} already exists"
            pmos_nets.add(net_name)
            pmos_graph.add_node(net_name, type="net")
            # add transistor nodes to this net
            for it in f:
                # detect transistor nodes
                if (
                    not it.startswith("NET")
                    and not it.startswith("VSS")
                    and not it.startswith("OUT")
                ):
                    tran_name = it.replace("MMN_", "MMP_")
                    pmos_graph.add_node(
                        tran_name, type="transistor", net=nodes[it]["net"]
                    )
                    pmos_graph.add_edge(tran_name, net_name)
        return pmos_graph

    def polygon_area(self, face, pos):
        """
        Compute the area of a polygon (face) using the shoelace formula.

        Args:
            face (list): An ordered list of vertices that define the polygon.
            pos (dict): A mapping from vertex to its (x, y) coordinate.

        Returns:
            float: The computed area of the polygon.
        """
        n = len(face)
        area = 0
        for i in range(n):
            x1, y1 = pos[face[i]]
            x2, y2 = pos[face[(i + 1) % n]]
            area += x1 * y2 - x2 * y1
        return abs(area) / 2.0

    def get_faces_from_nmos_graph(self, nmos_graph):
        """
        Add an auxiliary edge connection VSS and OUT, so that one face represents the OUT node.
        """
        # Set fixed positions for VSS and OUT at far apart coordinates.
        fixed_positions = {"VSS": (-50, 0), "OUT": (50, 0)}
        pos = nx.spring_layout(
            nmos_graph, pos=fixed_positions, fixed=fixed_positions, iterations=1000
        )
        # self.__plot_graph__(
        #     nmos_graph,
        #     pos=pos,
        #     node_attribute_keys=["type", "net"],
        #     edge_attribute_keys=[],
        # )
        nmos_graph.add_edge("VSS", "OUT")
        faces = self.planar_faces(nmos_graph)
        nmos_graph.remove_edge("VSS", "OUT")
        # print(f"Found {len(faces)} faces in the NMOS graph: {faces}")

        # Compute the area of each face
        face_areas = [self.polygon_area(face, pos) for face in faces]
        # print(f"Face areas: {face_areas}")
        # The outer face is the one with the largest area.
        outer_face_index = face_areas.index(max(face_areas))
        outer_face = faces.pop(outer_face_index)
        faces.append(outer_face)
        return faces

    def planar_faces(self, G):
        """
        Extract faces from a planar graph using half-edge data structure terminology.

        Args:
            G (nx.Graph): A planar undirected graph

        Returns:
            list: List of faces, where each face is a list of vertices in order
        """
        # Check if G is planar and get its embedding
        is_planar, embedding = nx.check_planarity(G)
        if not is_planar:
            raise nx.NetworkXException("Graph is not planar!")

        # Get the rotation system (clockwise ordering of neighbors)
        rotation_system = embedding.get_data()

        # Create half-edge structure
        # Each (u,v) edge is a directed half-edge
        half_edges_used = set()
        faces = []

        # For each vertex and its incident half-edges in the rotation system
        for vertex, adjacent_vertices in rotation_system.items():
            for i, target in enumerate(adjacent_vertices):
                # This represents a half-edge from vertex to target
                half_edge = (vertex, target)

                # Skip if we've already processed this half-edge
                if half_edge in half_edges_used:
                    continue

                # Start a new face
                face = []
                current_vertex, next_vertex = vertex, target

                # Follow half-edges around the face
                while True:
                    # Mark this half-edge as used
                    half_edges_used.add((current_vertex, next_vertex))
                    face.append(current_vertex)

                    # Get the rotation system at the next vertex
                    rotation = rotation_system[next_vertex]

                    # Find the twin half-edge's position in the rotation
                    twin_idx = rotation.index(current_vertex)

                    # Find the next half-edge in counter-clockwise order around the face
                    # In a rotation system, moving -1 gives us the next edge around a face
                    next_half_edge_idx = (twin_idx - 1) % len(rotation)
                    next_half_edge_target = rotation[next_half_edge_idx]

                    # Update for next iteration
                    current_vertex, next_vertex = next_vertex, next_half_edge_target

                    # If we've completed the cycle, we've found a face
                    if (current_vertex, next_vertex) in half_edges_used:
                        if current_vertex == vertex:
                            break

                faces.append(face)

        return faces

    def _add_pmos_dual_graph(self, nmos_graph):
        """
        Given an NMOS graph (which is planar), compute the dual graph corresponding
        to the PMOS network. Each face in the NMOS graph becomes a PMOS node.
        """
        # Check for planarity and get the embedding.
        is_planar, embedding = nx.check_planarity(nmos_graph, counterexample=False)
        if not is_planar:
            raise ValueError("The NMOS graph is not planar.")

        # Custom function to extract faces from the embedding.
        def get_faces_from_embedding(G, embedding):
            """
            Traverse each directed edge in the embedding that has not been visited
            and return a list of faces. Each face is represented as a list of nodes in
            cyclic order.
            """
            visited = set()
            faces = []
            face_to_incident_nodes = {}
            for u in embedding:
                for v in embedding[u]:
                    print(f"u: {u}, v: {v}")
                    if (u, v) in visited:
                        continue
                    face = []
                    current_edge = (u, v)
                    start_edge = (u, v)
                    while True:
                        visited.add(current_edge)
                        face.append(current_edge[0])
                        # At current edge (u, v), find the index of u in v's cyclic order.
                        neighbors = list(embedding.neighbors_cw_order(current_edge[1]))
                        idx = neighbors.index(current_edge[0])
                        # Get the predecessor in the cyclic order (wrap-around with modulo)
                        next_neighbor = neighbors[(idx - 1) % len(neighbors)]
                        current_edge = (current_edge[1], next_neighbor)
                        if current_edge == start_edge:
                            face.c(current_edge[0])
                            break
                    faces.append(face)
            return faces

        # Get the faces from the embedding using our custom function.
        faces = get_faces_from_embedding(nmos_graph, embedding)
        print(f"Found {len(faces)} faces in the NMOS graph: {faces}")

        # Create the dual graph: each face corresponds to a PMOS node.
        pmos_graph = nx.Graph()
        face_to_pmos = {}
        for i, face in enumerate(faces):
            pmos_node = f"pmos_{i}"
            pmos_graph.add_node(pmos_node, face=face, type="transistor")
            face_to_pmos[i] = pmos_node

        # Helper: get the set of undirected edges for a given face.
        def edges_in_face(face):
            edge_set = set()
            n = len(face)
            for i in range(
                n - 1
            ):  # face is cyclic; last equals first is already appended
                u = face[i]
                v = face[i + 1]
                edge_set.add(frozenset([u, v]))
            return edge_set

        # Precompute the set of edges for each face.
        face_edges = [edges_in_face(face) for face in faces]

        # For every pair of faces, if they share an edge, add an edge in the dual graph.
        for i in range(len(faces)):
            for j in range(i + 1, len(faces)):
                if face_edges[i] & face_edges[j]:
                    pmos_graph.add_edge(face_to_pmos[i], face_to_pmos[j])

        return pmos_graph

    def nsp_kernel_identification(self, cubes, return_all=False):
        """
        Find all NSP mappings for the given graph.

        Args:
            graph (nx.Graph): The graph to find NSP mappings for.

        Returns:
            list: A list of unique NSP mappings found.
        """
        G, edges, incident_labels = self.construct_graph(cubes)
        # check rule 1
        if not self.check_rule1(cubes, incident_labels):
            print("\t\tRule 1 not satisfied")
            return [], []
        nsp_mappings = []
        nsp_graphs = []
        # ^ A.1 NSP kernel identification
        # NOTE: although not specified in the paper, NSP kernel is possible to match with a complete graph with 4 vertices.
        # check if the graph is a complete graph with 4 vertices
        if self.is_complete(G) and G.order() == 4:
            # remove an edge and check if the new graph is planar or not
            for e in G.edges:
                tmp_graph = G.copy()
                tmp_graph.remove_edge(*e)
                # self.__plot_graph__(tmp_graph)
                if not nx.check_planarity(tmp_graph)[0]:
                    continue
                # the graph is planar then try to match with the NSP template
                is_nsp_isomorphic, mapping = self.is_graph_isomorphic(
                    tmp_graph, NSP_TEMPLATE_GRAPH, return_all=return_all
                )
                if not is_nsp_isomorphic:
                    continue
                nsp_mappings.append(mapping)
                nsp_graphs.append(self.to_NSP_kernel_graph(tmp_graph, mapping))
        else:
            # check if the graph is isomorphic to the NSP template
            is_nsp_isomorphic, mapping = self.is_graph_isomorphic(
                G, NSP_TEMPLATE_GRAPH, return_all=return_all
            )
            if is_nsp_isomorphic:
                nsp_mappings.append(mapping)
                nsp_graphs.append(self.to_NSP_kernel_graph(G, mapping))
        if nsp_mappings == []:
            print("\t\tNo kernel for NSP found")
            return [], []
        else:
            unique_mappings, unique_graphs = self.get_unique_mappings(
                nsp_mappings, nsp_graphs
            )
            return unique_mappings, unique_graphs

    # TODO: rewrite with construct_graph in mind
    def sp_kernel_identification(self, cubes, return_all=False):
        """
        Find all SP mappings for the given graph.

        Args:
            graph (nx.Graph): The graph to find SP mappings for.

        Returns:
            list: A list of unique SP mappings found.
        """
        G, edges, incident_labels = self.construct_graph(cubes)
        # check rule 1
        if not self.check_rule1(cubes, incident_labels):
            print("\t\tRule 1 not satisfied")
            return [], []
        # check if the graph is isomorphic to the SP template
        is_sp_isomorphic, sp_mappings = self.is_graph_isomorphic(
            G, SP_TEMPLATE_GRAPH, return_all=return_all
        )
        sp_graphs = self.to_SP_kernel_graph(G, sp_mappings)
        if not is_sp_isomorphic:
            # print("No kernel for SP found")
            return [], []
        else:
            unique_mappings, unique_graphs = self.get_unique_mappings(
                sp_mappings, sp_graphs
            )
            # print("SP mappings:", unique_mappings)
            # print(f"Found {len(unique_mappings)} SP mappings ...")
            return unique_mappings, unique_graphs

    def get_n_comb_node_set(self, G, n):
        """
        Get combinations of n nodes from the graph.
        Do not include the nodes that are already in the set.
        """
        # Get all nodes in the graph
        all_nodes = list(G.nodes())
        # Generate all combinations of n nodes
        combinations = list(itertools.combinations(all_nodes, n))
        return [list(combination) for combination in combinations]

    def kernel_identification(self):
        """
        Identify the kernel of the graph.
        """
        tmp_graph = self.graph.copy()
        # all_mappings = []
        all_graphs = []
        visited_cube_sets = set()
        # ^ A.1 NSP kernel identification
        four_cubes_combinations = self.get_n_comb_node_set(tmp_graph, 4)
        for cube_set in four_cubes_combinations:
            cubes = [tmp_graph.nodes[cube]["cube"] for cube in cube_set]
            print(f"\tCube set: {cube_set} {cubes}")
            nsp_mappings, nsp_graphs = self.nsp_kernel_identification(
                cubes, return_all=False
            )
            if nsp_mappings:
                visited_cube_sets.add(frozenset(cube_set))
                all_graphs.extend(nsp_graphs)
        # delete the visited cube sets from graph, prepare for the next iteration
        for cube_set in visited_cube_sets:
            tmp_graph.remove_nodes_from(cube_set)
        print(
            f"After NSP --> Visited {len(visited_cube_sets)} cube sets; Remaining nodes: {tmp_graph.nodes()}"
        )
        if len(tmp_graph.nodes()) == 0:
            return all_graphs
        # ^ A.2 SP kernel identification
        four_cubes_combinations = self.get_n_comb_node_set(tmp_graph, 4)
        for cube_set in four_cubes_combinations:
            cubes = [tmp_graph.nodes[cube]["cube"] for cube in cube_set]
            sp_mappings, sp_graphs = self.sp_kernel_identification(
                cubes, return_all=False
            )
            if sp_mappings:
                visited_cube_sets.add(frozenset(cube_set))
                all_graphs.extend(sp_graphs)
        # delete the visited cube sets from graph, prepare for the next iteration
        for cube_set in visited_cube_sets:
            tmp_graph.remove_nodes_from(cube_set)
        print(
            f"After SP --> Visited {len(visited_cube_sets)} cube sets; Remaining nodes: {tmp_graph.nodes()}"
        )
        if len(tmp_graph.nodes()) == 0:
            # return all_mappings
            return all_graphs
        # ^ A.3 Redundant Cube Insertion
        three_cubes_combinations = self.get_n_comb_node_set(tmp_graph, 3)
        for cube_set in three_cubes_combinations:
            cubes = [tmp_graph.nodes[cube]["cube"] for cube in cube_set]
            rci_mappings, rci_graphs = self.redundant_cube_insertion(
                cubes, return_all=False
            )
            if rci_mappings:
                visited_cube_sets.add(frozenset(cube_set))
                all_graphs.extend(rci_graphs)
        # delete the visited cube sets from graph, prepare for the next iteration
        for cube_set in visited_cube_sets:
            tmp_graph.remove_nodes_from(cube_set)
        print(
            f"After RCI --> Visited {len(visited_cube_sets)} cube sets; Remaining nodes: {tmp_graph.nodes()}"
        )
        if len(tmp_graph.nodes()) == 0:
            # return all_mappings
            return all_graphs
        # ^ A.4 Branched Network Generation
        # generate a branched network from the graph
        print(
            f"Branched Network Generation is used to fill the remaining graph nodes :{tmp_graph.nodes()}"
        )
        bn_graph = self.branched_network_generation(tmp_graph)
        all_graphs.append(bn_graph)

        # remove duplicate graphs
        unique_graphs = []
        for g in all_graphs:
            if not any(self.graph_equal(g, other) for other in unique_graphs):
                unique_graphs.append(g)

        return unique_graphs

    def branched_network_generation(self, G):
        """
        Generate a branched network from the graph.
        """
        start_node = "VSS"
        end_node = "OUT"
        bn_graph = nx.Graph()
        bn_graph.add_node(start_node, type="net")
        bn_graph.add_node(end_node, type="net")
        net_id = 0
        for cube in G.nodes:
            # each cube forms a path connecting from start_node to end_node
            for i, lit in enumerate(G.nodes[cube]["cube"]):
                bn_graph.add_node(
                    f"MMN_bn_{lit}_{GRAPH_ID}", type="transistor", net=lit
                )
                if i == 0:
                    bn_graph.add_edge(start_node, f"MMN_bn_{lit}_{GRAPH_ID}")
                    bn_graph.add_node(f"NET_bn_{net_id}_{GRAPH_ID}", type="net")
                    bn_graph.add_edge(
                        f"MMN_bn_{lit}_{GRAPH_ID}",
                        f"NET_bn_{net_id}_{GRAPH_ID}",
                    )
                elif i == len(G.nodes[cube]["cube"]) - 1:
                    bn_graph.add_edge(
                        f"NET_bn_{net_id}_{GRAPH_ID}",
                        f"MMN_bn_{lit}_{GRAPH_ID}",
                    )
                    bn_graph.add_edge(f"MMN_bn_{lit}_{GRAPH_ID}", end_node)
                else:
                    bn_graph.add_edge(f"NET_bn_{net_id}_{GRAPH_ID}", f"MMN_bn_{lit}")
                    net_id += 1
                    bn_graph.add_node(f"NET_bn_{net_id}_{GRAPH_ID}", type="net")
                    bn_graph.add_edge(
                        f"MMN_bn_{lit}_{GRAPH_ID}",
                        f"NET_bn_{net_id}_{GRAPH_ID}",
                    )
        return bn_graph

    def redundant_cube_insertion(self, cubes, return_all=False):
        """
        For each combination of 3 cubes from the input list, insert a redundant cube vz.
        For each cube in the 3-cube candidate, the missing literals are computed as:
        missing = cube - (union of edge labels from the induced graph among the 3 cubes)
        The redundant cube is defined as the union of all missing literals.
        Then the candidate kernel is the 3 cubes plus the redundant cube.
        The new kernel must satisfy Rule 1 and have exactly 5 edges (Rule 2).
        Returns a list of tuples (kernel, edges) for valid kernels obtained by redundant cube insertion.
        """
        G, edges, incident_labels = self.construct_graph(cubes)
        missing_union = set()
        for i in range(len(cubes)):
            missing = cubes[i] - incident_labels[i]
            missing_union.update(missing)
        if missing_union == 1:
            # only one missing literal, so we have to choose one existing literal
            # and add it to the missing_union
            print("Only one missing literal, picking an existing literal randomly")
            raise NotImplementedError
        elif missing_union > 1:
            new_cubes = cubes + [missing_union]
            nsp_mappings, nsp_graphs = self.nsp_kernel_identification(
                new_cubes, return_all=return_all
            )
            # do not return the same graph
            if nsp_mappings:
                return nsp_mappings, nsp_graphs
        return [], []

    def parse_function(self, F_str):
        """
        Parse a Boolean function in ISOP form with support for parentheses.
        Handles expressions like "(a & b) | (c & !d)" properly.
        Returns a list of cubes, where each cube is represented as a Cube object.
        """
        # Remove "F =" if present
        F_str = F_str.replace("F =", "").strip()

        # Helper function to parse a single term (handles parentheses)
        def parse_term(term):
            # If term is wrapped in parentheses, remove them and parse inside
            term = term.strip()
            if term.startswith("(") and term.endswith(")"):
                # Remove outermost parentheses
                term = term[1:-1].strip()

            # Split by & for AND terms
            and_terms = []

            # Handle nested parentheses when splitting AND terms
            paren_level = 0
            current_term = ""
            for char in term + "&":  # Add delimiter at end to catch final term
                if char == "(" and not paren_level:
                    current_term += char
                    paren_level += 1
                elif char == "(":
                    current_term += char
                    paren_level += 1
                elif char == ")":
                    current_term += char
                    paren_level -= 1
                elif char == "&" and paren_level == 0:
                    and_terms.append(current_term.strip())
                    current_term = ""
                else:
                    current_term += char

            # Process literals in the term
            literals = []
            for and_term in and_terms:
                if and_term.startswith("(") and and_term.endswith(")"):
                    # This is a nested term - recursively parse it
                    sub_literals = parse_term(and_term)
                    literals.extend(sub_literals)
                else:
                    # Simple literal
                    lit = and_term.strip()
                    if lit.startswith("!"):
                        literals.append(lit)
                    else:
                        literals.append(lit)

            return literals

        # Split by OR, respecting parentheses
        cube_terms = []
        paren_level = 0
        current_term = ""

        for char in F_str + "|":  # Add delimiter at end to catch final term
            if char == "(":
                current_term += char
                paren_level += 1
            elif char == ")":
                current_term += char
                paren_level -= 1
            elif char == "|" and paren_level == 0:
                cube_terms.append(current_term.strip())
                current_term = ""
            else:
                current_term += char

        # Parse each OR term into a cube
        cubes = []
        for term in cube_terms:
            if term:  # Skip empty terms
                literals = parse_term(term)
                cubes.append(Cube(literals))

        return cubes

    def check_rule1(self, cubes, incident_labels):
        """
        Rule 1: For every cube (vertex), the union of incident edge labels
        must equal the cube's literal set.
        """
        for i in range(len(cubes)):
            if cubes[i] != incident_labels[i]:
                return False
        return True

    def check_rule3(self, edges, num_vertices):
        """
        Rule 3: In the SP kernel template each vertex should have degree 2.
        Degree is computed by counting how many edges are incident to each vertex.
        """
        degrees = {i: 0 for i in range(num_vertices)}
        for (i, j), _ in edges:
            degrees[i] += 1
            degrees[j] += 1
        return all(degree == 2 for degree in degrees.values())

    # TODO: properly ID the cubes
    def construct_graph(self, cubes, cube_ids=None):
        """
        Given a list of cubes (each a set of literals), construct a graph.
        Returns:
        edges: a list of tuples ((i, j), common_literals)
        incident_labels: a dict mapping vertex index i to the union of edge labels incident on that vertex.
        """
        n = len(cubes)
        edges = []
        incident_labels = {i: set() for i in range(n)}
        edge_list = []  # Simple edge list for NetworkX

        for i in range(n):
            for j in range(i + 1, n):
                common = cubes[i].intersection(cubes[j])
                if common:
                    edges.append(((i, j), frozenset(common)))  # Convert to frozenset
                    incident_labels[i].update(common)
                    incident_labels[j].update(common)
                    edge_list.append((i, j))  # Add simple edge without data
        G = nx.Graph()
        # Construct NetworkX graph with simple edges
        # node labels are the cubes themselves
        # edge labels are the common literals
        G.add_nodes_from([(i, {"cube": cubes[i]}) for i in range(n)])
        G.add_edges_from([(i, j, {"common": common}) for (i, j), common in edges])
        return G, edges, incident_labels

    def draw(self, filename):
        # draw the graph
        pos = nx.spring_layout(self.graph)
        edge_labels = {(i, j): ", ".join(common) for (i, j), common in self.edges}
        node_labels = {i: str(cube) for i, cube in enumerate(self.cubes)}
        nx.draw(self.graph, pos, with_labels=True, labels=node_labels)
        nx.draw_networkx_edge_labels(self.graph, pos, edge_labels=edge_labels)
        plt.savefig(filename)
        plt.clf()

    def is_graph_isomorphic(self, G, graph_to_match, return_all=False):
        """
        Check if the graph isomorphism problem is solvable in polynomial time.
        """
        GM = iso.GraphMatcher(G, graph_to_match)
        if return_all:
            is_iso = GM.is_isomorphic()
            return is_iso, list(GM.subgraph_isomorphisms_iter())
        else:
            is_iso = GM.is_isomorphic()
            mapping = next(GM.isomorphisms_iter(), None)
            # print("GM Mapping: ", [GM.mapping])
            return is_iso, mapping

    def plot_graph(self, edges):
        """
        Plot the graph using matplotlib.
        """
        pos = nx.spring_layout(self.graph)
        edge_labels = {(i, j): ", ".join(common) for (i, j), common in edges}
        node_labels = {
            i: str(cube) for i, cube in enumerate(self.graph.nodes(data="cube"))
        }
        nx.draw(self.graph, pos, with_labels=True, labels=node_labels)
        nx.draw_networkx_edge_labels(self.graph, pos, edge_labels=edge_labels)
        plt.title("Input Transistor Graph")
        plt.axis("off")  # Hide axes
        plt.tight_layout()  # Adjust layout to fit labels
        plt.show()

    def __plot_graph__(
        self, G, pos=None, node_attribute_keys=[], edge_attribute_keys=[], title=None
    ):
        """
        Plot the graph using matplotlib.
        """
        plt.title(title if title else "Graph")
        if pos is None:
            pos = nx.spring_layout(G)
        nx.draw(G, pos, with_labels=True)

        # draw labels for nodes based on the specified attribute
        node_labels = {}
        for node_attribute_key in node_attribute_keys:
            # Check if at least one node has this attribute
            has_attribute = any(
                node_attribute_key in data for _, data in G.nodes(data=True)
            )
            if not has_attribute:
                print(
                    f"Node attribute '{node_attribute_key}' not found in any graph nodes."
                )
                continue

            # Create labels only for nodes that have this attribute
            for node, data in G.nodes(data=True):
                if node_attribute_key in data:
                    # append the attribute value to the label
                    if node in node_labels:
                        node_labels[node] += f", {data[node_attribute_key]}"
                    else:
                        node_labels[node] = str(data[node_attribute_key])
        # draw with a small offset to avoid overlap
        node_label_pos = {
            node: (x + 15, y + 15) for node, (x, y) in pos.items()
        }  # offset y position
        nx.draw_networkx_labels(
            G,
            node_label_pos,
            labels=node_labels,
            font_size=10,
            verticalalignment="bottom",
            bbox=dict(boxstyle="round,pad=0.3", fc="white", ec="none", alpha=0.7),
        )

        # Similarly for edge attribute
        edge_labels = {}
        for edge_attribute_key in edge_attribute_keys:
            # Check if at least one edge has this attribute
            has_attribute = any(
                edge_attribute_key in data for _, _, data in G.edges(data=True)
            )
            if not has_attribute:
                print(
                    f"Edge attribute '{edge_attribute_key}' not found in any graph edges."
                )
                continue
            # Create labels only for edges that have this attribute
            for u, v, data in G.edges(data=True):
                if edge_attribute_key in data:
                    # append the attribute value to the label
                    if (u, v) in edge_labels:
                        edge_labels[(u, v)] += f", {data[edge_attribute_key]}"
                    else:
                        edge_labels[(u, v)] = str(data[edge_attribute_key])
        edge_label_pos = {
            (u, v): (
                (pos[u][0] + pos[v][0]) / 2,
                (pos[u][1] + pos[v][1]) / 2 + 0.05,
            )  # offset y position
            for u, v in edge_labels.keys()
        }
        # draw edge labels with a small offset to avoid overlap
        nx.draw_networkx_edge_labels(
            G,
            edge_label_pos,
            edge_labels=edge_labels,
            font_size=8,
            bbox=dict(boxstyle="round,pad=0.3", fc="white", ec="none", alpha=0.7),
        )
        plt.axis("off")  # Hide axes
        plt.tight_layout()  # Adjust layout to fit labels
        plt.show()

    def __plot_planar_graph__(self, G: nx.PlanarEmbedding):
        """
        Plot the planar graph using matplotlib.
        Parameters:
            G (nx.Graph): NetworkX graph to be plotted
        """
        nx.draw_planar(G)
        plt.show()

    def to_NMOS_netlist(self, H, mapping):
        """
        Convert the graph to an NMOS transistor netlist.
        """
        for node_name, cube in mapping.items():
            # Extract the literals from the cube
            literals = [lit for lit in cube if not lit.startswith("!")]

    def to_SP_kernel_graph(self, H, mapping):
        """
        Convert the graph to an SP kernel netlist.
        """
        global GRAPH_ID
        kernel_graph = nx.Graph()
        # add OUT and VSS nodes
        kernel_graph.add_node("OUT", type="net")
        kernel_graph.add_node("VSS", type="net")
        kernel_graph.add_node(f"NET_sp_center_{GRAPH_ID}", type="net")
        for e in H.edges:
            # get nodes that the edge connects
            u, v = e
            ku, kv = mapping[u], mapping[v]
            # get the corresponding edge
            start_node = None
            end_node = None
            trans_name = None
            if (ku == "v1" and kv == "v2") or (ku == "v2" and kv == "v1"):
                start_node = f"NET_sp_center_{GRAPH_ID}"
                end_node = "VSS"
                trans_name = f"MMN_sp_e1_{GRAPH_ID}"
            elif (ku == "v2" and kv == "v3") or (ku == "v3" and kv == "v2"):
                start_node = "OUT"
                end_node = f"NET_sp_center_{GRAPH_ID}"
                trans_name = f"MMN_sp_e2_{GRAPH_ID}"
            elif (ku == "v3" and kv == "v4") or (ku == "v4" and kv == "v3"):
                start_node = f"NET_sp_center_{GRAPH_ID}"
                end_node = "VSS"
                trans_name = f"MMN_sp_e3_{GRAPH_ID}"
            elif (ku == "v4" and kv == "v1") or (ku == "v1" and kv == "v4"):
                start_node = "OUT"
                end_node = f"NET_sp_center_{GRAPH_ID}"
                trans_name = f"MMN_sp_e4_{GRAPH_ID}"
            else:
                print("Invalid edge")
                raise NotImplementedError
            # add nodes and edges to kernel_graph
            if u in mapping and v in mapping:
                # get the corresponding edge from H
                edge = H.edges[u, v]
                # get the common literals
                common = edge["common"]
                # convert frozenset to set
                common_set = set(common)
                if len(common_set) > 1:  # add intermediate node
                    raise NotImplementedError("Intermediate nodes not supported")
                else:
                    # add new transistor node
                    # kernel_graph.add_node(trans_name, type="transistor")
                    # trans_name = common_set.pop()
                    # NOTE: put the netname as net property because it is not unique
                    kernel_graph.add_node(
                        trans_name, type="transistor", net=common_set.pop()
                    )
                    # add edges
                    kernel_graph.add_edge(start_node, trans_name)
                    kernel_graph.add_edge(trans_name, end_node)
        GRAPH_ID += 1
        return kernel_graph

    def to_NSP_kernel_graph(self, H, mapping):
        """
        Convert the graph to an NSP kernel netlist.
        """
        global GRAPH_ID
        kernel_graph = nx.Graph()
        # add OUT and VSS nodes
        kernel_graph.add_node("OUT", type="net")
        kernel_graph.add_node("VSS", type="net")
        kernel_graph.add_node(f"NET_nsp_e5e2_{GRAPH_ID}", type="net")  # left
        kernel_graph.add_node(f"NET_nsp_e3e4_{GRAPH_ID}", type="net")  # right
        for e in H.edges:
            # get nodes that the edge connects
            u, v = e
            ku, kv = mapping[u], mapping[v]
            # get the corresponding edge
            start_node = None
            end_node = None
            trans_name = None
            if (ku == "v1" and kv == "v2") or (ku == "v2" and kv == "v1"):
                start_node = f"NET_nsp_e5e2_{GRAPH_ID}"
                end_node = "OUT"
                trans_name = f"MMN_nsp_e2_{GRAPH_ID}"
            elif (ku == "v2" and kv == "v3") or (ku == "v3" and kv == "v2"):
                start_node = "VSS"
                end_node = f"NET_nsp_e3e4_{GRAPH_ID}"
                trans_name = f"MMN_nsp_e3_{GRAPH_ID}"
            elif (ku == "v3" and kv == "v4") or (ku == "v4" and kv == "v3"):
                start_node = f"NET_nsp_e3e4_{GRAPH_ID}"
                end_node = "OUT"
                trans_name = f"MMN_nsp_e4_{GRAPH_ID}"
            elif (ku == "v4" and kv == "v1") or (ku == "v1" and kv == "v4"):
                start_node = "VSS"
                end_node = f"NET_nsp_e5e2_{GRAPH_ID}"
                trans_name = f"MMN_nsp_e5_{GRAPH_ID}"
            elif (ku == "v2" and kv == "v4") or (ku == "v4" and kv == "v2"):
                start_node = f"NET_nsp_e5e2_{GRAPH_ID}"
                end_node = f"NET_nsp_e3e4_{GRAPH_ID}"
                trans_name = f"MMN_nsp_e1_{GRAPH_ID}"
            else:
                print(f"Invalid edge", ku, kv)
                raise NotImplementedError
            # add nodes and edges to kernel_graph
            if u in mapping and v in mapping:
                # get the corresponding edge from H
                edge = H.edges[u, v]
                # get the common literals
                common = edge["common"]
                # convert frozenset to set
                common_set = set(common)
                if len(common_set) > 1:
                    raise NotImplementedError("Intermediate nodes not supported")
                else:
                    # add new transistor node
                    # trans_name = common_set.pop()
                    # NOTE: put the netname as net property because it is not unique
                    kernel_graph.add_node(
                        trans_name, type="transistor", net=common_set.pop()
                    )
                    # add edges
                    kernel_graph.add_edge(start_node, trans_name)
                    kernel_graph.add_edge(trans_name, end_node)
        GRAPH_ID += 1
        return kernel_graph

    def to_netlist(self, kernel_graph, subckt_name, outcdl):
        """
        Convert the graph to a netlist.
        """
        with open(outcdl, "w") as f:
            f.write("* Transistor graph netlist\n")
            # gather all the transistor nodes
            gate_net_str = " ".join(self.all_literals)
            f.write(f".SUBCKT {subckt_name} {gate_net_str} ZN VDD VSS\n")
            for k, v in kernel_graph.nodes(data=True):
                if v["type"] == "transistor":
                    # Get all edges connected to this transistor node
                    connected_edges = list(kernel_graph.edges(k))

                    assert (
                        len(connected_edges) == 2
                    ), f"Transistor {k} has {len(connected_edges)} connections, expected 2"

                    # Extract the source and drain nodes
                    source_node = connected_edges[0][1]
                    drain_node = connected_edges[1][1]

                    # Write transistor definition to netlist
                    # Format: M<name> <drain> <gate> <source> <body> <model>
                    gate_net = v["net"]
                    if "MMN" in k:
                        f.write(
                            f"{k} {drain_node} {gate_net} {source_node} VSS nmos L=0.15u W=1u\n"
                        )
                    elif "MMP" in k:
                        f.write(
                            f"{k} {drain_node} {gate_net} {source_node} VDD pmos L=0.15u W=1u\n"
                        )
            # always add an inverter at the end
            f.write("MMP0 ZN OUT VDD VDD pmos_rvt w=46.0n l=16n nfin=2\n")
            f.write("MMN0 ZN OUT VSS VSS nmos_rvt w=46.0n l=16n nfin=2\n")

            f.write(".ENDS\n")
            print(f"Netlist written to {outcdl}")

    def get_dual_pmos_graph(self, nmos_graph):
        """
        Convert the graph to a dual PMOS transistor netlist.
        """
        if not nx.is_planar(nmos_graph):
            print("The graph is not planar")
            return
        # convert to PlanarEmbedding
        embedding = nx.PlanarEmbedding(incoming_graph_data=nmos_graph)
        print(type(embedding))
        return embedding
        # pmos_graph = nx.Graph()
        # start_node = "VDD"
        # end_node = "OUT"
        # pmos_graph.add_node(start_node, type="net")
        # pmos_graph.add_node(end_node, type="net")


if __name__ == "__main__":
    # F_str = "F = a·b + !a·b + a·!b + !a·!b"
    # F_str = "a · b + a · c + a · d + b · c · d"
    # F_str = "(a & b) | (a & c) | (a & d) | (b & c & d)"
    # print(f"Testing with F_str: {F_str}")
    # tg = TransistorGraph(F_str)

    # a · b + a · c + c · e + a · d + b · c · d + a · g + b · c · g
    F_str = (
        "(a & b) | (a & c) | (c & e) | (a & d) | (b & c & d) | (a & g) | (b & c & g)"
    )
    print(f"Testing with F_str: {F_str}")
    tg = TransistorGraph(F_str)
