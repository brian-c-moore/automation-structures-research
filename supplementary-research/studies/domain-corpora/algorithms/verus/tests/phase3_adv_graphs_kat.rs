// phase3 advanced graphs KAT — cross-check.
extern crate algorithms_verus;
use algorithms_verus::instantiations::phase3_adv_graphs::{
    bellman_ford, dijkstra, floyd_warshall, graph_valid_tree, kruskal_mst, prim_mst,
};

fn check<T: std::fmt::Debug + PartialEq>(name: &str, got: T, want: T) -> bool {
    if got == want {
        println!("  PASS  {}", name);
        true
    } else {
        println!("  FAIL  {}: got {:?}, want {:?}", name, got, want);
        false
    }
}

fn main() {
    println!("phase3 advanced graphs KAT (Verus build)");
    let mut all_ok = true;

    // dijkstra: triangle 0-1 (w=2), 1-2 (w=3), 0-2 (w=10). From 0: dist=[0,2,5]
    let src = [0usize, 1, 0];
    let dst = [1usize, 2, 2];
    let w = [2i64, 3, 10];
    let d = dijkstra(3, &src, &dst, &w, 0);
    all_ok &= check("dijkstra[0]", d[0], 0);
    all_ok &= check("dijkstra[1]", d[1], 2);
    all_ok &= check("dijkstra[2]", d[2], 5);

    // bellman_ford: same graph.
    let d2 = bellman_ford(3, &src, &dst, &w, 0);
    all_ok &= check("bellman_ford[2]", d2[2], 5);

    // kruskal_mst: triangle. MST = 2 + 3 = 5.
    all_ok &= check("kruskal_mst triangle", kruskal_mst(3, &src, &dst, &w), 5);

    // prim_mst: same.
    all_ok &= check("prim_mst triangle", prim_mst(3, &src, &dst, &w), 5);

    // floyd_warshall: triangle.
    let fw = floyd_warshall(3, &src, &dst, &w);
    all_ok &= check("floyd_warshall[0->2]", fw[0 * 3 + 2], 5);
    all_ok &= check("floyd_warshall[1->2]", fw[1 * 3 + 2], 3);

    // graph_valid_tree: 3 nodes, 2 edges (0-1, 1-2) → tree.
    let ts = [0usize, 1];
    let td = [1usize, 2];
    all_ok &= check(
        "graph_valid_tree([(0,1),(1,2)])",
        graph_valid_tree(3, &ts, &td),
        true,
    );
    // 3 nodes with cycle 0-1-2-0 → not tree.
    let cs = [0usize, 1, 2];
    let cd = [1usize, 2, 0];
    all_ok &= check(
        "graph_valid_tree(cycle)",
        graph_valid_tree(3, &cs, &cd),
        false,
    );

    if all_ok {
        println!("KAT_RESULT: SUCCESS (phase3 6/6)");
        std::process::exit(0);
    } else {
        println!("KAT_RESULT: FAIL");
        std::process::exit(1);
    }
}
