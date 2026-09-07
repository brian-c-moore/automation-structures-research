// modalities KAT — cross-check.
extern crate cryptography_verus;
use cryptography_verus::modalities::sequential_refines_stepgraph::{
    begin_step, complete_step, expected_state, COMPLETED, NOT_READY, READY, RUNNING,
};

fn check(name: &str, ok: bool) -> bool {
    if ok {
        println!("  PASS  {}", name);
    } else {
        println!("  FAIL  {}", name);
    }
    ok
}

fn main() {
    println!("modalities KAT (Verus build)");
    let mut all_ok = true;

    // sequential_refines_stepgraph.
    let mut pc: usize = 0;
    let mut active: bool = false;
    begin_step(&mut pc, &mut active);
    all_ok &= check("begin_step: pc=1, active=true", pc == 1 && active);
    complete_step(&mut pc, &mut active);
    all_ok &= check("complete_step: pc=1, active=false", pc == 1 && !active);
    // expected_state is a spec function; runtime callable would need a wrapper.
    // Skip direct call; existence verified at compile time.
    let _ = (READY, RUNNING, COMPLETED, NOT_READY, expected_state);

    if all_ok {
        println!("KAT_RESULT: SUCCESS (1 bounded modality witness)");
        std::process::exit(0);
    } else {
        println!("KAT_RESULT: FAIL");
        std::process::exit(1);
    }
}
