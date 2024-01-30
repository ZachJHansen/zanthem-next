use assert_cmd::Command;

#[test]
fn help_cmd_ok() {
    let mut cmd = Command::new("anthem")
        .env("PATH", "/home/zachhansen/Desktop/anthem-next/target/debug")
        .args(&["--help"])
        .ok();
    assert!(cmd.is_ok());
}

#[test]
fn translate_tau_graph_coloring_ok() {
    let mut cmd = Command::new("anthem")
        .env("PATH", "/home/zachhansen/Desktop/anthem-next/target/debug")
        .args(&[
            "translate",
            "examples/graph-coloring/coloring.lp",
            "--with",
            "tau-star",
        ])
        .ok();
    assert!(cmd.is_ok());
}

#[test]
fn translate_completion_graph_coloring_ok() {
    let mut cmd = Command::new("anthem")
        .env("PATH", "/home/zachhansen/Desktop/anthem-next/target/debug")
        .args(&[
            "translate",
            "examples/graph-coloring/coloring.lp",
            "--with",
            "completion",
        ])
        .ok();
    assert!(cmd.is_ok());
}

#[test]
fn verify_graph_coloring_ok() {
    let mut cmd = Command::new("anthem")
        .env("PATH", "/home/zachhansen/Desktop/anthem-next/target/debug")
        .args(&[
            "verify-alt",
            "examples/graph-coloring",
            "--with",
            "sequential",
        ])
        .ok();
    assert!(cmd.is_ok());
}

#[test]
fn translate_completion_graph_coloring() {
    let mut cmd = Command::new("anthem")
        .env("PATH", "/home/zachhansen/Desktop/anthem-next/target/debug")
        .args(&[
            "translate",
            "examples/graph-coloring/coloring.lp",
            "--with",
            "completion",
        ])
        .unwrap();
    let formulas = [
        "forall X Z1 Z2 (exists Z Z2 (Z = X and Z2 = Z1 and color(Z, Z2)) and exists Z Z1 (Z = X and Z1 = Z2 and color(Z, Z1)) and exists Z Z3 (Z = Z1 and Z3 = Z2 and Z != Z3) -> #false).",
        "forall X (exists Z (Z = X and vertex(Z)) and exists Z (Z = X and not aux(Z)) -> #false).",
        "forall X Y Z (exists Z Z1 (Z = X and Z1 = Y and edge(Z, Z1)) and exists Z1 Z2 (Z1 = X and Z2 = Z and color(Z1, Z2)) and exists Z1 Z2 (Z1 = Y and Z2 = Z and color(Z1, Z2)) -> #false).",
        "forall V1 V2 (color(V1, V2) <-> exists X Z (V1 = X and V2 = Z and (exists Z (Z = X and vertex(Z)) and exists Z1 (Z1 = Z and color(Z1))) and not not color(V1, V2))).", 
        "forall V1 (aux(V1) <-> exists X Z (V1 = X and (exists Z (Z = X and vertex(Z)) and exists Z1 (Z1 = Z and color(Z1)) and exists Z1 Z2 (Z1 = X and Z2 = Z and color(Z1, Z2)))))."
    ];
    let mut expected = formulas.join("\n");
    expected.push_str("\n\n");
    assert_eq!(String::from_utf8_lossy(&cmd.stdout), expected.to_string());
}
