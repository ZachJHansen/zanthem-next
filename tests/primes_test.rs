use assert_cmd::Command;

#[test]
fn help_cmd() {
    let mut cmd = Command::new("anthem")
        .env("PATH", "/home/zachhansen/Desktop/anthem-next/target/debug")
        .args(&["--help"])
        .ok();
    assert!(cmd.is_ok());
}

#[test]
fn verify_graph_coloring_cmd() {
    let mut cmd = Command::new("anthem")
        .env("PATH", "/home/zachhansen/Desktop/anthem-next/target/debug")
        .args(&["verify-alt", "examples/graph-coloring", "--with", "sequential"])
        .ok();
    assert!(cmd.is_ok());
}
