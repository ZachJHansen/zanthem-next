use {assert_cmd::Command, std::path::Path};

#[test]
fn verify_examples() {
    for example in Path::new(file!())
        .parent()
        .unwrap()
        .join("examples")
        .read_dir()
        .unwrap()
        .map(Result::unwrap)
        .filter(|entry| entry.metadata().unwrap().is_dir())
        .map(|entry| entry.path())
    {
        let problem_dir = example.join("problem");
        let stdout = example.join("stdout");
        let stderr = example.join("stderr");

        let mut cmd = Command::cargo_bin(env!("CARGO_PKG_NAME")).unwrap();
        let assert = cmd
            .arg("verify-alt")
            .arg(program)
            .arg("--with")
            .arg("sequential")
            .arg("-b")
            .arg("-s")
            .assert();

        assert
            .stdout(std::fs::read_to_string(stdout).unwrap())
            .stderr(std::fs::read_to_string(stderr).unwrap());
    }
}
