// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

pub fn run_in_subprocess(test_name: &str) {
    use std::process::{Command, Stdio};
    use std::time::{Duration, Instant};

    let mut child = Command::new(std::env::current_exe().unwrap())
        .args(["--exact", test_name, "--nocapture"])
        .env("REGORUS_NATIVE_DEPTH_CHILD", "1")
        .env("RUST_MIN_STACK", "2097152")
        .stdout(Stdio::inherit())
        .stderr(Stdio::inherit())
        .spawn()
        .unwrap();
    let deadline = Instant::now() + Duration::from_secs(30);
    loop {
        if let Some(status) = child.try_wait().unwrap() {
            assert!(status.success(), "native-depth subprocess failed: {status}");
            break;
        }
        if Instant::now() >= deadline {
            child.kill().unwrap();
            child.wait().unwrap();
            panic!("native-depth subprocess exceeded deadline");
        }
        std::thread::sleep(Duration::from_millis(10));
    }
}
