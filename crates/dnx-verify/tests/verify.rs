use dnx_verify::{
    austral_check, austral_side, check, check_pairs, load_manifest, nix_side, Expected, Verdict,
    VerifyError,
};
use logos::deltanet::{unf_hash_string, AgentKind, Net as KernelNet, Port};
use std::path::{Path, PathBuf};

/// A scratch directory with the two files for one pair.
fn pair_dir(tag: &str, nix: &str, austral: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!("dnx-verify-{}-{tag}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).unwrap();
    std::fs::write(dir.join("pair.nix"), nix).unwrap();
    std::fs::write(dir.join("Pair.aum"), austral).unwrap();
    dir
}

fn write_manifest(dir: &Path, body: &str) -> PathBuf {
    let path = dir.join("pairs.json");
    std::fs::write(&path, body).unwrap();
    path
}

/// Build the kernel-side net for a closed lambda term by hand, so the
/// converter's port mapping is checked against the encoding the kernel
/// itself reduces, not against a second call to the converter.
fn kernel_hash(build: impl FnOnce(&mut KernelNet)) -> String {
    let mut net = KernelNet::new();
    build(&mut net);
    unf_hash_string(&net).unwrap()
}

#[test]
fn abstraction_slots_match_the_kernel_encoding() {
    // `x: y: x` — outer Abs: slot1 = use of x, slot2 = inner lambda;
    // inner Abs: slot1 = unused y (Era), slot2 = x.
    let expected = kernel_hash(|net| {
        let outer = net.alloc_node(AgentKind::Abs);
        let inner = net.alloc_node(AgentKind::Abs);
        let era = net.alloc_node(AgentKind::Era);
        net.root = Port::new(outer, 0);
        net.wire(Port::new(outer, 1), Port::new(inner, 2));
        net.wire(Port::new(outer, 2), Port::principal(inner));
        net.wire(Port::new(inner, 1), Port::principal(era));
    });
    assert_eq!(nix_side("x: y: x").unwrap().hash, expected);
}

#[test]
fn application_ports_match_the_kernel_encoding() {
    // `f: x: f x` — App slot0 = function, slot1 = argument, slot2 = result.
    let expected = kernel_hash(|net| {
        let outer = net.alloc_node(AgentKind::Abs);
        let inner = net.alloc_node(AgentKind::Abs);
        let app = net.alloc_node(AgentKind::App);
        net.root = Port::new(outer, 0);
        net.wire(Port::new(outer, 1), Port::principal(app));
        net.wire(Port::new(outer, 2), Port::principal(inner));
        net.wire(Port::new(inner, 1), Port::new(app, 1));
        net.wire(Port::new(inner, 2), Port::new(app, 2));
    });
    assert_eq!(nix_side("f: x: f x").unwrap().hash, expected);
}

#[test]
fn duplicator_level_matches_the_kernel_encoding() {
    // `x: x x` — Abs slot2 = App result, Dup(1) principal = binder,
    // Dup aux0/aux1 = the two uses.
    let expected = kernel_hash(|net| {
        let abs = net.alloc_node(AgentKind::Abs);
        let app = net.alloc_node(AgentKind::App);
        let dup = net.alloc_node(AgentKind::Dup(1));
        net.root = Port::new(abs, 0);
        net.wire(Port::new(abs, 1), Port::principal(dup));
        net.wire(Port::new(abs, 2), Port::new(app, 2));
        net.wire(Port::principal(app), Port::new(dup, 1));
        net.wire(Port::new(app, 1), Port::new(dup, 2));
    });
    assert_eq!(nix_side("x: x x").unwrap().hash, expected);
}

fn equivalent(nix: &str, austral: &str) -> (String, usize) {
    match check(nix, austral) {
        Ok(Verdict::Equivalent {
            left,
            right,
            witness_pairs,
        }) => {
            assert_eq!(left.hash, right.hash);
            assert_eq!(left.agents, right.agents);
            (left.hash, witness_pairs)
        }
        other => panic!("expected equivalence for {nix:?} / {austral:?}, got {other:?}"),
    }
}

#[test]
fn closed_arithmetic_is_equivalent() {
    let (_, pairs) = equivalent("2 + 3", "(2 + 3)");
    assert_eq!(pairs, 1, "a literal normal form is one canonical node");
}

#[test]
fn expression_and_literal_share_the_normal_form() {
    let (a, _) = equivalent("2 + 3", "5");
    let (b, _) = equivalent("5", "5");
    assert_eq!(a, b, "both expressions normalize to the literal 5");
}

#[test]
fn boolean_comparison_is_equivalent() {
    equivalent("1 < 2", "(1 < 2)");
    equivalent("true", "true");
}

#[test]
fn different_values_are_rejected() {
    match check("2 + 3", "(2 + 4)") {
        Ok(Verdict::Different { left, right }) => {
            assert_ne!(left.hash, right.hash);
        }
        other => panic!("expected a mismatch, got {other:?}"),
    }
}

#[test]
fn float_literals_compare_by_bits() {
    equivalent("3.5", "3.5");
}

/// The smallest module that reduces to an `Entity` rather than a value.
const ENTITY_MODULE: &str = "module body Probe is\n\
       function main(): ExitCode is\n\
       return ExitSuccess();\n\
       end;\n\
       end module body.";

#[test]
fn entity_reductions_compare_structurally() {
    match austral_check(ENTITY_MODULE, ENTITY_MODULE) {
        Ok(Verdict::Equivalent {
            left,
            witness_pairs,
            ..
        }) => {
            assert_eq!(left.entities, vec!["ExitSuccess".to_string()]);
            assert!(witness_pairs >= 1, "the entity node is covered");
        }
        other => panic!("expected an equivalent entity net, got {other:?}"),
    }
}

#[test]
fn entity_names_are_part_of_the_identity() {
    let other = ENTITY_MODULE.replace("ExitSuccess", "ExitFailure");
    match austral_check(ENTITY_MODULE, &other) {
        Ok(Verdict::Different { left, right }) => {
            assert_ne!(left.hash, right.hash);
            assert_eq!(left.entities, vec!["ExitSuccess".to_string()]);
            assert_eq!(right.entities, vec!["ExitFailure".to_string()]);
        }
        other => panic!("expected a mismatch, got {other:?}"),
    }
}

#[test]
fn entity_names_are_reported_on_a_plain_austral_side() {
    let side = austral_side(ENTITY_MODULE).unwrap();
    assert!(side.value.is_none(), "an entity is not a scalar value");
    assert_eq!(side.entities, vec!["ExitSuccess".to_string()]);
    assert_eq!(side.agents, 1);
}

#[test]
fn cli_austral_check_handles_entities() {
    let dir = pair_dir("entities", "1", "(1)");
    std::fs::write(dir.join("Reference.aum"), ENTITY_MODULE).unwrap();
    std::fs::write(dir.join("Translated.aum"), ENTITY_MODULE).unwrap();
    let bin = env!("CARGO_BIN_EXE_dnx-verify");
    let output = std::process::Command::new(bin)
        .args([
            "austral-check",
            "--reference-file",
            dir.join("Reference.aum").to_str().unwrap(),
            "--austral-file",
            dir.join("Translated.aum").to_str().unwrap(),
        ])
        .output()
        .unwrap();
    assert_eq!(output.status.code(), Some(0), "{output:?}");
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(stdout.contains("entities=ExitSuccess"), "{stdout}");
}

#[test]
fn unsupported_nix_values_are_not_mismatches() {
    match check(r#""hello""#, "5") {
        Err(VerifyError::Unsupported(msg)) => assert!(msg.contains("string"), "{msg}"),
        other => panic!("expected Unsupported, got {other:?}"),
    }
}

#[test]
fn module_main_is_the_compared_term() {
    let module = "module body Probe is\n\
                  function add(x: Int64): Int64 is\n\
                      return (x + 1);\n\
                  end;\n\
                  function main(): Int64 is\n\
                      return add(41);\n\
                  end;\n\
              end module body.\n";
    let (_, pairs) = equivalent("(41 + 1)", module);
    assert_eq!(pairs, 1);
}

#[test]
fn manifest_reports_every_pair_without_stopping() {
    let dir = pair_dir("batch", "2 + 3", "(2 + 3)");
    std::fs::write(dir.join("bad.nix"), "2 + 3").unwrap();
    std::fs::write(dir.join("bad.aum"), "(2 + 4)").unwrap();
    let manifest = write_manifest(
        &dir,
        r#"{"pairs":[
             {"name":"good","nix":"pair.nix","austral":"Pair.aum"},
             {"name":"bad","nix":"bad.nix","austral":"bad.aum"},
             {"name":"missing","nix":"absent.nix","austral":"absent.aum"}
           ]}"#,
    );
    let pairs = load_manifest(&manifest).unwrap();
    let reports = check_pairs(&pairs, &dir);
    assert_eq!(reports.len(), 3);
    assert!(matches!(reports[0].verdict, Ok(Verdict::Equivalent { .. })));
    assert!(matches!(reports[1].verdict, Ok(Verdict::Different { .. })));
    assert!(matches!(reports[2].verdict, Err(VerifyError::Nix(_))));
    assert_eq!(reports[0].name, "good");
}

#[test]
fn manifest_accepts_a_bare_array_and_defaults_the_name() {
    let dir = pair_dir("bare", "1 < 2", "(1 < 2)");
    let manifest = write_manifest(&dir, r#"[{"nix":"pair.nix","austral":"Pair.aum"}]"#);
    let pairs = load_manifest(&manifest).unwrap();
    assert_eq!(pairs.len(), 1);
    let reports = check_pairs(&pairs, &dir);
    assert_eq!(reports[0].name, "pair");
    assert!(matches!(reports[0].verdict, Ok(Verdict::Equivalent { .. })));
}

#[test]
fn malformed_manifests_are_manifest_errors() {
    let dir = pair_dir("malformed", "1", "1");
    let empty = write_manifest(&dir, r#"{"pairs":[]}"#);
    assert!(load_manifest(&empty).is_err());
    let garbage = write_manifest(&dir, "not json");
    assert!(load_manifest(&garbage).is_err());
}

#[test]
fn cli_batch_aggregates_exit_codes() {
    let dir = pair_dir("cli", "2 + 3", "(2 + 3)");
    let good = write_manifest(&dir, r#"[{"nix":"pair.nix","austral":"Pair.aum"}]"#);
    let bin = env!("CARGO_BIN_EXE_dnx-verify");
    let status = std::process::Command::new(bin)
        .args(["check", "--manifest", good.to_str().unwrap(), "--json"])
        .output()
        .unwrap();
    assert!(status.status.success(), "{status:?}");

    // A missing file makes the batch exit 2 even though no pair is a mismatch.
    let broken = write_manifest(&dir, r#"[{"nix":"absent.nix","austral":"absent.aum"}]"#);
    let output = std::process::Command::new(bin)
        .args(["check", "--manifest", broken.to_str().unwrap()])
        .output()
        .unwrap();
    assert_eq!(output.status.code(), Some(2));
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(stdout.contains("[error]"), "{stdout}");
}

#[test]
fn committed_precedence_pair_reports_the_expected_mismatch() {
    let dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("examples");
    let pairs = load_manifest(&dir.join("pairs.json")).unwrap();
    let reports = check_pairs(&pairs, &dir);
    let precedence = reports
        .iter()
        .find(|report| report.name == "precedence")
        .expect("the precedence fixture is in the example manifest");
    assert_eq!(precedence.expected, Some(Expected::Different));
    assert!(precedence.passed(), "a declared difference is a pass");
    match &precedence.verdict {
        Ok(Verdict::Different { left, right }) => {
            assert_eq!(left.value.as_deref(), Some("7"), "Nix binds * before +");
            assert_eq!(
                right.value.as_deref(),
                Some("9"),
                "the AustralVM parser groups left to right"
            );
            assert_ne!(left.hash, right.hash);
        }
        other => panic!("the precedence fixture must stay a mismatch, got {other:?}"),
    }
}

#[test]
fn committed_examples_manifest_passes() {
    let dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("examples");
    let pairs = load_manifest(&dir.join("pairs.json")).unwrap();
    assert_eq!(pairs.len(), 5);
    let reports = check_pairs(&pairs, &dir);
    let different = reports
        .iter()
        .filter(|report| matches!(&report.verdict, Ok(Verdict::Different { .. })))
        .count();
    assert_eq!(different, 1, "only the precedence pair is a mismatch");
    for report in &reports {
        assert!(
            report.passed(),
            "{}: expected {:?}, got {:?}",
            report.name,
            report.expected,
            report.verdict
        );
    }
}

#[test]
fn expected_mismatch_makes_the_batch_pass() {
    let dir = pair_dir("expect-different", "2 + 3", "(2 + 4)");
    let manifest = write_manifest(
        &dir,
        r#"[{"nix":"pair.nix","austral":"Pair.aum","expect":"different"}]"#,
    );
    let pairs = load_manifest(&manifest).unwrap();
    assert_eq!(pairs[0].expect.as_deref(), Some("different"));
    assert!(check_pairs(&pairs, &dir)[0].passed());

    let bin = env!("CARGO_BIN_EXE_dnx-verify");
    let output = std::process::Command::new(bin)
        .args(["check", "--manifest", manifest.to_str().unwrap()])
        .output()
        .unwrap();
    assert_eq!(output.status.code(), Some(0), "{output:?}");
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        stdout.contains("different") && stdout.contains("(expected)"),
        "{stdout}"
    );
    assert!(stdout.contains("expectations met"), "{stdout}");
}

#[test]
fn unmet_expectations_fail_the_batch() {
    let dir = pair_dir("expect-unmet", "2 + 3", "(2 + 4)");
    let bin = env!("CARGO_BIN_EXE_dnx-verify");

    // A pair declared equivalent that differs is a failure.
    let expects_same = write_manifest(
        &dir,
        r#"[{"nix":"pair.nix","austral":"Pair.aum","expect":"equivalent"}]"#,
    );
    let output = std::process::Command::new(bin)
        .args(["check", "--manifest", expects_same.to_str().unwrap()])
        .output()
        .unwrap();
    assert_eq!(output.status.code(), Some(1), "{output:?}");
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(stdout.contains("[fail]"), "{stdout}");
    assert!(stdout.contains("(expected equivalent)"), "{stdout}");
    assert!(stdout.contains("1 unexpected"), "{stdout}");

    // A pair declared different that matches exactly is also a failure.
    std::fs::write(dir.join("Pair.aum"), "(2 + 3)").unwrap();
    let expects_diff = write_manifest(
        &dir,
        r#"[{"nix":"pair.nix","austral":"Pair.aum","expect":"different"}]"#,
    );
    let output = std::process::Command::new(bin)
        .args(["check", "--manifest", expects_diff.to_str().unwrap()])
        .output()
        .unwrap();
    assert_eq!(output.status.code(), Some(1), "{output:?}");
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(stdout.contains("[fail]"), "{stdout}");
    assert!(stdout.contains("(expected different)"), "{stdout}");
}

#[test]
fn unknown_expectation_is_a_manifest_error() {
    let dir = pair_dir("expect-unknown", "1", "1");
    let manifest = write_manifest(
        &dir,
        r#"[{"nix":"pair.nix","austral":"Pair.aum","expect":"maybe"}]"#,
    );
    let err = load_manifest(&manifest).unwrap_err();
    assert!(err.contains("unknown `expect`"), "{err}");

    let bin = env!("CARGO_BIN_EXE_dnx-verify");
    let output = std::process::Command::new(bin)
        .args(["check", "--manifest", manifest.to_str().unwrap()])
        .output()
        .unwrap();
    assert_eq!(output.status.code(), Some(2), "{output:?}");
}

#[test]
fn scan_regeneration_preserves_recorded_expectations() {
    use dnx_verify::{manifest_json, manifest_json_preserving, scan_dir};

    let dir = std::env::temp_dir().join(format!("dnx-verify-expect-scan-{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).unwrap();
    std::fs::write(dir.join("one.nix"), "2 + 3").unwrap();
    std::fs::write(dir.join("one.aum"), "(2 + 4)").unwrap();
    let manifest = write_manifest(
        &dir,
        r#"[{"name":"one","nix":"one.nix","austral":"one.aum","expect":"different"}]"#,
    );

    let report = scan_dir(&dir).unwrap();
    std::fs::write(
        &manifest,
        manifest_json_preserving(&report.pairs, &dir, &manifest),
    )
    .unwrap();
    let regenerated = load_manifest(&manifest).unwrap();
    assert_eq!(regenerated[0].expect.as_deref(), Some("different"));
    assert!(check_pairs(&regenerated, &dir)[0].passed());

    // A plain regeneration does not invent expectations.
    let plain: Vec<serde_json::Value> =
        serde_json::from_str::<serde_json::Value>(&manifest_json(&report.pairs, &dir))
            .unwrap()
            .get("pairs")
            .unwrap()
            .as_array()
            .unwrap()
            .clone();
    assert!(plain[0].get("expect").is_none());
}

#[test]
fn scan_pairs_by_stem_and_reports_unpaired() {
    use dnx_verify::scan_dir;

    let dir = std::env::temp_dir().join(format!("dnx-verify-scan-{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(dir.join("sub")).unwrap();
    for (path, body) in [
        ("a.nix", "2 + 3"),
        ("a.aum", "(2 + 3)"),
        ("sub/b.nix", "1 < 2"),
        ("sub/b.aum", "(1 < 2)"),
        ("orphan.nix", "1"),
        ("orphan.aum.bak", "1"),
        ("notes.txt", "ignored"),
    ] {
        std::fs::write(dir.join(path), body).unwrap();
    }
    std::fs::create_dir_all(dir.join("target")).unwrap();
    std::fs::write(dir.join("target/skip.nix"), "1").unwrap();

    let report = scan_dir(&dir).unwrap();
    let names: Vec<&str> = report.pairs.iter().map(|p| p.name.as_str()).collect();
    assert_eq!(names, vec!["a", "sub/b"]);
    assert_eq!(report.unpaired.len(), 1, "only orphan.nix is unpaired");
    assert!(report.unpaired[0].ends_with("orphan.nix"));
}

#[test]
fn generated_manifest_round_trips_through_batch_mode() {
    use dnx_verify::{manifest_json, scan_dir};

    let dir = std::env::temp_dir().join(format!("dnx-verify-gen-{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).unwrap();
    std::fs::write(dir.join("arith.nix"), "(2 + 3) * 4").unwrap();
    std::fs::write(dir.join("arith.aum"), "((2 + 3) * 4)").unwrap();
    std::fs::write(dir.join("bool.nix"), "1 < 2").unwrap();
    std::fs::write(dir.join("bool.aum"), "(1 < 2)").unwrap();

    let report = scan_dir(&dir).unwrap();
    let text = manifest_json(&report.pairs, &dir);
    let manifest_path = dir.join("pairs.json");
    std::fs::write(&manifest_path, format!("{text}\n")).unwrap();

    let pairs = load_manifest(&manifest_path).unwrap();
    assert_eq!(pairs.len(), 2);
    for report in check_pairs(&pairs, &dir) {
        assert!(
            matches!(&report.verdict, Ok(Verdict::Equivalent { .. })),
            "{}: {:?}",
            report.name,
            report.verdict
        );
    }
}

#[test]
fn generated_manifest_paths_are_relative_to_the_manifests_directory() {
    use dnx_verify::{manifest_json, scan_dir};

    let root = std::env::temp_dir().join(format!("dnx-verify-relocate-{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&root);
    let translations = root.join("translations");
    let manifests = root.join("manifests");
    std::fs::create_dir_all(&translations).unwrap();
    std::fs::create_dir_all(&manifests).unwrap();
    std::fs::write(translations.join("a.nix"), "2 + 3").unwrap();
    std::fs::write(translations.join("a.aum"), "(2 + 3)").unwrap();

    let report = scan_dir(&translations).unwrap();
    let manifest_path = manifests.join("pairs.json");
    std::fs::write(&manifest_path, manifest_json(&report.pairs, &manifests)).unwrap();

    let pairs = load_manifest(&manifest_path).unwrap();
    assert_eq!(pairs[0].nix, "../translations/a.nix");
    assert_eq!(pairs[0].austral, "../translations/a.aum");
    assert!(matches!(
        &check_pairs(&pairs, &manifests)[0].verdict,
        Ok(Verdict::Equivalent { .. })
    ));
}

#[test]
fn cli_scan_writes_the_default_manifest() {
    let dir = std::env::temp_dir().join(format!("dnx-verify-scan-cli-{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).unwrap();
    std::fs::write(dir.join("one.nix"), "2 + 3").unwrap();
    std::fs::write(dir.join("one.aum"), "(2 + 3)").unwrap();

    let bin = env!("CARGO_BIN_EXE_dnx-verify");
    let output = std::process::Command::new(bin)
        .args(["scan", "--dir", dir.to_str().unwrap()])
        .output()
        .unwrap();
    assert!(output.status.success(), "{output:?}");
    let generated = dir.join("pairs.json");
    assert!(generated.exists());
    let pairs = load_manifest(&generated).unwrap();
    assert_eq!(pairs.len(), 1);
    assert_eq!(pairs[0].nix, "one.nix");
    assert_eq!(pairs[0].austral, "one.aum");
}

#[test]
fn cli_scan_prints_stdout_manifest_with_relative_paths() {
    let dir = std::env::temp_dir().join(format!("dnx-verify-scan-stdout-{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(dir.join("sub")).unwrap();
    std::fs::write(dir.join("sub/one.nix"), "2 + 3").unwrap();
    std::fs::write(dir.join("sub/one.aum"), "(2 + 3)").unwrap();

    let bin = env!("CARGO_BIN_EXE_dnx-verify");
    let output = std::process::Command::new(bin)
        .current_dir(&dir)
        .args(["scan", "--dir", ".", "--output", "-"])
        .output()
        .unwrap();
    assert!(output.status.success(), "{output:?}");
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(stdout.contains("\"name\": \"sub/one\""), "{stdout}");
    assert!(stdout.contains("\"nix\": \"sub/one.nix\""), "{stdout}");
    assert!(
        !dir.join("pairs.json").exists(),
        "stdout mode writes nothing"
    );
}

#[test]
fn cli_scan_refuses_a_folder_with_no_pairs() {
    let dir = std::env::temp_dir().join(format!("dnx-verify-scan-empty-{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).unwrap();
    std::fs::write(dir.join("only.nix"), "1").unwrap();

    let bin = env!("CARGO_BIN_EXE_dnx-verify");
    let output = std::process::Command::new(bin)
        .args(["scan", "--dir", dir.to_str().unwrap()])
        .output()
        .unwrap();
    assert_eq!(output.status.code(), Some(2), "{output:?}");
    assert!(!dir.join("pairs.json").exists(), "nothing is written");
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(stderr.contains("unpaired"), "{stderr}");
    assert!(stderr.contains("no `X.nix`/`X.aum` pairs"), "{stderr}");
}

#[test]
fn nix_hash_is_stable_across_runs() {
    let a = nix_side("1 + 2 * 3").unwrap();
    let b = nix_side("1 + 2 * 3").unwrap();
    assert_eq!(a.hash, b.hash);
    assert_eq!(a.value.as_deref(), Some("7"));
}
