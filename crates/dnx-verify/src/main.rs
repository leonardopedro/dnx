//! `dnx-verify` — compare a Nix expression's DeltaNet with an AustralVM
//! expression's DeltaNet.
//!
//! ```text
//! dnx-verify check --nix '2 + 3' --austral '(2 + 3)'
//! dnx-verify check --nix-file default.nix --austral-file Main.aum
//! dnx-verify check --manifest pairs.json
//! dnx-verify austral-check --reference Ref.aum --austral-file Main.aum
//! dnx-verify scan --dir translations --output pairs.json
//! dnx-verify nix-hash --expr '1 + 2'
//! dnx-verify austral-hash --expr '(1 + 2)'
//! ```
//!
//! Exit status: 0 equivalent, 1 not equivalent, 2 could not compare. In batch
//! mode the status aggregates: any error is 2, else any pair that misses the
//! verdict its manifest requires is 1.

use dnx_verify::{
    austral_check, austral_side, check, check_pairs, load_manifest, manifest_json,
    manifest_json_preserving, nix_side, scan_dir, Expected, PairReport, Side, Verdict, VerifyError,
};
use std::process::ExitCode;

const USAGE: &str = "\
usage: dnx-verify check (--nix EXPR | --nix-file PATH) (--austral SRC | --austral-file PATH) [--json]
       dnx-verify check --manifest PATH [--json]
       dnx-verify austral-check (--reference SRC | --reference-file PATH) (--austral SRC | --austral-file PATH) [--json]
       dnx-verify nix-hash (--expr EXPR | --file PATH) [--json]
       dnx-verify austral-hash (--expr SRC | --file PATH) [--json]
       dnx-verify scan [--dir DIR] [--output PATH]

check          reduce both sides to DeltaNet normal forms and compare their
               canonical UNF digests (SHA-256, shared kernel serializer)
               with --manifest: check every pair it lists (see README); a
               pair's optional `expect` field records its required verdict
austral-check  compare two AustralVM sources structurally, including nets
               that still contain Entity names (a translation against a
               reference module)
nix-hash       print the Nix side's digest and reduced net size
austral-hash   print the AustralVM side's digest and reduced net size
scan           pair `foo.nix` with `foo.aum` by path stem under DIR and write
               a starter manifest (default DIR/pairs.json; `--output -` prints
               it, paths relative to the working directory)

Exit status: 0 equivalent, 1 not equivalent, 2 could not compare.
In batch mode: 2 if any pair could not be compared, else 1 if any pair misses
its expected verdict (with no `expect`, an equivalent verdict is expected).
The comparison is over the closed fragment shared by both encodings; an
unconvertible Nix net is reported as 'unsupported', never as a mismatch.";

fn main() -> ExitCode {
    match run(std::env::args().skip(1).collect()) {
        Ok(code) => code,
        Err(msg) => {
            eprintln!("dnx-verify: {msg}");
            eprintln!("{USAGE}");
            ExitCode::from(2)
        }
    }
}

fn run(args: Vec<String>) -> Result<ExitCode, String> {
    let Some(cmd) = args.first().map(String::as_str) else {
        return Err("expected a subcommand".into());
    };
    if matches!(cmd, "-h" | "--help" | "help") {
        println!("{USAGE}");
        return Ok(ExitCode::SUCCESS);
    }
    let flags = Flags::parse(&args[1..])?;
    match cmd {
        "check" => cmd_check(flags),
        "austral-check" => cmd_austral_check(flags),
        "nix-hash" => cmd_nix_hash(flags),
        "austral-hash" => cmd_austral_hash(flags),
        "scan" => cmd_scan(flags),
        other => Err(format!("unknown subcommand {other:?}")),
    }
}

struct Flags {
    nix: Option<String>,
    nix_file: Option<String>,
    austral: Option<String>,
    austral_file: Option<String>,
    reference: Option<String>,
    reference_file: Option<String>,
    dir: Option<String>,
    output: Option<String>,
    expr: Option<String>,
    file: Option<String>,
    manifest: Option<String>,
    json: bool,
    dump: bool,
}

impl Flags {
    fn parse(args: &[String]) -> Result<Self, String> {
        let mut f = Flags {
            nix: None,
            nix_file: None,
            austral: None,
            austral_file: None,
            reference: None,
            reference_file: None,
            dir: None,
            output: None,
            expr: None,
            file: None,
            manifest: None,
            json: false,
            dump: false,
        };
        let mut i = 0;
        while i < args.len() {
            let arg = args[i].as_str();
            let mut value = |name: &str| -> Result<String, String> {
                i += 1;
                args.get(i)
                    .cloned()
                    .ok_or_else(|| format!("{name} needs a value"))
            };
            match arg {
                "--nix" => f.nix = Some(value("--nix")?),
                "--nix-file" => f.nix_file = Some(value("--nix-file")?),
                "--austral" => f.austral = Some(value("--austral")?),
                "--austral-file" => f.austral_file = Some(value("--austral-file")?),
                "--reference" => f.reference = Some(value("--reference")?),
                "--reference-file" => f.reference_file = Some(value("--reference-file")?),
                "--dir" => f.dir = Some(value("--dir")?),
                "--output" => f.output = Some(value("--output")?),
                "--expr" => f.expr = Some(value("--expr")?),
                "--file" => f.file = Some(value("--file")?),
                "--manifest" => f.manifest = Some(value("--manifest")?),
                "--json" => f.json = true,
                "--dump" => f.dump = true,
                "-h" | "--help" => {
                    println!("{USAGE}");
                    std::process::exit(0);
                }
                other => return Err(format!("unknown flag {other:?}")),
            }
            i += 1;
        }
        Ok(f)
    }
}

fn read_source(inline: Option<String>, file: Option<String>, what: &str) -> Result<String, String> {
    match (inline, file) {
        (Some(s), None) => Ok(s),
        (None, Some(path)) => {
            std::fs::read_to_string(&path).map_err(|e| format!("{what}: read {path}: {e}"))
        }
        (Some(_), Some(_)) => Err(format!("{what}: give only one of the inline or file form")),
        (None, None) => Err(format!("{what}: missing input")),
    }
}

fn cmd_check(flags: Flags) -> Result<ExitCode, String> {
    if flags.reference.is_some() || flags.reference_file.is_some() {
        return Err("--reference is only valid with `austral-check`".into());
    }
    if let Some(manifest) = flags.manifest {
        if flags.nix.is_some()
            || flags.nix_file.is_some()
            || flags.austral.is_some()
            || flags.austral_file.is_some()
        {
            return Err("--manifest takes no --nix/--austral input".into());
        }
        return cmd_manifest(&manifest, flags.json);
    }
    let nix = read_source(flags.nix, flags.nix_file, "--nix")?;
    let austral = read_source(flags.austral, flags.austral_file, "--austral")?;
    Ok(report_verdict(
        check(&nix, &austral),
        "nix",
        "austral",
        flags.json,
    ))
}

fn cmd_austral_check(flags: Flags) -> Result<ExitCode, String> {
    reject_manifest(&flags)?;
    if flags.nix.is_some() || flags.nix_file.is_some() {
        return Err("austral-check takes two AustralVM sources, not a Nix expression".into());
    }
    let reference = read_source(flags.reference, flags.reference_file, "--reference")?;
    let translated = read_source(flags.austral, flags.austral_file, "--austral")?;
    Ok(report_verdict(
        austral_check(&reference, &translated),
        "reference",
        "translated",
        flags.json,
    ))
}

/// Print one verdict and map it to an exit status: 0 equivalent, 1 different,
/// 2 uncomparable. `left`/`right` name the two sides (<nix, austral> or
/// <reference, translated>).
fn report_verdict(
    verdict: Result<Verdict, VerifyError>,
    left_label: &str,
    right_label: &str,
    json: bool,
) -> ExitCode {
    match verdict {
        Ok(Verdict::Equivalent {
            left,
            right,
            witness_pairs,
        }) => {
            if json {
                println!(
                    "{{\"verdict\":\"equivalent\",\"witness_pairs\":{},\"{left_label}\":{},\"{right_label}\":{}}}",
                    witness_pairs,
                    json_side(&left),
                    json_side(&right)
                );
            } else {
                print_side(left_label, &left);
                print_side(right_label, &right);
                println!(
                    "verdict   equivalent (canonical nets identical; witness covers {witness_pairs} node(s))"
                );
            }
            ExitCode::SUCCESS
        }
        Ok(Verdict::Different { left, right }) => {
            if json {
                println!(
                    "{{\"verdict\":\"different\",\"{left_label}\":{},\"{right_label}\":{}}}",
                    json_side(&left),
                    json_side(&right)
                );
            } else {
                print_side(left_label, &left);
                print_side(right_label, &right);
                println!("verdict   NOT equivalent (canonical nets differ)");
            }
            ExitCode::from(1)
        }
        Err(e) => {
            report_error(json, &e);
            ExitCode::from(2)
        }
    }
}

fn cmd_scan(flags: Flags) -> Result<ExitCode, String> {
    reject_manifest(&flags)?;
    reject_reference(&flags)?;
    if flags.nix.is_some()
        || flags.nix_file.is_some()
        || flags.austral.is_some()
        || flags.austral_file.is_some()
        || flags.expr.is_some()
        || flags.file.is_some()
    {
        return Err("scan takes a --dir, not a Nix/AustralVM source".into());
    }
    let dir = flags.dir.unwrap_or_else(|| ".".into());
    let dir_path = std::path::Path::new(&dir);
    if !dir_path.is_dir() {
        return Err(format!("scan {dir}: not a directory"));
    }
    let report = scan_dir(dir_path)?;
    for path in &report.unpaired {
        eprintln!("dnx-verify: unpaired {} (no matching stem)", path.display());
    }
    if report.pairs.is_empty() {
        return Err(format!(
            "scan {dir}: no `X.nix`/`X.aum` pairs (nothing written)"
        ));
    }

    let output = flags
        .output
        .unwrap_or_else(|| dir_path.join("pairs.json").display().to_string());
    if output == "-" {
        println!(
            "{}",
            manifest_json(&report.pairs, std::path::Path::new("."))
        );
    } else {
        let output_path = std::path::Path::new(&output);
        let base = output_path
            .parent()
            .filter(|p| !p.as_os_str().is_empty())
            .unwrap_or_else(|| std::path::Path::new("."));
        let text = manifest_json_preserving(&report.pairs, base, output_path);
        std::fs::write(output_path, format!("{text}\n"))
            .map_err(|e| format!("write {output}: {e}"))?;
        println!("wrote {} pair(s) to {output}", report.pairs.len());
    }
    Ok(ExitCode::SUCCESS)
}

fn cmd_nix_hash(flags: Flags) -> Result<ExitCode, String> {
    reject_manifest(&flags)?;
    reject_reference(&flags)?;
    let expr = read_source(flags.expr, flags.file, "--expr")?;
    match nix_side(&expr) {
        Ok(side) => {
            if flags.json {
                println!("{}", json_side(&side));
            } else {
                print_side("nix", &side);
                if flags.dump {
                    dump_net(&side);
                }
            }
            Ok(ExitCode::SUCCESS)
        }
        Err(e) => {
            report_error(flags.json, &e);
            Ok(ExitCode::from(2))
        }
    }
}

fn cmd_austral_hash(flags: Flags) -> Result<ExitCode, String> {
    reject_manifest(&flags)?;
    reject_reference(&flags)?;
    let source = read_source(flags.expr, flags.file, "--expr")?;
    match austral_side(&source) {
        Ok(side) => {
            if flags.json {
                println!("{}", json_side(&side));
            } else {
                print_side("austral", &side);
                if flags.dump {
                    dump_net(&side);
                }
            }
            Ok(ExitCode::SUCCESS)
        }
        Err(e) => {
            report_error(flags.json, &e);
            Ok(ExitCode::from(2))
        }
    }
}

fn dump_net(side: &Side) {
    for (id, node) in side.net.nodes.iter().enumerate() {
        let Some(node) = node else { continue };
        if node.freed {
            continue;
        }
        let ports: Vec<String> = node
            .ports
            .iter()
            .enumerate()
            .map(|(slot, p)| match p {
                Some(p) => format!("{slot}:{}.{}", p.node, p.slot),
                None => format!("{slot}:_"),
            })
            .collect();
        println!(
            "  node {id:<4} {:<12} {}",
            format!("{}", node.kind),
            ports.join(" ")
        );
    }
    println!("  root      {}.{}", side.net.root.node, side.net.root.slot);
}

fn reject_manifest(flags: &Flags) -> Result<(), String> {
    match flags.manifest {
        Some(_) => Err("--manifest is only valid with `check`".into()),
        None => Ok(()),
    }
}

fn reject_reference(flags: &Flags) -> Result<(), String> {
    if flags.reference.is_some() || flags.reference_file.is_some() {
        Err("--reference is only valid with `austral-check`".into())
    } else {
        Ok(())
    }
}

fn cmd_manifest(path: &str, json: bool) -> Result<ExitCode, String> {
    let pairs = load_manifest(std::path::Path::new(path))?;
    let base = std::path::Path::new(path)
        .parent()
        .filter(|p| !p.as_os_str().is_empty())
        .unwrap_or_else(|| std::path::Path::new("."));
    let reports = check_pairs(&pairs, base);

    let mut equivalent = 0usize;
    let mut different = 0usize;
    let mut errors = 0usize;
    let mut declared = 0usize;
    let mut unexpected = 0usize;
    for report in &reports {
        match &report.verdict {
            Ok(Verdict::Equivalent { .. }) => equivalent += 1,
            Ok(Verdict::Different { .. }) => different += 1,
            Err(_) => errors += 1,
        }
        if report.expected.is_some() {
            declared += 1;
            if report.is_unexpected() {
                unexpected += 1;
            }
        }
    }

    if json {
        let entries: Vec<String> = reports.iter().map(json_report).collect();
        println!(
            "{{\"pairs\":[{}],\"summary\":{{\"total\":{},\"equivalent\":{},\"different\":{},\"error\":{},\"declared\":{declared},\"unexpected\":{unexpected}}}}}",
            entries.join(","),
            reports.len(),
            equivalent,
            different,
            errors
        );
    } else {
        for report in &reports {
            print_report(report);
        }
        let mut line = format!(
            "{} pair(s): {equivalent} equivalent, {different} different, {errors} error(s)",
            reports.len()
        );
        if declared > 0 {
            if unexpected > 0 {
                line.push_str(&format!("; {unexpected} unexpected"));
            } else {
                line.push_str("; expectations met");
            }
        }
        println!("{line}");
    }

    Ok(if errors > 0 {
        ExitCode::from(2)
    } else if reports.iter().all(|report| report.passed()) {
        ExitCode::SUCCESS
    } else {
        ExitCode::from(1)
    })
}

fn print_report(report: &PairReport) {
    let name = &report.name;
    let label = if report.passed() { "[ok]" } else { "[fail]" };
    match &report.verdict {
        Ok(Verdict::Equivalent {
            left,
            witness_pairs,
            ..
        }) => {
            let note = match report.expected {
                Some(Expected::Different) => "  (expected different)",
                _ => "",
            };
            println!(
                "{label:<9}{name:<24} equivalent  {}  witness={witness_pairs}{note}",
                left.hash
            );
        }
        Ok(Verdict::Different { left, right }) => {
            let note = match report.expected {
                Some(Expected::Different) => "  (expected)",
                Some(Expected::Equivalent) => "  (expected equivalent)",
                None => "",
            };
            println!(
                "{label:<9}{name:<24} different   nix={} austral={}{note}",
                left.hash, right.hash
            );
        }
        Err(e) => println!("[error]  {name:<24} {e}"),
    }
}

fn json_report(report: &PairReport) -> String {
    let name = json_escape(&report.name);
    let expected = match report.expected {
        Some(expected) => format!(",\"expected\":\"{}\"", expected.as_str()),
        None => String::new(),
    };
    match &report.verdict {
        Ok(Verdict::Equivalent {
            left,
            right,
            witness_pairs,
        }) => format!(
            "{{\"name\":\"{name}\",\"verdict\":\"equivalent\",\"passed\":{}{expected},\"witness_pairs\":{witness_pairs},\"nix\":{},\"austral\":{}}}",
            report.passed(),
            json_side(left),
            json_side(right)
        ),
        Ok(Verdict::Different { left, right }) => format!(
            "{{\"name\":\"{name}\",\"verdict\":\"different\",\"passed\":{}{expected},\"nix\":{},\"austral\":{}}}",
            report.passed(),
            json_side(left),
            json_side(right)
        ),
        Err(e) => format!(
            "{{\"name\":\"{name}\",\"verdict\":\"error\",\"passed\":false{expected},\"error\":\"{}\"}}",
            json_escape(&e.to_string())
        ),
    }
}

fn print_side(label: &str, side: &Side) {
    let value = side.value.as_deref().unwrap_or("-");
    let entities = if side.entities.is_empty() {
        String::new()
    } else {
        format!("  entities={}", side.entities.join(","))
    };
    println!(
        "{label:<9} {}  agents={}  value={value}{entities}",
        side.hash, side.agents
    );
}

fn report_error(json: bool, e: &VerifyError) {
    if json {
        println!(
            "{{\"verdict\":\"error\",\"error\":\"{}\"}}",
            json_escape(&e.to_string())
        );
    } else {
        eprintln!("dnx-verify: {e}");
    }
}

fn json_side(side: &Side) -> String {
    let entities: Vec<String> = side
        .entities
        .iter()
        .map(|e| format!("\"{}\"", json_escape(e)))
        .collect();
    format!(
        "{{\"unf_hash\":\"{}\",\"agents\":{},\"value\":{},\"entities\":[{}]}}",
        side.hash,
        side.agents,
        match &side.value {
            Some(v) => format!("\"{}\"", json_escape(v)),
            None => "null".into(),
        },
        entities.join(",")
    )
}

fn json_escape(s: &str) -> String {
    let mut out = String::with_capacity(s.len());
    for c in s.chars() {
        match c {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            c if (c as u32) < 0x20 => out.push_str(&format!("\\u{:04x}", c as u32)),
            c => out.push(c),
        }
    }
    out
}
