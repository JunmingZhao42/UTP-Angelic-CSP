#!/usr/bin/env python3
"""Build a paper-only source snapshot without changing any Git worktree."""

import argparse
import hashlib
import io
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import tarfile
import tempfile


REPO = Path(__file__).resolve().parent.parent
PARALLEL = {
    "utp_ades_parallel", "utp_ades_parallel_generic", "utp_ades_parallel_normal",
    "utp_rad_parallel", "utp_rad_parallel_generic", "utp_rad_parallel_examples",
    "utp_ap_parallel", "utp_ap_parallel_generic", "utp_ap_parallel_examples",
}
THEORY_DIRS = (".", "angelic-designs", "reactive-angelic-designs",
               "angelic-processes")
AGGREGATES = {
    "angelic-designs/utp_ades.thy": "utp_ades_designs",
    "reactive-angelic-designs/utp_rad.thy":
        "utp_rad_nd utp_rad_examples utp_rad_ops_csp",
    "Angelic_CSP.thy":
        '"angelic-processes/utp_ap_nd" "angelic-processes/utp_ap_examples"',
}


def git(directory, *args):
    return subprocess.check_output(["git", "-C", str(directory), *args])


def digest(data):
    return hashlib.sha256(data).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path,
                        help="new directory for the retained snapshot and logs")
    parser.add_argument("--prepare-only", action="store_true")
    parser.add_argument("--isabelle", default=os.environ.get("ISABELLE", "isabelle"))
    parser.add_argument("--profile", default="utp-paper-baseline")
    parser.add_argument("--threads", type=int, default=4)
    args = parser.parse_args()
    if args.threads < 1:
        parser.error("--threads must be positive")
    if args.output:
        output = args.output.expanduser().resolve()
        output.mkdir(parents=True, exist_ok=False)
    else:
        output = Path(tempfile.mkdtemp(prefix="utp-paper-baseline-"))
    project = output / "project"
    project.mkdir()
    manifest = {
        "parent_head": git(REPO, "rev-parse", "HEAD").decode().strip(),
        "project_source": "working tree; parallel theories excluded",
        "dependency_source": "each checked-out submodule HEAD; local edits excluded",
        "dependencies": {}, "files": {}, "transformed_files": [],
    }

    # Copy current paper proofs verbatim, including untracked paper theories.
    for directory in THEORY_DIRS:
        for source in sorted((REPO / directory).glob("*.thy")):
            if source.stem in PARALLEL:
                continue
            relative = source.relative_to(REPO)
            destination = project / relative
            destination.parent.mkdir(parents=True, exist_ok=True)
            data = source.read_bytes()
            manifest["files"][str(relative)] = {"source_sha256": digest(data)}
            destination.write_bytes(data)

    # Only session registration and the three import-only aggregates change.
    root = (REPO / "ROOT").read_text()
    for theory in PARALLEL:
        pattern = r'(?m)^    (?:' + theory + r'|"(?:[^"\n]*/)?' + theory + r'")\n'
        root, count = re.subn(pattern, "", root)
        sources = sum((REPO / directory / (theory + ".thy")).is_file()
                      for directory in THEORY_DIRS)
        if sources > 1 or count != sources:
            raise RuntimeError(f"ROOT/source mismatch for {theory}: "
                               f"{count} registrations, {sources} files")
    (project / "ROOT").write_text(root)
    manifest["transformed_files"].append("ROOT")
    for relative, imports in AGGREGATES.items():
        path = project / relative
        original = path.read_text()
        # Fail closed if an aggregate has acquired definitions or proofs.
        if not re.search(r"\bbegin\s+end\s*$", original):
            raise RuntimeError(f"Expected an import-only aggregate: {relative}")
        replacement, count = re.subn(r"(?m)^  imports .+$", "  imports " + imports,
                                     original)
        if count != 1:
            raise RuntimeError(f"Expected one import line: {relative}")
        path.write_text(replacement)
        manifest["transformed_files"].append(relative)

    # git archive reads committed objects, including committed submodule-local
    # work awaiting a push, and never resets/stages/commits the user's checkout.
    deps = project / "deps"
    deps.mkdir()
    for name in ("ROOT", "ROOTS"):
        shutil.copyfile(REPO / "deps" / name, deps / name)
    modules = git(REPO, "config", "--file", ".gitmodules", "--get-regexp",
                  r"^submodule\..*\.path$").decode().splitlines()
    for entry in modules:
        relative = entry.split(maxsplit=1)[1]
        source = REPO / relative
        target = project / relative
        target.mkdir(parents=True)
        head = git(source, "rev-parse", "HEAD").decode().strip()
        parent = git(REPO, "ls-tree", "HEAD", relative).decode().split()[2]
        status = git(source, "status", "--porcelain=v1",
                     "--untracked-files=all").decode()
        manifest["dependencies"][relative] = {
            "head": head, "parent_gitlink": parent, "excluded_local_status": status,
        }
        archive = git(source, "archive", "--format=tar", head)
        with tarfile.open(fileobj=io.BytesIO(archive)) as archive_file:
            for member in archive_file.getmembers():
                path = Path(member.name)
                if path.is_absolute() or ".." in path.parts or not (
                        member.isfile() or member.isdir()):
                    raise RuntimeError(f"Unsupported archive member: {member.name}")
            archive_file.extractall(target)

    # Record the exact exported build inputs, not just Git revision labels.
    for path in sorted(project.rglob("*")):
        if path.is_file():
            entry = manifest["files"].setdefault(str(path.relative_to(project)), {})
            entry["snapshot_sha256"] = digest(path.read_bytes())
    manifest_path = output / "manifest.json"
    manifest_path.write_text(json.dumps(manifest, indent=2) + "\n")
    print(f"Paper snapshot: {project}", flush=True)
    print(f"Input manifest: {manifest_path}", flush=True)
    if args.prepare_only:
        return

    env = os.environ.copy()
    env.update(ISABELLE_IDENTIFIER=args.profile, PROJECT_DIR=str(project))
    command = [args.isabelle, "build", "-v", "-b", "-d", str(deps),
               "-d", str(project), "-o", "system_heaps=false", "-o",
               f"threads={args.threads}", "UTP-Angelic-CSP"]
    print("Build command: " + " ".join(command), flush=True)
    result = {"command": command, "profile": args.profile, "project": str(project)}
    with (output / "build.log").open("w") as log:
        with subprocess.Popen(command, env=env, cwd=project, stdout=subprocess.PIPE,
                              stderr=subprocess.STDOUT, text=True) as process:
            for line in process.stdout:
                print(line, end="", flush=True)
                log.write(line)
            result["exit_code"] = process.wait()
    (output / "result.json").write_text(json.dumps(result, indent=2) + "\n")
    raise SystemExit(result["exit_code"])


if __name__ == "__main__":
    main()
