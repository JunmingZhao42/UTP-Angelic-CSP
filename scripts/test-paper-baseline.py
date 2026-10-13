"""Run with python3 scripts/test-paper-baseline.py; no Isabelle build required."""

import hashlib
import json
from pathlib import Path
import subprocess
import sys
import tempfile


repo = Path(__file__).resolve().parent.parent
command = [sys.executable, str(repo / "scripts/check-paper-baseline.py")]
with tempfile.TemporaryDirectory() as directory:
    output = Path(directory) / "snapshot"
    isabelle = Path(directory) / "isabelle"
    isabelle.write_text('#!/bin/sh\necho "build failed" >&2\nexit 7\n')
    isabelle.chmod(0o700)
    result = subprocess.run(command + ["--output", str(output), "--isabelle",
                                       str(isabelle)], capture_output=True, text=True)
    assert result.returncode == 7, result.stderr
    assert (output / "build.log").read_text() == "build failed\n"
    assert json.loads((output / "result.json").read_text())["exit_code"] == 7
    manifest = json.loads((output / "manifest.json").read_text())
    for relative, hashes in manifest["files"].items():
        data = (output / "project" / relative).read_bytes()
        assert hashlib.sha256(data).hexdigest() == hashes["snapshot_sha256"], relative
        if "source_sha256" in hashes:
            assert hashlib.sha256((repo / relative).read_bytes()).hexdigest() == hashes["source_sha256"]
            if relative not in manifest["transformed_files"]:
                assert data == (repo / relative).read_bytes(), relative
    for theory in ("utp_ades_parallel", "utp_rad_parallel", "utp_ap_parallel",
                   "utp_rad_representation"):
        assert not list((output / "project").rglob(theory + ".thy"))
        assert theory not in (output / "project/ROOT").read_text()
        for relative in manifest["transformed_files"]:
            assert theory not in (output / "project" / relative).read_text()
    # An existing snapshot must never be overwritten.
    assert subprocess.run(command + ["--output", str(output)],
                          capture_output=True).returncode != 0
print("Snapshot integrity and build failure propagation passed.")
