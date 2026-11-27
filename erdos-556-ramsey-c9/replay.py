"""Check the archived artefacts and replay any selected certificate."""

import argparse
import hashlib
import io
import json
from pathlib import Path
import subprocess
import sys
import tarfile
import tempfile
import zipfile


ROOT = Path(__file__).resolve().parent


def sha256(data):
    return hashlib.sha256(data).hexdigest()


def read_archive(index):
    archive = (ROOT / "certificates.tar.xz").read_bytes()
    if sha256(archive) != index["archive_sha256"]:
        raise ValueError("Certificate archive SHA-256 mismatch")
    expected = {
        item["path"]: item["sha256"]
        for proof in index["proofs"].values()
        for item in (proof["proof"], proof["reference_json"], proof["checker_zip"])
    }
    contents = {}
    with tarfile.open(fileobj=io.BytesIO(archive), mode="r:xz") as stream:
        for member in stream:
            if not member.isfile() or member.name not in expected or member.name in contents:
                raise ValueError(f"Unexpected archive member {member.name}")
            data = stream.extractfile(member).read()
            if sha256(data) != expected[member.name]:
                raise ValueError(f"SHA-256 mismatch for {member.name}")
            contents[member.name] = data
    if contents.keys() != expected.keys():
        raise ValueError("Certificate archive is missing indexed files")
    return contents


def replay(answer, proof, contents):
    package = contents[proof["checker_zip"]["path"]]
    with tempfile.TemporaryDirectory(prefix="ramsey-c9-") as tmp:
        directory = Path(tmp)
        with zipfile.ZipFile(io.BytesIO(package)) as source:
            source.extractall(directory)
        entry = directory / proof["entrypoint"]
        actual = subprocess.check_output([sys.executable, "-B", str(entry)], cwd=entry.parent)
    if actual != contents[proof["reference_json"]["path"]]:
        raise ValueError(f"{answer} output differs from the frozen certificate")
    print(f"{answer} reproduced byte for byte", flush=True)


def check_declared_dependencies(proofs, contents):
    count = 0
    for answer, proof in proofs.items():
        record = json.loads(contents[proof["reference_json"]["path"]])
        for prior in record.get("prior_answers", ()):
            if int(prior.removeprefix("answer-")) >= int(answer.removeprefix("answer-")):
                raise ValueError(f"{answer} declares a non-earlier prerequisite {prior}")
            count += 1
    print(f"Checked chronological order of {count} declared prerequisites", flush=True)


def main():
    index = json.loads((ROOT / "certificates.json").read_text(encoding="utf-8"))
    proofs = index["proofs"]
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument("--integrity-only", action="store_true")
    mode.add_argument("--all", action="store_true", help="replay all embedded checkers")
    mode.add_argument("--answers", nargs="+", choices=tuple(proofs), help="select checkers to replay")
    args = parser.parse_args()
    if not args.integrity_only and sys.version_info < (3, 10):
        parser.error("certificate replay requires Python 3.10 or later")
    contents = read_archive(index)
    print(f"Verified SHA-256 for the archive and its {len(contents)} files", flush=True)
    check_declared_dependencies(proofs, contents)
    if not args.integrity_only:
        for answer in proofs if args.all else args.answers or ("answer-51",):
            replay(answer, proofs[answer], contents)


if __name__ == "__main__":
    main()
