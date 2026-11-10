"""Operator preparation for the identified native host engine and caller."""
# §AR-host-boundary.primitives: Build preparation is separate from per-request effects.
import hashlib
import json
import os
from pathlib import Path
import secrets
import shutil
import subprocess
import sys


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def sources(root):
    root = Path(root)
    files = [p for p in (root / "host").rglob("*.lean") if ".lake" not in p.parts]
    files += [root / "host" / name for name in ("lean-toolchain", "lake-manifest.json")]
    files += [root / "linux" / name for name in (
        "host_python.c", "host_python_primitives.c", "host_python_primitives.h", "host_primitives.c")]
    return {str(p.relative_to(root)): digest(p) for p in sorted(set(files))}


def prepare_key(stage):
    # §FS-host-boundary.publication: The key is host-only; the VM entry list never includes it.
    area = stage / ".leancage-private-host"
    area.mkdir(mode=0o700)
    os.setxattr(area, "user.leancage.private", b"\x01")
    key = area / "publication.key"
    descriptor = os.open(key, os.O_WRONLY | os.O_CREAT | os.O_EXCL | os.O_CLOEXEC, 0o600)
    with os.fdopen(descriptor, "wb") as target:
        target.write(secrets.token_bytes(32))
        target.flush()
        os.setxattr(target.fileno(), "user.leancage.private", b"\x01")
        os.fchmod(target.fileno(), 0o400)


def stage(root, destination, dependencies):
    root, destination = Path(root), Path(destination)
    filesystem_encoding = sys.getfilesystemencoding().lower().replace("_", "-")
    filesystem_errors = sys.getfilesystemencodeerrors()
    if filesystem_encoding not in ("utf-8", "utf8") or filesystem_errors != "surrogateescape":
        raise ValueError("the supported host interpreter requires UTF-8/surrogateescape filesystem paths")
    before = sources(root)
    subprocess.run(["lake", "build", "leancage-host"], cwd=root / "host", check=True)
    engine = root / "host/.lake/build/bin/leancage-host"
    shutil.copy2(engine, destination / "bin/leancage-host")
    include = Path("/usr/include/python3.12")
    if not (include / "Python.h").is_file():
        raise ValueError("the identified CPython 3.12 SDK is required for the abi3 caller")
    extension = destination / "python/leancage/_host.abi3.so"
    # A copied old generated alias is replaced only inside this newly owned stage.
    if extension.is_symlink():
        extension.unlink()
    subprocess.run(["cc", "-std=c11", "-O2", "-Wall", "-Wextra", "-Werror", "-shared", "-fPIC",
                    "-I" + str(include), str(root / "linux/host_python.c"),
                    str(root / "linux/host_python_primitives.c"), "-ldl",
                    "/lib/x86_64-linux-gnu/libcrypto.so.3", "-o", str(extension)],
                   check=True)
    for library in dependencies(engine):
        target = destination / "lib" / str(library).lstrip("/")
        target.parent.mkdir(parents=True, exist_ok=True)
        if target.exists() and digest(target) != digest(library):
            raise ValueError("host and controller runtime closures disagree: " + str(library))
        if not target.exists():
            shutil.copy2(library, target)
    notices = destination / "host-notices"
    notices.mkdir()
    for label, pattern in (("openssl", "libssl3*/copyright"), ("python-sdk", "python3.12*/copyright")):
        candidates = sorted(Path("/usr/share/doc").glob(pattern))
        if not candidates:
            raise ValueError("missing host dependency licensing record: " + label)
        for index, source in enumerate(candidates):
            shutil.copy2(source, notices / f"{label}-{index}.copyright")
    prepare_key(destination)
    current = sources(root)
    if current != before:
        raise ValueError("maintained host sources changed during native preparation")
    headers = {str(p): digest(p) for p in sorted(include.rglob("*.h"))}
    configuration = Path("/usr/include/x86_64-linux-gnu/python3.12/pyconfig.h")
    if configuration.is_file():
        headers[str(configuration)] = digest(configuration)
    return {
        "schema": "leancage-host-application-v1",
        "engine": "bin/leancage-host", "caller": "python/leancage/_host.abi3.so",
        "wire": "LCHREQ1/LCHRES1", "limited_python_api": "0x030b0000",
        "preparation_interpreter": {
            "version": sys.version, "executable": str(Path(sys.executable).resolve()),
            "filesystem_encoding": filesystem_encoding, "filesystem_errors": filesystem_errors},
        "source_sha256": current, "sdk_headers_sha256": headers,
        "private_key": ".leancage-private-host/publication.key",
        "private_attribute": {"name": "user.leancage.private", "value_hex": "01"},
        "authentication": "HMAC-SHA256; explicit bounded-message unforgeability contract",
    }


def install_source_alias(root, bundle):
    # §DA-host-engine.bootstrap: The loader-visible alias preserves repository results defaults.
    root, bundle = Path(root).absolute(), Path(bundle).absolute()
    link = root / "python/leancage/_host.abi3.so"
    if link.exists() or link.is_symlink():
        if not link.is_symlink():
            raise ValueError("refusing to replace a non-generated native source-package caller")
        selected = (link.parent / os.readlink(link)).resolve()
        if not selected.is_relative_to(root / ".tools"):
            raise ValueError("refusing to replace a native caller alias outside project-local artifacts")
    temporary = link.with_name(link.name + ".next")
    if temporary.exists() or temporary.is_symlink():
        raise ValueError("native alias preparation is already present")
    os.symlink(os.path.relpath(bundle / "python/leancage/_host.abi3.so", link.parent), temporary)
    os.replace(temporary, link)


def finish_development_bundle(root, bundle, dependencies):
    """Identify the same engine inside an isolated operator-owned integration bundle."""
    root, bundle = Path(root), Path(bundle)
    contract = stage(root, bundle, dependencies)
    manifest = json.loads((bundle / "manifest.json").read_bytes())
    manifest["host_application"] = contract
    manifest["source_sha256"].update(contract["source_sha256"])
    manifest["files"] = {str(p.relative_to(bundle)): digest(p) for p in sorted(bundle.rglob("*"))
                         if p.is_file() and p != bundle / "manifest.json"}
    (bundle / "manifest.json").write_text(json.dumps(manifest, indent=2, sort_keys=True) + "\n")
    return contract
