#!/usr/bin/env python3
"""Run the Lean-native Paper audit in a separate import driver."""
from contextlib import contextmanager
from pathlib import Path
import ctypes
import json
import os
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parent.parent


@contextmanager
def lean_lock():
    """Share the repository's Lean process mutex on Windows."""
    if os.name != 'nt':
        yield
        return
    kernel = ctypes.windll.kernel32
    kernel.CreateMutexW.argtypes = [ctypes.c_void_p, ctypes.c_int, ctypes.c_wchar_p]
    kernel.CreateMutexW.restype = ctypes.c_void_p
    kernel.WaitForSingleObject.argtypes = [ctypes.c_void_p, ctypes.c_uint32]
    kernel.ReleaseMutex.argtypes = [ctypes.c_void_p]
    kernel.CloseHandle.argtypes = [ctypes.c_void_p]
    handle = kernel.CreateMutexW(None, False, 'VegasCoreLedgerBuild')
    if not handle:
        raise OSError('Could not create Lean process mutex')
    try:
        if kernel.WaitForSingleObject(handle, 0xFFFFFFFF) not in (0, 0x80):
            raise OSError('Could not acquire Lean process mutex')
        yield
    finally:
        kernel.ReleaseMutex(handle)
        kernel.CloseHandle(handle)


def lean(args):
    result = subprocess.run(['lake', 'env', 'lean', *map(str, args)], cwd=ROOT,
                            text=True, encoding='utf-8', capture_output=True)
    if result.returncode:
        raise RuntimeError(result.stdout + result.stderr)
    return result.stdout


def audit_files(files, *, source_override=None):
    """Elaborate isolated cases in one native process; overrides are mutation tests only."""
    files = [Path(f).resolve() for f in files]
    with lean_lock():
        setup = ROOT / '.lake/build-stable/ir/Paper.setup.json'
        tool_setup = ROOT / '.lake/build-stable/ir/Tools/PaperAudit.setup.json'
        output = lean(['--setup', tool_setup, '--run', 'Tools/PaperAudit.lean', *files])
        headers = json.loads(output.strip().splitlines()[-1])
        imports = list(dict.fromkeys(name for h in headers for name in h['imports']))
        prefix = ['import ' + name for name in imports]
        if source_override is None:
            prefix.append('import Tools.PaperAudit')
        else:
            # The injected copy stays in an ignored driver; maintained files and
            # their compiled artifacts are never mutated.
            prefix.append(source_override.replace('import Lean\n', '', 1))
        prefix.append('open Lean Elab')
        commands = []
        for file in files:
            value = file.as_posix()
            literal = (' ++\n    ').join(json.dumps(value[i:i+60], ensure_ascii=False)
                for i in range(0, len(value), 60))
            commands.append('run_cmd do\n'
                '  let path := ' + literal + '\n'
                '  let report ← PaperAudit.run (← getEnv) (← getOptions) path\n'
                '  IO.println ("PAPER_AUDIT:" ++ (Lean.toJson report).compress)\n')
        directory = ROOT / '.lake/paper-audit'
        directory.mkdir(parents=True, exist_ok=True)
        with tempfile.TemporaryDirectory(prefix='driver-', dir=directory) as temp:
            assert Path(temp).resolve().is_relative_to(directory.resolve())
            driver = Path(temp) / 'AuditDriver.lean'
            driver.write_text('\n'.join(prefix + commands), encoding='utf-8')
            output = lean(['--setup', setup, driver])
        reports = [json.loads(line.removeprefix('PAPER_AUDIT:'))
                   for line in output.splitlines() if line.startswith('PAPER_AUDIT:')]
        if len(reports) != len(files):
            raise RuntimeError('Native audit did not report every input: ' + output)
        return reports


def main():
    reports = audit_files(sys.argv[1:] or [ROOT / 'Paper.lean'])
    for report in reports:
        for error in report['errors']:
            print(report['file'] + ': ' + error)
        if not report['errors']:
            print(f"{report['file']}: {len(report['results'])} authored proofs, "
                  f"{len(report['pins'])} exact guarded pins; native audit passed.")
    return int(any(r['errors'] for r in reports))


if __name__ == '__main__':
    raise SystemExit(main())
