#!/usr/bin/env python3
"""Run the Lean-native Paper audit in a separate import driver."""
from pathlib import Path
import json
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parent.parent


LEAN_TIMEOUT_SECONDS = 180


def lean(args):
    try:
        result = subprocess.run(['lake', 'env', 'lean', *map(str, args)], cwd=ROOT,
                                text=True, encoding='utf-8', capture_output=True,
                                timeout=LEAN_TIMEOUT_SECONDS)
    except subprocess.TimeoutExpired as error:
        raise RuntimeError(f'Lean audit exceeded {LEAN_TIMEOUT_SECONDS} seconds') from error
    if result.returncode:
        raise RuntimeError(result.stdout + result.stderr)
    return result.stdout


def ensure_fresh_build():
    """Refuse to audit proofs against missing or outdated target artifacts."""
    result = subprocess.run(['lake', '--wfail', 'build', '--no-build', 'Paper', 'Tools'], cwd=ROOT,
                            text=True, encoding='utf-8', capture_output=True,
                            timeout=LEAN_TIMEOUT_SECONDS)
    if result.returncode:
        raise RuntimeError('Paper/Tools build is missing or stale, or has warnings; '
                           'run lake --wfail build Paper Tools.\n'
                           + result.stdout + result.stderr)


def audit_files(files, *, source_override=None):
    """Use each exact import header and its pristine environment; overrides test mutations."""
    ensure_fresh_build()
    files = [Path(f).resolve() for f in files]
    setup = ROOT / '.lake/build-stable/ir/Paper.setup.json'
    tool_setup = ROOT / '.lake/build-stable/ir/Tools/PaperAudit.setup.json'
    print(f'Auditing {len(files)} file(s); Lean calls have a '
          f'{LEAN_TIMEOUT_SECONDS}s timeout.', file=sys.stderr, flush=True)
    output = lean(['--setup', tool_setup, '--run', 'Tools/PaperAudit.lean', *files])
    headers = json.loads(output.strip().splitlines()[-1])
    groups = {}
    for item in headers:
        file = Path(item['file'])
        header = file.read_text(encoding='utf-8').encode('utf-8')[:item['headerEnd']].decode('utf-8')
        groups.setdefault(header, []).append(file)
    tool = source_override if source_override is not None else (
        ROOT / 'Tools/PaperAudit.lean').read_text(encoding='utf-8')
    # Inline the validator after the target's imports. importEnv? retrieves the
    # pristine import environment, before any validator or driver declarations.
    # No tool import, merged headers, loader override or shared build writes occur.
    # Frontend APIs may arrive through meta imports. Only the validator runs in
    # a meta scope; each audited file gets a fresh ordinary command state below.
    tool = '@[expose] public meta section\n' + tool.split('\n@[expose] public section\n', 1)[1]
    directory = ROOT / '.lake/paper-audit'
    directory.mkdir(parents=True, exist_ok=True)
    reports = {}
    for header, group in groups.items():
        commands = []
        for file in group:
            value = file.as_posix()
            literal = (' ++\n    ').join(json.dumps(value[i:i+60], ensure_ascii=False)
                for i in range(0, len(value), 60))
            commands.append('run_cmd do\n'
                '  let path := ' + literal + '\n'
                '  let some env := (← getEnv).importEnv?\n'
                '    | throwError "missing pristine import environment"\n'
                '  let report ← PaperAudit.run env (← getOptions) path\n'
                '  IO.println ("PAPER_AUDIT:" ++ (Lean.toJson report).compress)\n')
        with tempfile.TemporaryDirectory(prefix='driver-', dir=directory) as temp:
            assert Path(temp).resolve().is_relative_to(directory.resolve())
            driver = Path(temp) / 'AuditDriver.lean'
            driver.write_text(header + '\n' + tool + '\n' +
                              '\n'.join(commands), encoding='utf-8')
            output = lean(['--setup', setup, driver])
        for line in output.splitlines():
            if line.startswith('PAPER_AUDIT:'):
                report = json.loads(line.removeprefix('PAPER_AUDIT:'))
                reports[Path(report['file'])] = report
    if set(reports) != set(files):
        raise RuntimeError('Native audit did not report every input')
    return [reports[file] for file in files]


def main():
    reports = audit_files(sys.argv[1:] or [ROOT / 'Paper.lean'])
    for report in reports:
        for error in report['errors']:
            print(report['file'] + ': ' + error)
        if not report['errors']:
            print(f"{report['file']}: {len(report['results'])} Prop-typed results, "
                  f"{len(report['pins'])} exact guarded pins; native audit passed.")
    return int(any(r['errors'] for r in reports))


if __name__ == '__main__':
    raise SystemExit(main())
