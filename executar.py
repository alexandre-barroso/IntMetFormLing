import argparse
from concurrent.futures import ThreadPoolExecutor, as_completed
from datetime import datetime, timezone
import importlib.metadata
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import time
import uuid
from validar_execucoes import ROOT, DATA, sha, source_name, reports, failures
from validar_execucoes import dependency_closure, direct_dependencies, snapshot
from validar_execucoes import execution_errors, lean_admissions


def lean_order(paths):
    pending = {path.resolve() for path in paths}
    result = []
    while pending:
        ready = sorted(path for path in pending if not direct_dependencies(path) & pending)
        if not ready:
            raise ValueError('Dependências Lean circulares')
        result.extend(ready)
        pending.difference_update(ready)
    return result


def runtime_info(executable, system):
    info = {'executavel': executable, 'executavel_sha256': sha(Path(executable).resolve()),
            'python': sys.version, 'pacotes': {}}
    for package in ('sympy', 'numpy', 'scipy', 'mpmath'):
        try:
            info['pacotes'][package] = importlib.metadata.version(package)
        except importlib.metadata.PackageNotFoundError:
            pass
    if system == 'lean':
        answer = subprocess.run([executable, '--version'], capture_output=True, text=True, timeout=30)
        info['versao_lean'] = answer.stdout.strip()
    return info


def run_one(path, command, output, environment, timeout, runtime, compiled=None):
    name = source_name(path)
    closure = dependency_closure(path)
    before = snapshot(closure)
    imported_objects = {}
    if path.suffix == '.lean':
        if any(lean_admissions(item) for item in closure if item.suffix == '.lean'):
            raise ValueError('Admissão ou axioma local Lean: ' + name)
        for dependency in closure - {path}:
            if dependency.suffix == '.lean':
                target = compiled / dependency.relative_to(ROOT).with_suffix('.olean')
                if not target.is_file():
                    raise ValueError('Dependência Lean não compilada nesta execução: ' + str(target))
                imported_objects[str(target)] = sha(target)
    start = time.monotonic()
    started = datetime.now(timezone.utc).isoformat()
    log = output / (name.replace('/', '__') + '.log')
    timed_out = False
    with log.open('w') as stream:
        try:
            process = subprocess.run(command, cwd=ROOT, env=environment, stdout=stream,
                                     stderr=subprocess.STDOUT, timeout=timeout)
            status = process.returncode
        except subprocess.TimeoutExpired:
            status, timed_out = None, True
    raw = log.read_text(errors='replace')
    errors, parsed = execution_errors(path.suffix, status, raw)
    after = snapshot(dependency_closure(path))
    unchanged = before == after
    if not unchanged:
        errors.append('dependencia_alterada_durante_execucao')
    if timed_out:
        errors.append('timeout')
    artifacts = {}
    if path.suffix == '.lean':
        target = compiled / path.relative_to(ROOT).with_suffix('.olean')
        if not target.is_file():
            errors.append('objeto_lean_nao_produzido')
        else:
            artifacts[str(target)] = sha(target)
        for location, digest in imported_objects.items():
            if not Path(location).is_file() or sha(Path(location)) != digest:
                errors.append('objeto_lean_importado_alterado')
        artifacts.update(imported_objects)
    record = {'versao': 2, 'arquivo': name, 'sha256': before[name], 'comando': command,
              'inicio_utc': started, 'fim_utc': datetime.now(timezone.utc).isoformat(),
              'segundos': round(time.monotonic() - start, 3), 'codigo_saida': status,
              'timeout': timed_out, 'relatorios': parsed, 'log': str(log), 'log_sha256': sha(log),
              'aprovado': not errors, 'erros': sorted(set(errors)),
              'fontes_inalteradas_durante_execucao': unchanged, 'fontes_antes': before,
              'fontes_depois': after, 'dependencias': before, 'artefatos_lean': artifacts,
              'ambiente': runtime, 'executor_sha256': sha(Path(__file__)),
              'validador_sha256': sha(ROOT / 'validar_execucoes.py')}
    (output / (name.replace('/', '__') + '.json')).write_text(json.dumps(record, ensure_ascii=False, indent=2))
    print(json.dumps({key: record[key] for key in ('arquivo', 'segundos', 'codigo_saida', 'aprovado', 'erros')}, ensure_ascii=False), flush=True)
    return record


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--sistema', choices=['python', 'wolfram', 'lean'], required=True)
    parser.add_argument('--saida', type=Path, default=ROOT / '.execucoes')
    parser.add_argument('--jobs', type=int, default=1)
    parser.add_argument('--timeout', type=int, default=7200)
    parser.add_argument('--arquivo', action='append')
    parser.add_argument('--capitulo', type=int, choices=range(1, 10))
    parser.add_argument('--dependencias-lean', type=Path)
    args = parser.parse_args()
    if not __debug__ or os.environ.get('PYTHONOPTIMIZE'):
        raise RuntimeError('Asserções Python devem estar habilitadas')
    if args.jobs < 1 or args.timeout < 1:
        raise ValueError('Jobs e timeout devem ser positivos')
    run_id = datetime.now(timezone.utc).strftime('%Y%m%dT%H%M%S') + '-' + uuid.uuid4().hex[:8]
    output = args.saida.resolve() / run_id
    output.mkdir(parents=True)
    environment = os.environ.copy()
    environment['PYTHONPATH'] = str(ROOT) + os.pathsep + environment.get('PYTHONPATH', '')
    environment['PYTHONDONTWRITEBYTECODE'] = '1'
    suffix = {'python': '.py', 'wolfram': '.wl', 'lean': '.lean'}[args.sistema]
    available = {path.resolve() for path in ROOT.glob('capitulo_*/*' + suffix) if path.name not in DATA}
    if args.capitulo:
        available = {path for path in available if path.parent.name == f'capitulo_{args.capitulo:02}'}
    if args.arquivo:
        selected = {(ROOT / name).resolve() for name in args.arquivo}
        if not selected <= available:
            raise ValueError('Arquivo solicitado ausente ou não executável')
    else:
        selected = available
    if not selected:
        raise ValueError('Nenhum arquivo executável selecionado')
    commands = {}
    if args.sistema == 'lean':
        executable = shutil.which('lean')
        if not executable:
            raise RuntimeError('Lean não encontrado')
        paths = set().union(*(dependency_closure(path) for path in selected))
        paths = lean_order({path for path in paths if path.suffix == '.lean'})
        compiled = output / 'olean'
        compiled.mkdir()
        dependencies = []
        if args.dependencias_lean:
            dependencies = sorted(args.dependencias_lean.resolve().glob('*/.lake/build/lib/lean'))
            if not dependencies:
                raise RuntimeError('Bibliotecas Lean compiladas não encontradas')
        environment['LEAN_PATH'] = os.pathsep.join(map(str, [compiled, *dependencies])) + os.pathsep + environment.get('LEAN_PATH', '')
        runtime = runtime_info(executable, args.sistema)
        runtime['bibliotecas_lean'] = list(map(str, dependencies))
        records = []
        for path in paths:
            target = compiled / path.relative_to(ROOT).with_suffix('.olean')
            target.parent.mkdir(parents=True, exist_ok=True)
            command = [executable, '-o', str(target), str(path)]
            record = run_one(path, command, output, environment, args.timeout, runtime, compiled)
            records.append(record)
            if not record['aprovado']:
                break
    else:
        executable = sys.executable if args.sistema == 'python' else shutil.which('wolframscript')
        if not executable:
            raise RuntimeError('wolframscript não encontrado')
        runtime = runtime_info(executable, args.sistema)
        for path in sorted(selected):
            commands[path] = [executable, *([] if args.sistema == 'python' else ['-file']), str(path)]
        with ThreadPoolExecutor(max_workers=args.jobs) as pool:
            futures = [pool.submit(run_one, path, command, output, environment, args.timeout, runtime)
                       for path, command in commands.items()]
            records = [future.result() for future in as_completed(futures)]
    summary = {'sistema': args.sistema, 'arquivos': len(records),
               'aprovados': sum(record['aprovado'] for record in records),
               'selecionados': sorted(source_name(path) for path in selected),
               'execucoes': sorted(records, key=lambda item: item['arquivo'])}
    (output / (args.sistema + '.json')).write_text(json.dumps(summary, ensure_ascii=False, indent=2))
    print(json.dumps({'diretorio_resultados': str(output), 'arquivos': len(records), 'aprovados': summary['aprovados']}, ensure_ascii=False))
    return 0 if records and all(record['aprovado'] for record in records) else 1


if __name__ == '__main__':
    raise SystemExit(main())
