"""Prospective completion reminders and full declared prompt-matrix admission checks.

This module neither runs models nor certifies task correctness. Future launchers
must call admit_runtime_prompt on the exact task message they will send.
"""
from itertools import product
import hashlib
import json
from pathlib import Path, PurePosixPath

VERSION = 'strict-completion-v1'
MARKER = '<!-- VeriBench strict-completion-v1 -->'


def digest(data):
    return hashlib.sha256(data).hexdigest()


def canonical(value):
    return json.dumps(value, sort_keys=True, separators=(',', ':'), allow_nan=False).encode()


def require(condition, message):
    if not condition:
        raise ValueError(message)


def unique(values, label):
    require(isinstance(values, list) and values, f'{label} must be a nonempty declared list')
    require(len({canonical(v) for v in values}) == len(values), f'Duplicate {label}')
    return values


def completion_reminder(output_paths):
    paths = unique(output_paths, 'output paths')
    for path in paths:
        require(isinstance(path, str) and path.startswith('/') and '\n' not in path
                and '`' not in path and '..' not in PurePosixPath(path).parts,
                'Each output path must be an explicit absolute sandbox path')
    return MARKER + '\n' + (
        '## Complete the entire assigned task\n\n'
        'Solve every task, file, question, and required part assigned in the supplied public instructions. '
        'Perform the work: a plan, partial demonstration, or promise to continue does not complete the assignment. '
        'Keep working through the entire assigned scope within the declared time, token, request, and tool limits; '
        'do not end early while required work remains and the permitted work can continue.\n\n'
        'Write and preserve the actual final Lean output on disk at every required path:\n'
        + ''.join(f'- `{path}`\n' for path in paths) + '\n'
        'Create a substantive on-disk implementation early, save progress throughout, then improve, prove, '
        'and check it. Do not spend the entire allowance only planning or reasoning while leaving the '
        'required files empty or unwritten. Preserve the actual files even when some obligations remain unfinished.\n\n'
        'Complete all implementations, executable examples, public checks, specifications, Pre/Post definitions, '
        'named claims, and proofs required by this task. Preserve the full required semantics and input domain. '
        'Requirements that the public task explicitly makes optional remain optional. Follow its existing proof '
        'and submission policy; do not drop or weaken obligations, invent claims, or describe unresolved proofs as complete.\n\n'
        'Use the authorized tools to run the declared Lean compiler and available public task checks, inspect their '
        'actual diagnostics, and repair the files within the original remaining budget. Check every required output '
        'before finishing. Save progress as you work and keep scratch probes separate from the submission. '
        'Use only the permitted public task inputs; do not seek hidden references or private evaluation material.\n\n'
        'If a declared limit is reached or a genuine blocker prevents further work, preserve the best actual files '
        'and state the exact unfinished parts and observed blocker. Report only artifacts written and checks actually '
        'run. Do not invent tool results, claim unproved facts, or label incomplete work as finished. '
        'A completed attempt and a correct solution are separate claims.\n')


def add_completion_reminder(prompt, output_paths):
    require(isinstance(prompt, str) and prompt.strip(), 'Nonempty public runtime prompt required')
    block = completion_reminder(output_paths)
    if MARKER in prompt:
        require(prompt.count(MARKER) == 1 and block in prompt, 'Conflicting or duplicate completion reminder')
        return prompt
    return prompt + '\n\n' + block


def expected_cells(plan):
    """Derive the entire Cartesian matrix from the caller's separately declared plan."""
    agents = unique(plan['agents'], 'agents')
    tasks = unique(plan['tasks'], 'tasks')
    seeds = unique(plan['seeds'], 'seeds')
    repetitions = unique(plan['repetitions'], 'repetitions')
    require(all(isinstance(a, str) and a for a in agents), 'Agent identities must be nonempty strings')
    require(all(type(s) is int or s is None for s in seeds), 'Declare integer seeds or explicit null')
    require(all(type(r) is int and r >= 0 for r in repetitions), 'Declare nonnegative integer repetitions')
    ids = [task['id'] for task in tasks]
    require(all(isinstance(t, str) and t for t in ids) and len(ids) == len(set(ids)), 'Duplicate or invalid task identity')
    for task in tasks:
        completion_reminder(task['output_paths'])
    require(set(plan['phases']) == set(agents), 'Every declared agent needs its phase schedule')
    cells = []
    for agent in agents:
        phases = unique(plan['phases'][agent], 'phases')
        require(phases == ['initial'] + [f'continuation_{i}' for i in range(1, len(phases))],
                'Declare initial and every consecutive continuation phase')
        cells += [dict(agent=agent, task=task, seed=seed, repetition=repetition, phase=phase)
                  for task, seed, repetition, phase in product(ids, seeds, repetitions, phases)]
    return cells


def key(row):
    return tuple(row[name] for name in ('agent', 'task', 'seed', 'repetition', 'phase'))


def build_bundle(plan, public_prompts, output):
    """Write a new ignored bundle; source rows contain public final task messages only."""
    cells = expected_cells(plan)
    require(isinstance(public_prompts, list), 'Public prompt rows required')
    index = {key(row): row for row in public_prompts}
    require(len(index) == len(public_prompts), 'Duplicate runtime prompt cell')
    require(set(index) == {key(cell) for cell in cells}, 'Missing or extra declared runtime prompt cells')
    for row in public_prompts:
        require(row.get('public_agent_input') is True, 'Only explicitly public agent prompts may be used')
        require(isinstance(row.get('prompt'), str) and row['prompt'].strip(), 'Empty runtime prompt')
    output = Path(output).absolute()
    require('private' in output.parts, 'Prompt bodies must remain in an ignored private bundle')
    output.mkdir(parents=True, exist_ok=False)
    paths = {task['id']: task['output_paths'] for task in plan['tasks']}
    rows = []
    for i, cell in enumerate(cells):
        source = index[key(cell)]['prompt']
        rendered = add_completion_reminder(source, paths[cell['task']])
        name = f'prompt_{i:06d}.txt'
        (output / name).write_text(rendered, encoding='utf-8')
        rows.append({**cell, 'path': name, 'source_prompt_sha256': digest(source.encode()),
                     'runtime_prompt_sha256': digest(rendered.encode())})
    manifest = {'schema_version': 1, 'completion_contract': VERSION,
                'utility_sha256': digest(Path(__file__).read_bytes()),
                'declared_plan_sha256': digest(canonical(plan)), 'plan': plan, 'prompts': rows}
    (output / 'manifest.json').write_bytes(canonical(manifest) + b'\n')
    return verify_bundle(output, plan)


def verify_bundle(bundle, expected_plan, *, expected_manifest_sha256=None):
    """The expected plan must come from the launch declaration, not the bundle itself."""
    bundle = Path(bundle)
    manifest_bytes = (bundle / 'manifest.json').read_bytes()
    if expected_manifest_sha256 is not None:
        require(digest(manifest_bytes) == expected_manifest_sha256, 'Frozen prompt manifest digest differs')
    manifest = json.loads(manifest_bytes)
    require(manifest['schema_version'] == 1, 'Unsupported prompt manifest schema')
    require(manifest['completion_contract'] == VERSION and manifest['utility_sha256'] == digest(Path(__file__).read_bytes()),
            'Completion utility/version changed')
    require(manifest['plan'] == expected_plan and manifest['declared_plan_sha256'] == digest(canonical(expected_plan)),
            'Bundle differs from the full declared launch plan')
    cells = expected_cells(expected_plan)
    rows = manifest['prompts']
    require(len(rows) == len(cells) and len({key(r) for r in rows}) == len(rows)
            and {key(r) for r in rows} == {key(c) for c in cells}, 'Incomplete or duplicate prompt matrix')
    require(len({r['path'] for r in rows}) == len(rows), 'Prompt files must bind distinct cells')
    require({p.name for p in bundle.glob('prompt_*.txt')} == {r['path'] for r in rows}, 'Prompt file inventory differs')
    outputs = {task['id']: task['output_paths'] for task in expected_plan['tasks']}
    for row in rows:
        path = Path(row['path'])
        require(not path.is_absolute() and len(path.parts) == 1, 'Prompt path escapes bundle')
        target = bundle / path
        require(not target.is_symlink(), 'Symlink prompt rejected')
        raw = target.read_bytes()
        require(digest(raw) == row['runtime_prompt_sha256'], 'Runtime prompt digest differs')
        text = raw.decode('utf-8')
        require(text.count(MARKER) == 1 and completion_reminder(outputs[row['task']]) in text,
                'Completion reminder absent or changed')
    return {'status': 'PASS', 'declared_cells': len(cells), 'manifest_sha256': digest((bundle / 'manifest.json').read_bytes()),
            'declared_plan_sha256': manifest['declared_plan_sha256'], 'completion_contract': VERSION}


def admit_runtime_prompt(bundle, expected_plan, cell, actual_prompt, *, expected_manifest_sha256):
    """Call immediately before the future launcher sends each initial/continuation message."""
    require(isinstance(expected_manifest_sha256, str) and len(expected_manifest_sha256) == 64,
            'Independently frozen manifest SHA256 required')
    receipt = verify_bundle(bundle, expected_plan, expected_manifest_sha256=expected_manifest_sha256)
    manifest = json.loads((Path(bundle) / 'manifest.json').read_text())
    matches = [r for r in manifest['prompts'] if key(r) == key(cell)]
    require(len(matches) == 1, 'Runtime cell is not in the full declared matrix')
    require(digest(actual_prompt.encode()) == matches[0]['runtime_prompt_sha256'],
            'Actual runtime message differs from admitted prompt')
    return {**receipt, 'cell': {name: cell[name] for name in ('agent', 'task', 'seed', 'repetition', 'phase')},
            'runtime_prompt_sha256': matches[0]['runtime_prompt_sha256']}
