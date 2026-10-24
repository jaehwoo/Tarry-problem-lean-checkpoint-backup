"""Generate checkpoint211 compiled queries; do not execute or certify them.

The ordered unit list is read from tools/checkpoint211_units.json, either a
JSON list or an object with a `units` list. Run this only after that list and
the new module sources are final. The unchanged checkpoint210 dependency
baseline is reused after checking the checkpoint211 starting source hashes.
This script never edits the root module, manuscript, or persistent checklist.
"""
from pathlib import Path
import hashlib
import json
import re
import sys

from checkpoint100_make_audit import strip_comments

P = Path(__file__).resolve().parents[1]


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def declaration_rows(unit):
    path = P / 'PaperILean' / f'{unit}.lean'
    text = strip_comments(path.read_text())
    rows = []
    stack = []
    for line_no, line in enumerate(text.splitlines(), 1):
        stripped = line.strip()
        namespace = re.fullmatch(r'namespace\s+(\S+)', stripped)
        if namespace:
            stack.append(('namespace', namespace[1]))
            continue
        section = re.fullmatch(r'(?:noncomputable\s+)?section(?:\s+(\S+))?', stripped)
        if section:
            stack.append(('section', section[1] or ''))
            continue
        end = re.fullmatch(r'end(?:\s+(\S+))?', stripped)
        if end:
            if not stack:
                raise ValueError(f'{unit}:{line_no}: unmatched end')
            kind, label = stack.pop()
            if end[1] and end[1] != label:
                raise ValueError(f'{unit}:{line_no}: named end requires parser review')
            continue
        match = re.match(
            r'^(?:@\[[^\]]+\]\s*)?'
            r'(?P<mods>(?:(?:private|protected|noncomputable|unsafe|partial)\s+)*)'
            r'(?P<kind>theorem|lemma|def|abbrev|structure|opaque|inductive)\s+'
            r'(?P<name>[^\s({:=]+)', stripped)
        if not match:
            continue
        if any(mod in match['mods'].split() for mod in ['private', 'unsafe', 'partial']):
            raise ValueError(f'{unit}:{line_no}: explicit scope review required for {stripped}')
        if match['kind'] in {'opaque', 'inductive'}:
            raise ValueError(f'{unit}:{line_no}: explicit scope review required for {stripped}')
        name = match['name']
        if name.startswith('_root_.'):
            name = name.removeprefix('_root_.')
        else:
            name = '.'.join([n for k, n in stack if k == 'namespace'] + [name])
        if not name.startswith('PaperI.'):
            raise ValueError(f'{unit}:{line_no}: unexpected declaration namespace: {name}')
        origin = 'new original-route proof work in checkpoint211'
        rows.append(dict(name=name, kind=match['kind'], module=unit, line=line_no,
                         source_sha256=sha(path), origin=origin))
    if not rows:
        raise ValueError(f'No declarations identified in {unit}')
    return rows


def main():
    units_path = P / 'tools/checkpoint211_units.json'
    if not units_path.exists():
        raise FileNotFoundError('Create tools/checkpoint211_units.json with the final ordered module list first')
    units_data = json.loads(units_path.read_text())
    units = units_data['units'] if isinstance(units_data, dict) else units_data
    if '--recovery' in sys.argv:
        units = units[:5]
    if not isinstance(units, list) or not units or len(set(units)) != len(units):
        raise ValueError('The units must be a nonempty list without duplicates')
    if not all(isinstance(u, str) and re.fullmatch(r'[A-Za-z][A-Za-z0-9_]*', u) for u in units):
        raise ValueError('Use simple Lean module basenames, without paths or PaperILean prefixes')

    baseline_path = P / 'evidence/checkpoint_211_baseline.json'
    baseline = json.loads(baseline_path.read_text())
    checked_baseline = {}
    for rel, expected in baseline.items():
        # The integration root may gain imports; all inherited theorem source,
        # manuscripts, pinning and policy files must stay byte-identical.
        if rel == 'PaperILean.lean':
            continue
        actual = sha(P / rel)
        if actual != expected:
            raise AssertionError(('Unchanged dependency baseline cannot be reused', rel, expected, actual))
        checked_baseline[rel] = actual

    rows = [row for unit in units for row in declaration_rows(unit)]
    names = {row['name'] for row in rows}
    if len(names) != len(rows):
        raise ValueError('Duplicate declaration names in audit scope')
    inherited_path = P / 'reports/Checkpoint210_KernelProjectDependencies.json'
    inherited = json.loads(inherited_path.read_text())
    dependencies = {row['declaration']: row['direct_project_dependencies'] for row in inherited}
    inherited_names_set = set(dependencies)
    while True:
        good = {n for n in inherited_names_set if set(dependencies[n] if isinstance(dependencies[n], list) else dependencies[n].split(';')) <= inherited_names_set}
        if good == inherited_names_set: break
        inherited_names_set = good
    inherited_names = sorted(inherited_names_set)
    # Only reuse metadata whose entire project closure is represented. Other
    # inherited names are expanded if the new roots actually reach them.

    if len(set(inherited_names)) != len(inherited_names):
        raise ValueError('Duplicate names in checkpoint210 dependency baseline')
    if names.intersection(inherited_names):
        raise ValueError('New211 roots overlap an inherited210 kernel declaration')

    registry = json.loads((P / 'reports/PublishedAssumptions_Contracts.json').read_text())
    contracts = list(dict.fromkeys(
        [r['declaration'] for r in registry]
        + ['PaperI.PublishedFiniteConnectedCover',
           'PaperI.PublishedSemialgebraicHardtTriviality',
           'PaperI.PublishedCompatibleSemialgebraicHardtTriviality',
           'PaperI.PublishedRealSemialgebraicity',
           'PaperI.PublishedEquispacedDividedDifferenceMeanValue']
        + [r['name'] for r in rows if r['kind'] == 'structure' and r['name'].split('.')[-1].startswith('Published')]
    ))
    new_contracts = [r['name'] for r in rows if r['kind'] == 'structure'
                     and r['name'].split('.')[-1].startswith('Published')]

    header = '\n'.join('import PaperILean.' + unit for unit in units)
    header += '\n\nset_option pp.funBinderTypes true\nset_option pp.piBinderTypes true\n'
    header += 'set_option pp.deepTerms true\nset_option pp.maxSteps 100000\n\n'
    header += '/-! Executable metadata queries, not proof certificates. -/\n\n'
    query = ''
    for row in rows:
        name = row['name']
        query += 'run_cmd Lean.logInfo ' + json.dumps('TYPE_BEGIN|' + name) + '\n'
        query += '#check ' + name + '\n'
        query += 'run_cmd Lean.logInfo ' + json.dumps('TYPE_END|' + name) + '\n'
        query += '#print axioms ' + name + '\n'
        if row['kind'] in {'def', 'abbrev', 'structure'}:
            query += 'run_cmd Lean.logInfo ' + json.dumps('BODY_BEGIN|' + name) + '\n'
            query += '#print ' + name + '\n'
            query += 'run_cmd Lean.logInfo ' + json.dumps('BODY_END|' + name) + '\n'

    meta = '''
open Lean Elab Command in
run_cmd do
  let names : Array Name := #[NAMES]
  let rec inputs : Expr → Array Name
    | .forallE _ domain body _ => domain.getUsedConstants ++ inputs body
    | _ => #[]
  let contracts : Array String := #[CONTRACTS]
  for name in names do
    let ci ← getConstInfo name
    for contract in contracts do
      if (inputs ci.type).any (fun n => n.toString == contract) then
        logInfo s!"EXPLICIT_PUBLISHED_INPUT|{name}|{contract}"
  let inherited : Std.HashSet String := Std.HashSet.ofList [INHERITED]
  let isProject := fun n : Name =>
    n.toString.startsWith "PaperI." || n.toString.startsWith "_private.PaperILean."
  let mut pending := names.toList
  let mut seen : List Name := []
  while !pending.isEmpty do
    let name := pending.head!
    pending := pending.tail!
    if !seen.contains name && !inherited.contains name.toString then
      seen := name :: seen
      let ci ← getConstInfo name
      let refs := ci.type.getUsedConstants ++ ((ci.value? true).map Expr.getUsedConstants).getD #[]
      let deps := (refs.toList.filter isProject).eraseDups
      logInfo s!"DEPENDENCIES|{name}|{String.intercalate ";" (deps.map Name.toString)}"
      let libs := (refs.toList.filter (fun n => !isProject n)).eraseDups
      logInfo s!"LIBRARY_REFERENCES|{name}|{String.intercalate ";" (libs.map Name.toString)}"
      pending := deps ++ pending
  logInfo s!"REUSED_UNCHANGED_DEPENDENCY_BASELINE|checkpoint210|{inherited.size}"
'''.replace('NAMES', ','.join('``' + r['name'] for r in rows)).replace(
        'CONTRACTS', ','.join(json.dumps(c) for c in contracts)).replace(
        'INHERITED', ','.join(json.dumps(n) for n in inherited_names))

    scope = dict(checkpoint=211, units=units, declarations=rows,
                 external_contracts=contracts, new_external_contracts=new_contracts,
                 body_query_roots=[r['name'] for r in rows if r['kind'] in {'def', 'abbrev', 'structure'}],
                 baseline_dependency_file=str(inherited_path.relative_to(P)),
                 baseline_dependency_sha256=sha(inherited_path),
                 baseline_dependency_records=len(inherited),
                 source_preservation_file=str(baseline_path.relative_to(P)),
                 source_preservation_sha256=sha(baseline_path),
                 unchanged_baseline_files_checked=len(checked_baseline),
                 generated_query_status='Not yet executed; no verification claim from generation')
    (P / 'tools/checkpoint211_scope.json').write_text(json.dumps(scope, indent=2) + '\n')
    (P / 'PaperILean/Batch211AxiomAudit.lean').write_text(header + query + meta)
    print(json.dumps(dict(declarations=len(rows), theorem_proofs=sum(
        r['kind'] in {'theorem', 'lemma'} for r in rows),
        definitions=sum(r['kind'] in {'def', 'abbrev'} for r in rows),
        structures=sum(r['kind'] == 'structure' for r in rows),
        bodies_and_contracts=len(scope['body_query_roots']), units=units,
        new_external_contracts=new_contracts, reused_baseline_records=len(inherited),
        compiled=False, root_modified=False), indent=2))


if __name__ == '__main__':
    main()

