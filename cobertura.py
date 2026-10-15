from pathlib import Path
import hashlib
import json
import re
import sys

ROOT = Path(__file__).resolve().parents[1]

PROSA_MATEMATICA = {
    7: [r"Aumentar \(b\) reduz a instabilidade dessa aproximação computacional; não amplia o corpus do qual as repetições foram retiradas."],
    8: ["A fonte também informa o mínimo cinco quando a substituição custa um.", "Em zero, os dois trechos se encontram, mas suas inclinações diferem: zero à esquerda e um à direita. A continuidade e a quina já estudadas passam a ter uma função na transformação de representações.", r"A norma ao quadrado é a soma dos quadrados das coordenadas. Para um par observado, \(p-y=p-1<0\), e a mudança aumenta o produto se \(v\ne0\). Para um par negativo, \(p-y=p>0\), e o reduz."],
    9: ["Muitos conjuntos diferentes de erros podem conduzir ao mesmo F1 arredondado."]
}

def normalized(value):
    return " ".join(value.split())

def without_comments(source):
    return re.sub(r"(?<!\\)%[^\n]*", lambda match: " " * len(match.group()), source)

def group_at(source, offset):
    if source[offset] != "{":
        raise ValueError(offset)
    depth = 1
    cursor = offset + 1
    while depth:
        if cursor >= len(source):
            raise ValueError("Unclosed group")
        if source[cursor] == "{" and source[cursor - 1] != "\\":
            depth += 1
        elif source[cursor] == "}" and source[cursor - 1] != "\\":
            depth -= 1
        cursor += 1
    return source[offset + 1:cursor - 1], cursor

def mathematical_occurrences(source):
    pattern = r"\\\((.*?)\\\)|\\\[(.*?)\\\]|(?<!\\)\$(?!\$)(.*?)(?<!\\)\$"
    for match in re.finditer(pattern, source, re.S):
        yield match.start(), "display" if match.group(2) is not None else "inline", next(value for value in match.groups() if value is not None)

def plot_occurrences(source):
    for match in re.finditer(r'\\addplot\b\+?',source):
        cursor=match.end()
        while cursor<len(source) and source[cursor].isspace():
            cursor+=1
        if cursor<len(source) and source[cursor]=='[':
            depth=1
            cursor+=1
            while cursor<len(source) and depth:
                if source[cursor]=='[' and source[cursor-1]!='\\':
                    depth+=1
                elif source[cursor]==']' and source[cursor-1]!='\\':
                    depth-=1
                cursor+=1
            if depth:
                raise ValueError('Unclosed plot options')
        while cursor<len(source) and source[cursor].isspace():
            cursor+=1
        kind='plot_function'
        if source.startswith('coordinates',cursor):
            kind='plot_coordinates'
            cursor+=len('coordinates')
            while cursor<len(source) and source[cursor].isspace():
                cursor+=1
        if cursor<len(source) and source[cursor]=='{':
            expression,_=group_at(source,cursor)
            yield match.start(),kind,expression

def collect():
    result = []
    for chapter in range(1, 10):
        path = ROOT / f"latex/capitulos/capitulo_{chapter:02}.tex"
        source = without_comments(path.read_text())
        topics = [(match.start(),match.group(1),hashlib.sha256(normalized(match.group(2)).encode()).hexdigest()) for match in re.finditer(r"\\begin\{topico\}\{([^}]+)\}(.*?)\\end\{topico\}",source,re.S)]

        def topic_at(offset):
            return next((topic for start, topic, digest in reversed(topics) if start < offset), None)

        def add(file, text, offset, kind, expression, topic):
            identity = f"c{chapter:02}.e{1 + sum(row['chapter'] == chapter for row in result):04}"
            result.append({"id": identity, "chapter": chapter, "topic": topic, "context_sha256":next((digest for start,key,digest in topics if key==topic),None), "file": str(file.relative_to(ROOT)), "source_file_sha256":hashlib.sha256(text.encode()).hexdigest(), "line": text[:offset].count("\n") + 1, "kind": kind, "expression": normalized(expression), "sha256": hashlib.sha256(expression.encode()).hexdigest()})

        for offset, kind, expression in mathematical_occurrences(source):
            add(path, source, offset, kind, expression, topic_at(offset))
        for match in re.finditer(r"\\begin\{tabular\}.*?\\end\{tabular\}|\\begin\{tableau\}.*?\\end\{tableau\}", source, re.S):
            add(path, source, match.start(), "table", match.group(), topic_at(match.start()))
        for call in re.finditer(r"\\figuratex\{([^}]+)\}", source):
            figure = ROOT / "latex/figures" / (call.group(1) + ".tex")
            drawing = without_comments(figure.read_text())
            for offset, kind, expression in mathematical_occurrences(drawing):
                add(figure, drawing, offset, "figure_" + kind, expression, topic_at(call.start()))
            for match in re.finditer(r"\\addplot(?:\[[^]]*\])?\s*(coordinates\s*)?\{", drawing):
                expression, _ = group_at(drawing, match.end() - 1)
                add(figure, drawing, match.start(), "plot_coordinates" if match.group(1) else "plot_function", expression, topic_at(call.start()))
        for call in re.finditer(r"\\figuratex\{([^}]+)\}", source):
            figure = ROOT / "latex/figures" / (call.group(1) + ".tex")
            drawing = without_comments(figure.read_text())
            add(figure, drawing, 0, "figure_semantics", drawing, topic_at(call.start()))
        for match in re.finditer(r"\\begin\{figure\}.*?\\end\{figure\}", source, re.S):
            add(path, source, match.start(), "figure_semantics", match.group(), topic_at(match.start()))
        for call in re.finditer(r"\\figuratex\{([^}]+)\}", source):
            figure=ROOT/'latex/figures'/(call.group(1)+'.tex')
            drawing=without_comments(figure.read_text())
            previous_offsets={match.start() for match in re.finditer(r"\\addplot(?:\[[^]]*\])?\s*(coordinates\s*)?\{",drawing)}
            for offset,kind,expression in plot_occurrences(drawing):
                if offset not in previous_offsets:
                    add(figure,drawing,offset,kind,expression,topic_at(call.start()))
            for match in re.finditer(r"\\begin\{tabular\}.*?\\end\{tabular\}|\\begin\{tableau\}.*?\\end\{tableau\}",drawing,re.S):
                add(figure,drawing,match.start(),'figure_table',match.group(),topic_at(call.start()))
        for claim in PROSA_MATEMATICA.get(chapter,[]):
            if source.count(claim)!=1:
                raise ValueError('Afirmação matemática em prosa ausente ou ambígua: '+claim)
            offset=source.index(claim)
            add(path,source,offset,'prose_claim',claim,topic_at(offset))
    return result

def load_manifest(chapter):
    import runpy
    return runpy.run_path(str(ROOT / f"scripts/capitulo_{chapter:02}/cobertura.py"))

def uncollected_math_sources(rows):
    collected={row['file'] for row in rows}
    pending=[ROOT/'latex/main.tex']
    visited=set()
    failures=[]
    while pending:
        path=pending.pop()
        if path in visited:
            continue
        visited.add(path)
        source=without_comments(path.read_text())
        relative=str(path.relative_to(ROOT))
        if relative not in collected and '/configuracao/' not in relative and list(mathematical_occurrences(source)):
            failures.append(relative)
        for match in re.finditer(r'\\(?:input|include)\{([^}]+)\}',source):
            if '#' in match.group(1):
                continue
            dependency=ROOT/'latex'/match.group(1)
            if not dependency.suffix:
                dependency=dependency.with_suffix('.tex')
            if dependency.is_file():
                pending.append(dependency)
    return sorted(failures)

def isolated_notation(expression):
    return re.fullmatch(r'(?:[A-Za-z]|\\(?:alpha|beta|gamma|delta|Delta|sigma|Sigma|theta|lambda|mu|nu|epsilon|varepsilon|phi|Phi|psi|omega|Omega|pi|tau|eta|rho|ell|partial|nabla|sum|int|exists|forall|in|subseteq|subset|cup|cap|emptyset|varnothing|approx|leq|geq|neq)|[=<>+*/-])(?:_(?:\{[^}]+\}|[a-zA-Z0-9]))?', expression) is not None

def local_verification_dependencies(paths):
    import ast
    known = set(paths)
    dependencies = {path:set() for path in known}
    for path in known:
        if not path.is_file():
            continue
        source = path.read_text()
        modules = []
        if path.suffix == '.lean':
            modules = [(module,'.lean') for line in re.findall(r'^(?:public\s+)?import\s+([^\n]+)',source,re.M) for module in line.split()]
        elif path.suffix == '.py':
            for node in ast.walk(ast.parse(source)):
                if isinstance(node,ast.Import):
                    modules.extend((alias.name,'.py') for alias in node.names)
                elif isinstance(node,ast.ImportFrom) and node.module:
                    if re.fullmatch(r'capitulo_\d+',node.module):
                        modules.extend((node.module+'.'+alias.name,'.py') for alias in node.names)
                    else:
                        modules.append((node.module,'.py'))
        for module,suffix in modules:
            relative = Path(*module.split('.')).with_suffix(suffix)
            candidates = (ROOT/'scripts'/relative,path.parent/relative) if module.startswith('capitulo_') else (path.parent/relative,ROOT/'scripts'/relative)
            for candidate in candidates:
                if candidate in known or candidate.is_file():
                    dependencies[path].add(candidate)
                    break
            else:
                if module.startswith('capitulo_'):
                    dependencies[path].add(ROOT/'scripts'/relative)
        if path.suffix == '.wl':
            for name in re.findall(r'Get\[\s*"([^"]+)"\s*\]',source):
                candidate = (path.parent/name).resolve()
                if candidate in known or candidate.is_file():
                    dependencies[path].add(candidate)
            anchors=set(re.findall(r'\b([A-Za-z$][A-Za-z0-9$]*)\s*=\s*DirectoryName\[\$InputFileName\]',source))
            for anchor,tail in re.findall(r'Get\[\s*FileNameJoin\[\s*\{\s*([A-Za-z$][A-Za-z0-9$]*|DirectoryName\[\$InputFileName\])\s*((?:,\s*"[^"]*")+?)\s*\}\s*\]\s*\]',source):
                if anchor not in anchors and anchor!='DirectoryName[$InputFileName]':
                    dependencies[path].add(path.parent/('__dependencia_dinamica_nao_resolvida_'+anchor+'.wl'))
                    continue
                candidate=path.parent.joinpath(*re.findall(r'"([^"]*)"',tail)).resolve()
                dependencies[path].add(candidate)
    return dependencies

def audit(rows=None, manifests=None, check_files=True, detailed=False):
    from collections import Counter
    from objetos import catalogue, seal
    import aritmetica
    rows = collect() if rows is None else rows
    manifests = {chapter:load_manifest(chapter) for chapter in range(1,10)} if manifests is None else manifests
    actual = {row['id']:row for row in rows}
    errors = []
    file_digests = {ROOT/f'scripts/capitulo_{chapter:02}'/name:digest for chapter,manifest in manifests.items() for name,digest in manifest['ARQUIVOS'].items()}
    changed_paths = {path for path,digest in file_digests.items() if check_files and (not path.is_file() or hashlib.sha256(path.read_bytes()).hexdigest()!=digest)}
    dependencies = local_verification_dependencies(file_digests) if check_files else {}
    invalid_dependencies = set(changed_paths)
    while True:
        affected = {path for path,imports in dependencies.items() if imports & invalid_dependencies or imports-set(file_digests)}
        if affected <= invalid_dependencies:
            break
        invalid_dependencies |= affected
    if check_files:
        errors.extend({'arquivo':name,'erro':'matematica_em_arquivo_nao_inventariado'} for name in uncollected_math_sources(rows))
    pending = []
    expected = {}
    decisions = {}
    methods = Counter()
    verified_objects = set()
    for chapter, manifest in manifests.items():
        folder = ROOT / f'scripts/capitulo_{chapter:02}'
        current_objects = catalogue(folder) if check_files else manifest['OBJETOS']
        for name, digest in manifest['ARQUIVOS'].items():
            path = folder/name
            if path in changed_paths:
                errors.append({'arquivo':str(path.relative_to(ROOT)), 'erro':'verificacao_alterada_desde_a_revisao'})
        for entry in manifest['EXPRESSOES']:
            identity = entry['id']
            if identity in expected:
                errors.append({'id':identity, 'erro':'identificador_duplicado'})
            expected[identity] = entry
            source = actual.get(identity)
            if source is None or source['sha256'] != entry['sha256']:
                errors.append({'id':identity, 'erro':'expressao_ausente_ou_alterada'})
            if source is not None and (source['topic']!=entry['familia'] or source['context_sha256']!=entry['context_sha256']):
                errors.append({'id':identity, 'erro':'contexto_alterado'})
        generated_files, accepted = aritmetica.generated(chapter,rows)
        generated_ids = {row['id'] for row,relations,expressions in accepted}
        generated_records = {record['ids'][0]:record for record in aritmetica.records(chapter,rows)}
        for review in manifest.get('REVISOES',[]):
            issues = []
            if review.get('assinatura_revisao') != seal(review):
                issues.append('vinculo_ou_hipoteses_alterados_sem_revisao')
            if not review.get('proposicao') or review.get('alcance') not in ('notacao','mencao') and not review.get('hipoteses'):
                issues.append('proposicao_ou_condicoes_nao_declaradas')
            if review.get('alcance') not in ('completa','parcial','definicao','hipotese','notacao','mencao'):
                issues.append('alcance_invalido')
            if review.get('alcance') in ('notacao','mencao') and not review.get('observacao'):
                issues.append('ausencia_de_proposicao_sem_justificativa_contextual')
            components = review.get('componentes',[])
            if not isinstance(components,list) or not all(isinstance(item,str) for item in components) or len(components)!=len(set(components)):
                issues.append('componentes_visuais_invalidos')
                components = []
            elif any(identity not in actual or identity in review['ids'] for identity in components):
                issues.append('componente_visual_ausente_ou_circular')
            for identity in review['ids']:
                source = actual.get(identity)
                snapshot = review.get('fontes',{}).get(identity,{})
                if source is None or any(snapshot.get(key)!=source[key] for key in ('sha256','context_sha256','source_file_sha256','file','expression')):
                    issues.append('fonte_da_revisao_alterada')
            complete = review.get('alcance')=='completa'
            for system in ('py','lean','wl'):
                witnesses = review.get('testemunhas',{}).get(system,[])
                if not witnesses or review.get('pendencias',{}).get(system):
                    complete = False
                for witness in witnesses:
                    key = witness.get('objeto_id')
                    item = current_objects.get(key)
                    frozen = manifest['OBJETOS'].get(key)
                    if item is None or frozen is None or item!=frozen:
                        issues.append('objeto_ausente_ou_fragmento_alterado')
                        continue
                    if folder/item['arquivo'] in invalid_dependencies:
                        issues.append('dependencias_do_objeto_alteradas_desde_a_revisao')
                    if item['arquivo']!=witness['arquivo'] or not item['arquivo'].endswith('.'+system) or item['sha256']!=witness.get('objeto_sha256') or manifest['ARQUIVOS'].get(item['arquivo'])!=witness.get('arquivo_sha256'):
                        issues.append('testemunha_inconsistente')
                    if not (item['objeto']==witness['nome'] or item['objeto'].endswith('.'+witness['nome'])) or 'linha' in witness and item['linha']!=witness['linha']:
                        issues.append('objeto_diferente_do_nome_revisado')
                    method = witness.get('metodo')
                    if method not in ('prova_geral','identidade_simbolica','calculo_exato','teste_numerico','definicao','apoio_parcial','contraexemplo','eliminacao_de_quantificadores','inducao_estrutural','deducao_natural'):
                        issues.append('metodo_nao_declarado')
                    if method=='eliminacao_de_quantificadores' and system!='wl':
                        issues.append('metodo_incompativel_com_backend')
                    if method in ('inducao_estrutural','deducao_natural') and system not in ('py','wl'):
                        issues.append('metodo_incompativel_com_backend')
                    if method=='prova_geral' and (system!='lean' or item.get('tipo') not in ('theorem','lemma')):
                        issues.append('declaracao_nao_e_prova')
                    if system=='lean' and method in ('calculo_exato','identidade_simbolica','contraexemplo') and item.get('tipo') not in ('theorem','lemma'):
                        issues.append('definicao_usada_como_resultado')
                    if system in ('py','wl') and method not in ('definicao','apoio_parcial') and item.get('tipo')!='check':
                        issues.append('objeto_sem_verificacao_executavel')
                    if method in ('teste_numerico','definicao','apoio_parcial'):
                        complete = False
                    methods[(system,method)] += 1
                    verified_objects.add((chapter,key))
            if review.get('vinculo')=='transcricao_integral_reproduzivel':
                if not set(review['ids'])<=generated_ids:
                    issues.append('expressao_nao_transcrita_integralmente')
                if len(review['ids'])!=1:
                    issues.append('transcricao_sem_identidade_univoca')
                else:
                    generated_review=generated_records.get(review['ids'][0],{})
                    if any(review.get(key)!=generated_review.get(key) for key in ('proposicao','hipoteses')):
                        issues.append('sentido_ou_dominio_da_transcricao_divergente')
                    for system in ('py','lean','wl'):
                        correct={(w['arquivo'],w['nome']) for w in generated_review.get('testemunhas',{}).get(system,[])}
                        referenced={(w['arquivo'],w['nome']) for w in review.get('testemunhas',{}).get(system,[])}
                        if correct!=referenced:
                            issues.append('testemunha_aritmetica_de_outra_expressao')
                if check_files:
                    for name, code in generated_files.items():
                        if not (folder/name).is_file() or (folder/name).read_text()!=code:
                            issues.append('transcricao_diverge_do_latex')
            if issues:
                complete = False
                errors.append({'ids':review['ids'], 'erros':sorted(set(issues))})
            decision = {'alcance':review['alcance'], 'triplice_completa':complete, 'proposicao':review['proposicao'], 'hipoteses':review['hipoteses'], 'observacao':review.get('observacao',''), 'pendencias':review.get('pendencias',{}), 'testemunhas':review.get('testemunhas',{}), 'componentes':components, 'integridade':not issues}
            for identity in review['ids']:
                decisions.setdefault(identity,[]).append(decision)
    for identity in sorted(set(actual)-set(expected)):
        errors.append({'id':identity,'erro':'expressao_nova_sem_revisao'})
    component_graph = {identity:{component for review in reviews for component in review['componentes']} for identity,reviews in decisions.items()}
    def cyclic_component(identity,path):
        if identity in path:
            return True
        return any(cyclic_component(component,path|{identity}) for component in component_graph.get(identity,set()))
    for identity,reviews in decisions.items():
        for review in reviews:
            if review['componentes'] and cyclic_component(identity,set()):
                review['integridade'] = False
                review['triplice_completa'] = False
                errors.append({'id':identity,'erro':'ciclo_entre_componentes_visuais'})
            unreviewed_components = [component for component in review['componentes'] if component not in decisions]
            if unreviewed_components:
                review['integridade'] = False
                review['triplice_completa'] = False
                errors.append({'id':identity,'erro':'componente_visual_sem_revisao','componentes':unreviewed_components})
    while True:
        changed = False
        for identity,reviews in decisions.items():
            for review in reviews:
                gaps = sorted({component for component in review['componentes'] for item in decisions.get(component,[]) if not item['integridade'] or item.get('componentes_com_lacunas') or item['alcance']=='parcial' or item['alcance']=='completa' and not item['triplice_completa']})
                if gaps != review.get('componentes_com_lacunas',[]):
                    changed = True
                review['componentes_com_lacunas'] = gaps
                if gaps and review['triplice_completa']:
                    review['triplice_completa'] = False
                    changed = True
        if not changed:
            break
    complete_ids = []
    partial_ids = []
    unreviewed_ids = []
    notation_ids = []
    result_gap_ids = []
    condition_definition_ids = []
    for identity,row in actual.items():
        reviews = decisions.get(identity,[])
        obligations = [item for item in reviews if item['alcance'] not in ('notacao','mencao') or not item['integridade'] or item.get('componentes_com_lacunas')]
        if obligations and all(item['triplice_completa'] for item in obligations):
            complete_ids.append(identity)
        elif reviews and not obligations:
            notation_ids.append(identity)
        else:
            (partial_ids if reviews else unreviewed_ids).append(identity)
            if reviews:
                if any(item['alcance']=='parcial' or not item['integridade'] or item.get('componentes_com_lacunas') or item['alcance']=='completa' and not item['triplice_completa'] for item in obligations):
                    result_gap_ids.append(identity)
                else:
                    condition_definition_ids.append(identity)
            pending.append({'id':identity,'arquivo':row['file'],'linha':row['line'],'expressao':row['expression'], 'estado':'revisao_parcial_ou_condicional' if reviews else 'sem_vinculo_semantico_individual_revisado', 'revisoes':reviews})
    result = {'ocorrencias_no_latex':len(rows), 'ocorrencias_com_vinculo_triplice_integral':len(complete_ids), 'ocorrencias_com_revisao_parcial_ou_condicional':len(partial_ids), 'ocorrencias_sem_revisao_semantica_individual':len(unreviewed_ids), 'notacoes_ou_mencoes_examinadas_sem_proposicao_autonoma':len(notation_ids), 'dentre_nao_revisadas_simbolos_sem_proposicao_autonoma':sum(isolated_notation(actual[identity]['expression']) for identity in unreviewed_ids), 'objetos_individuais_conferidos':len(verified_objects), 'metodos':{system:{method:count for (sy,method),count in methods.items() if sy==system} for system in ('py','lean','wl')}, 'integridade_estrutural':not errors, 'cobertura_semantica_total':not errors and not pending, 'vinculos_de_contexto_contam_como_cobertura':False, 'erros':errors}
    result['resultados_com_lacuna_em_algum_backend']=len(result_gap_ids)
    result['condicoes_ou_definicoes_documentadas_sem_certificacao_triplice']=len(condition_definition_ids)
    result['execucao_dos_tres_sistemas_nesta_chamada']=False
    if detailed:
        result['pendencias'] = pending
        result['integralmente_vinculadas'] = complete_ids
        result['notacoes_ou_mencoes_examinadas'] = notation_ids
        result['resultados_com_lacuna'] = result_gap_ids
    return result

def detail(identity):
    for chapter in range(1,10):
        manifest = load_manifest(chapter)
        for entry in manifest['EXPRESSOES']:
            if entry['id']==identity:
                return {'latex':next(row for row in collect() if row['id']==identity), 'registro':entry, 'revisoes_semanticas':[record for record in manifest.get('REVISOES',[]) if identity in record['ids']], 'candidatos_do_topico_sem_valor_probatorio':manifest['CONTEXTOS'].get(entry['familia'],{})}
    raise KeyError(identity)

def self_test():
    import copy
    from objetos import seal
    from aritmetica import Parser, Unsupported, evaluate, statement
    rows = collect()
    manifests = {chapter:load_manifest(chapter) for chapter in range(1,10)}
    baseline = audit(rows,manifests,False,detailed=True)
    assert not baseline['erros'], baseline['erros']
    from unittest.mock import patch
    integral = set(baseline['integralmente_vinculadas'])
    chapter, dependency_review = next((chapter,record) for chapter,manifest in manifests.items() for record in manifest['REVISOES'] if record['alcance']=='completa' and set(record['ids'])<=integral and record['testemunhas']['py'])
    dependency_name = dependency_review['testemunhas']['py'][0]['arquivo']
    dependency_path = ROOT/f'scripts/capitulo_{chapter:02}'/dependency_name
    original_read_bytes = Path.read_bytes
    def changed_dependency(path):
        data = original_read_bytes(path)
        return data+b'\n' if path==dependency_path else data
    with patch.object(Path,'read_bytes',changed_dependency):
        dependent_report = audit(rows,manifests,True,detailed=True)
    assert not set(dependency_review['ids']) & set(dependent_report['integralmente_vinculadas'])
    assert any('dependencias_do_objeto_alteradas_desde_a_revisao' in error.get('erros',[]) for error in dependent_report['erros'])
    dependencies = local_verification_dependencies(ROOT/f'scripts/capitulo_{chapter:02}'/name for chapter,manifest in manifests.items() for name in manifest['ARQUIVOS'])
    imported_path = ROOT/'scripts/capitulo_04/Espectro.lean'
    importing_path = ROOT/'scripts/capitulo_04/Certificados.lean'
    assert imported_path in dependencies[importing_path]
    importing_python = ROOT/'scripts/capitulo_01/dependency_probe.py'
    importing_wolfram = ROOT/'scripts/capitulo_01/dependency_probe.wl'
    local_helper = ROOT/'scripts/capitulo_01/dependency_helper.py'
    shadowed_helper = ROOT/'scripts/dependency_helper.py'
    wolfram_helper = ROOT/'scripts/capitulo_01/dependency_helper.wl'
    synthetic_sources = {importing_python:'import dependency_helper\n',importing_wolfram:'Get["dependency_helper.wl"]\n',shadowed_helper:''}
    synthetic_files = set(synthetic_sources)|{local_helper,wolfram_helper}
    with patch.object(Path,'is_file',lambda path:path in synthetic_files), patch.object(Path,'read_text',lambda path,*args,**kwargs:synthetic_sources[path]):
        unsealed = local_verification_dependencies(synthetic_sources)
    assert unsealed[importing_python]=={local_helper}
    assert unsealed[importing_wolfram]=={wolfram_helper}
    assert local_helper not in synthetic_sources and wolfram_helper not in synthetic_sources
    qualified_helper=ROOT/'scripts/capitulo_04/svd_geral.py'
    joined_helper=ROOT/'scripts/capitulo_02/riemann_geral.wl'
    qualified_sources={importing_python:'from capitulo_04 import svd_geral as s\n',importing_wolfram:'probeDirectory=DirectoryName[$InputFileName];\nBlock[{$ContextPath={"System`"}},Get[FileNameJoin[{probeDirectory,"..","capitulo_02","riemann_geral.wl"}]]];\n'}
    with patch.object(Path,'is_file',lambda path:path in set(qualified_sources)|{qualified_helper,joined_helper}),patch.object(Path,'read_text',lambda path,*args,**kwargs:qualified_sources[path]):
        qualified_dependencies=local_verification_dependencies(qualified_sources)
    assert qualified_dependencies[importing_python]=={qualified_helper}
    assert qualified_dependencies[importing_wolfram]=={joined_helper}
    unknown_source={importing_wolfram:'Get[FileNameJoin[{unknownDirectory,"unsealed.wl"}]];'}
    with patch.object(Path,'is_file',lambda path:path in unknown_source),patch.object(Path,'read_text',lambda path,*args,**kwargs:unknown_source[path]):
        unknown_dependencies=local_verification_dependencies(unknown_source)
    assert unknown_dependencies[importing_wolfram]=={importing_wolfram.parent/'__dependencia_dinamica_nao_resolvida_unknownDirectory.wl'}
    with patch.dict(audit.__globals__,{'local_verification_dependencies':lambda paths:{dependency_path:{local_helper}}}):
        unsealed_report = audit(rows,manifests,True,detailed=True)
    assert not set(dependency_review['ids']) & set(unsealed_report['integralmente_vinculadas'])
    assert any('dependencias_do_objeto_alteradas_desde_a_revisao' in error.get('erros',[]) for error in unsealed_report['erros'])
    dependent_records = [record for record in manifests[4]['REVISOES'] if any(w['arquivo']=='Certificados.lean' for w in record['testemunhas'].get('lean',[]))]
    assert dependent_records
    dependency_path = imported_path
    with patch.object(Path,'read_bytes',changed_dependency):
        dependent_report = audit(rows,manifests,True,detailed=True)
    assert any('dependencias_do_objeto_alteradas_desde_a_revisao' in error.get('erros',[]) and set(error.get('ids',[])) & {identity for record in dependent_records for identity in record['ids']} for error in dependent_report['erros'])
    altered = copy.deepcopy(rows)
    altered[0]['sha256']='0'*64
    assert audit(altered,manifests,False)['erros']
    altered = copy.deepcopy(rows)
    altered[0]['context_sha256']='0'*64
    assert audit(altered,manifests,False)['erros']
    altered=copy.deepcopy(rows)
    reviewed=next(identity for manifest in manifests.values() for record in manifest['REVISOES'] for identity in record['ids'])
    next(row for row in altered if row['id']==reviewed)['source_file_sha256']='0'*64
    assert audit(altered,manifests,False)['erros']
    assert audit(rows[1:],manifests,False)['erros']
    added = rows+[dict(rows[0],id='c01.e9999')]
    assert audit(added,manifests,False)['erros']
    damaged = copy.deepcopy(manifests)
    record = next(record for record in damaged[1]['REVISOES'] if record['alcance']=='completa')
    old = record['testemunhas']['lean'][0]['objeto_id']
    replacement = next(key for key,item in damaged[1]['OBJETOS'].items() if item['arquivo'].endswith('.lean') and key!=old)
    record['testemunhas']['lean'][0]['objeto_id']=replacement
    assert audit(rows,damaged,False)['erros']
    damaged = copy.deepcopy(manifests)
    arithmetic = [record for record in damaged[1]['REVISOES'] if record.get('vinculo')=='transcricao_integral_reproduzivel']
    arithmetic[0]['testemunhas']=copy.deepcopy(arithmetic[1]['testemunhas'])
    arithmetic[0]['assinatura_revisao']=seal(arithmetic[0])
    assert any('testemunha_aritmetica_de_outra_expressao' in error.get('erros',[]) for error in audit(rows,damaged,False)['erros'])
    damaged = copy.deepcopy(manifests)
    damaged[1]['REVISOES'][0]['hipoteses']=[]
    assert audit(rows,damaged,False)['erros']
    damaged = copy.deepcopy(manifests)
    for manifest in damaged.values():
        manifest['REVISOES']=[]
    report = audit(rows,damaged,False)
    assert report['ocorrencias_com_vinculo_triplice_integral']==0
    assert not report['cobertura_semantica_total']
    damaged = copy.deepcopy(manifests)
    for manifest in damaged.values():
        for record in manifest['REVISOES']:
            record['testemunhas']['lean']=[]
            record['assinatura_revisao']=seal(record)
    report = audit(rows,damaged,False)
    assert report['ocorrencias_com_vinculo_triplice_integral']==0
    damaged = copy.deepcopy(manifests)
    for manifest in damaged.values():
        for record in manifest['REVISOES']:
            for witness in record['testemunhas'].get('py',[]):
                witness['metodo']='teste_numerico'
            record['assinatura_revisao']=seal(record)
    assert audit(rows,damaged,False)['ocorrencias_com_vinculo_triplice_integral']==0
    chapter,parent = next((chapter,record) for chapter,manifest in manifests.items() for record in manifest['REVISOES'] if record.get('componentes') and record['alcance']=='completa')
    damaged = copy.deepcopy(manifests)
    altered_parent = next(record for record in damaged[chapter]['REVISOES'] if record['ids']==parent['ids'] and record.get('componentes'))
    altered_parent['componentes'].append('c99.e9999')
    altered_parent['assinatura_revisao']=seal(altered_parent)
    assert any('componente_visual_ausente_ou_circular' in error.get('erros',[]) for error in audit(rows,damaged,False)['erros'])
    damaged = copy.deepcopy(manifests)
    child = next(record for record in damaged[chapter]['REVISOES'] if set(record['ids']) & set(parent['componentes']) and record['alcance']=='completa')
    child['alcance']='parcial'
    child['pendencias']={'py':'obrigacao ausente no contraprova','lean':'','wl':''}
    child['assinatura_revisao']=seal(child)
    assert not set(parent['ids']) & set(audit(rows,damaged,False,True)['integralmente_vinculadas'])
    damaged = copy.deepcopy(manifests)
    altered_parent = next(record for record in damaged[chapter]['REVISOES'] if record['ids']==parent['ids'] and record.get('componentes'))
    child = next(record for record in damaged[chapter]['REVISOES'] if set(record['ids']) & set(parent['componentes']))
    child['componentes']=[parent['ids'][0]]
    child['assinatura_revisao']=seal(child)
    assert any(error.get('erro')=='ciclo_entre_componentes_visuais' for error in audit(rows,damaged,False)['erros'])
    synthetic_rows = [row for row in rows if row['chapter']==1][:3]
    synthetic_ids = [row['id'] for row in synthetic_rows]
    prototype = next(record for record in manifests[1]['REVISOES'] if record['alcance']=='completa' and set(record['ids'])<=integral)
    for middle_scope in ('definicao','mencao'):
        synthetic = {1:copy.deepcopy(manifests[1])}
        synthetic[1]['EXPRESSOES'] = [entry for entry in synthetic[1]['EXPRESSOES'] if entry['id'] in synthetic_ids]
        synthetic[1]['REVISOES'] = []
        for index,row in enumerate(synthetic_rows):
            review = copy.deepcopy(prototype)
            review.pop('vinculo',None)
            review['ids'] = [row['id']]
            review['fontes'] = {row['id']:{key:row[key] for key in ('sha256','context_sha256','source_file_sha256','file','expression')}}
            review['componentes'] = [synthetic_ids[index+1]] if index<2 else []
            review['alcance'] = ('completa',middle_scope,'parcial')[index]
            review['observacao'] = 'Contraprova de propagacao transitiva.'
            review['pendencias'] = {'py':'obrigacao ausente','lean':'','wl':''} if index==2 else {}
            review['assinatura_revisao'] = seal(review)
            synthetic[1]['REVISOES'].append(review)
        transitive_report = audit(synthetic_rows,synthetic,False,True)
        assert not transitive_report['erros'], transitive_report['erros']
        assert not transitive_report['integralmente_vinculadas']
        assert set(transitive_report['resultados_com_lacuna'])==set(synthetic_ids)
    for invalid in ('1/0=0','x/x=1','1+1=2=3x',r'\frac3 100=3/100','2^10=1024','1.000=1','0^0=1'):
        try:
            for operator,left,right in Parser(invalid).parse():
                evaluate(left)
                evaluate(right)
        except Unsupported:
            continue
        raise AssertionError(invalid)
    assert evaluate(Parser('-2^2=-4').parse()[0][1])==-4
    for expression in ('(2+1)!=6','2^{1+2}=8','2^{-(1+2)}=1/8','(6/2)!=6'):
        relations = Parser(expression).parse()
        for system in ('py','lean','wl'):
            try:
                statement(relations,system)
            except Unsupported:
                continue
            raise AssertionError((expression,system))
    plots=list(plot_occurrences(r'\addplot+[black,-{Stealth[length=4pt]}] coordinates {(0,0)(1,2)};'))
    assert len(plots)==1 and plots[0][1:] == ('plot_coordinates','(0,0)(1,2)')
    return {'alteracao_de_expressao':True,'alteracao_de_contexto':True,'alteracao_do_arquivo_latex':True,'alteracao_de_dependencia_invalida_o_vinculo':True,'alteracao_de_import_transitivo_invalida_o_vinculo':True,'dependencia_local_nova_e_sombreamento_detectados':True,'troca_objeto_sem_nova_revisao_rejeitada':True,'objeto_aritmetico_errado_mesmo_com_selo_recalculado':True,'hipoteses_removidas':True,'contexto_generico_nao_certifica':True,'backend_ausente_nao_certifica':True,'amostragem_nao_vira_prova':True,'transcricao_parcial_rejeitada':True,'argumentos_compostos_nao_precalculados':True,'denominador_zero_rejeitado':True,'coordenadas_com_opcoes_aninhadas':True,'componente_visual_ausente_rejeitado':True,'lacuna_do_componente_invalida_figura':True,'lacuna_visual_transitiva_invalida_todos_ancestrais':True,'ciclo_entre_componentes_rejeitado':True}

if __name__=='__main__':
    if '--inventario' in sys.argv:
        output = {'ocorrencias':len(collect()),'expressoes':collect()}
    elif '--detalhar' in sys.argv:
        output = detail(sys.argv[sys.argv.index('--detalhar')+1])
    elif '--autoteste' in sys.argv:
        output = {'autoteste':self_test()}
    else:
        output = audit(detailed='--pendencias' in sys.argv or '--lacunas' in sys.argv)
        if '--lacunas' in sys.argv:
            identities=set(output['resultados_com_lacuna'])
            output['pendencias']=[row for row in output['pendencias'] if row['id'] in identities]
            output.pop('integralmente_vinculadas')
            output.pop('notacoes_ou_mencoes_examinadas')
    print(json.dumps(output,ensure_ascii=False,indent=2))
    raise SystemExit(1 if output.get('erros') else 2 if output.get('cobertura_semantica_total') is False else 0)

