REDTEAM = [{'ids': ['c03.e0001'],
  'expressoes': {'c03.e0001': '\\varnothing'},
  'proposicao': 'Convenção morfológica para expoente zero; não é aqui o conjunto vazio da matemática A '
                'expressão desta ocorrência é \\varnothing.',
  'hipoteses': ['As convenções e o domínio são os explicitados na prosa adjacente.'],
  'alcance': 'notacao',
  'observacao': 'Convenção morfológica para expoente zero; não é aqui o conjunto vazio da matemática Não se '
                'contabiliza como prova de um resultado matemático.',
  'testemunhas': {'lean': [], 'py': [], 'wl': []},
  'pendencias': {'lean': '', 'py': '', 'wl': ''}},
 {'ids': ['c03.e0002'],
  'expressoes': {'c03.e0002': '-\\varnothing'},
  'proposicao': 'Convenção morfológica para expoente zero; não é aqui o conjunto vazio da matemática A '
                'expressão desta ocorrência é -\\varnothing.',
  'hipoteses': ['As convenções e o domínio são os explicitados na prosa adjacente.'],
  'alcance': 'notacao',
  'observacao': 'Convenção morfológica para expoente zero; não é aqui o conjunto vazio da matemática Não se '
                'contabiliza como prova de um resultado matemático.',
  'testemunhas': {'lean': [], 'py': [], 'wl': []},
  'pendencias': {'lean': '', 'py': '', 'wl': ''}},
 {'ids': ['c03.e0003'],
  'expressoes': {'c03.e0003': 'D=\\{1,2,3,4,5,6,7,8\\}'},
  'proposicao': 'D define o domínio das oito classes flexionais da tabela A expressão desta ocorrência é '
                'D=\\{1,2,3,4,5,6,7,8\\}.',
  'hipoteses': ['Identificadores de classe 1..8; não são contagens de ocorrências.'],
  'alcance': 'definicao',
  'observacao': 'D define o domínio das oito classes flexionais da tabela Não se contabiliza como prova de '
                'um resultado matemático.',
  'testemunhas': {'lean': [], 'py': [], 'wl': []},
  'pendencias': {'lean': '', 'py': '', 'wl': ''}},
 {'ids': ['c03.e0007', 'c03.e0009', 'c03.e0016', 'c03.e0017'],
  'expressoes': {'c03.e0007': '5\\in A',
                 'c03.e0009': '1\\notin A',
                 'c03.e0016': '|A\\cap B|=2',
                 'c03.e0017': '|A\\cup B|=4'},
  'proposicao': 'Pertinências e cardinalidades da interseção e união dos conjuntos extraídos do paradigma.',
  'hipoteses': ['A={5,6,8}; B={1,5,6}; igualdade de identificadores de classe.'],
  'alcance': 'completa',
  'observacao': '',
  'testemunhas': {'lean': [{'arquivo': 'Expressoes.lean',
                            'nome': 'Chapter03Expressions.set_membership',
                            'linha': 25,
                            'metodo': 'prova_geral'}],
                  'py': [{'arquivo': 'expressoes.py',
                          'nome': 'set_membership',
                          'linha': 16,
                          'metodo': 'identidade_simbolica'}],
                  'wl': [{'arquivo': 'expressoes.wl',
                          'nome': 'set_membership',
                          'linha': 11,
                          'metodo': 'identidade_simbolica'}]},
  'pendencias': {'lean': '', 'py': '', 'wl': ''}},
 {'ids': ['c03.e0014', 'c03.e0015'],
  'expressoes': {'c03.e0014': '|A|=3', 'c03.e0015': '|B|=3'},
  'proposicao': 'Cada um dos conjuntos de classes selecionados tem cardinalidade três.',
  'hipoteses': ['Conjuntos A e B publicados; não contam repetição de um mesmo elemento.'],
  'alcance': 'completa',
  'observacao': '',
  'testemunhas': {'lean': [{'arquivo': 'Verificar.lean',
                            'nome': 'Chapter03.c03_r01.publishedSets',
                            'linha': 10,
                            'metodo': 'prova_geral'}],
                  'py': [{'arquivo': 'verificar.py',
                          'nome': 'c03_r01',
                          'linha': 26,
                          'metodo': 'calculo_exato'}],
                  'wl': [{'arquivo': 'verificar.wl',
                          'nome': 'c03_r01',
                          'linha': 7,
                          'metodo': 'calculo_exato'}]},
  'pendencias': {'lean': '', 'py': '', 'wl': ''}},
 {'ids': ['c03.e0023'],
  'expressoes': {'c03.e0023': 'S\\subseteq L'},
  'proposicao': 'Inclusão lexical, premissa universal ou universo de referência explicitamente adotados no '
                'argumento A expressão desta ocorrência é S\\subseteq L.',
  'hipoteses': ['Conjuntos no mesmo universo; a inclusão não pressupõe existência de elementos.'],
  'alcance': 'hipotese',
  'observacao': 'Inclusão lexical, premissa universal ou universo de referência explicitamente adotados no '
                'argumento Não se contabiliza como prova de um resultado matemático.',
  'testemunhas': {'lean': [], 'py': [], 'wl': []},
  'pendencias': {'lean': '', 'py': '', 'wl': ''}},
 {'ids': ['c03.e0036'],
  'expressoes': {'c03.e0036': 'L\\subseteq U'},
  'proposicao': 'Inclusão lexical, premissa universal ou universo de referência explicitamente adotados no '
                'argumento A expressão desta ocorrência é L\\subseteq U.',
  'hipoteses': ['Conjuntos no mesmo universo; a inclusão não pressupõe existência de elementos.'],
  'alcance': 'hipotese',
  'observacao': 'Inclusão lexical, premissa universal ou universo de referência explicitamente adotados no '
                'argumento Não se contabiliza como prova de um resultado matemático.',
  'testemunhas': {'lean': [], 'py': [], 'wl': []},
  'pendencias': {'lean': '', 'py': '', 'wl': ''}},
 {'ids': ['c03.e0162'],
  'expressoes': {'c03.e0162': 'S\\subseteq L'},
  'proposicao': 'Inclusão lexical, premissa universal ou universo de referência explicitamente adotados no '
                'argumento A expressão desta ocorrência é S\\subseteq L.',
  'hipoteses': ['Conjuntos no mesmo universo; a inclusão não pressupõe existência de elementos.'],
  'alcance': 'hipotese',
  'observacao': 'Inclusão lexical, premissa universal ou universo de referência explicitamente adotados no '
                'argumento Não se contabiliza como prova de um resultado matemático.',
  'testemunhas': {'lean': [], 'py': [], 'wl': []},
  'pendencias': {'lean': '', 'py': '', 'wl': ''}},
 {'ids': ['c03.e0163'],
  'expressoes': {'c03.e0163': 'N\\subseteq M'},
  'proposicao': 'Inclusão lexical, premissa universal ou universo de referência explicitamente adotados no '
                'argumento A expressão desta ocorrência é N\\subseteq M.',
  'hipoteses': ['Conjuntos no mesmo universo; a inclusão não pressupõe existência de elementos.'],
  'alcance': 'hipotese',
  'observacao': 'Inclusão lexical, premissa universal ou universo de referência explicitamente adotados no '
                'argumento Não se contabiliza como prova de um resultado matemático.',
  'testemunhas': {'lean': [], 'py': [], 'wl': []},
  'pendencias': {'lean': '', 'py': '', 'wl': ''}},
 {'ids': ['c03.e0164'],
  'expressoes': {'c03.e0164': 'L\\subseteq N'},
  'proposicao': 'Inclusão lexical, premissa universal ou universo de referência explicitamente adotados no '
                'argumento A expressão desta ocorrência é L\\subseteq N.',
  'hipoteses': ['Conjuntos no mesmo universo; a inclusão não pressupõe existência de elementos.'],
  'alcance': 'hipotese',
  'observacao': 'Inclusão lexical, premissa universal ou universo de referência explicitamente adotados no '
                'argumento Não se contabiliza como prova de um resultado matemático.',
  'testemunhas': {'lean': [], 'py': [], 'wl': []},
  'pendencias': {'lean': '', 'py': '', 'wl': ''}},
 {'ids': ['c03.e0167'],
  'expressoes': {'c03.e0167': 'S\\subseteq L'},
  'proposicao': 'Inclusão lexical, premissa universal ou universo de referência explicitamente adotados no '
                'argumento A expressão desta ocorrência é S\\subseteq L.',
  'hipoteses': ['Conjuntos no mesmo universo; a inclusão não pressupõe existência de elementos.'],
  'alcance': 'hipotese',
  'observacao': 'Inclusão lexical, premissa universal ou universo de referência explicitamente adotados no '
                'argumento Não se contabiliza como prova de um resultado matemático.',
  'testemunhas': {'lean': [], 'py': [], 'wl': []},
  'pendencias': {'lean': '', 'py': '', 'wl': ''}},
 {'ids': ['c03.e0169'],
  'expressoes': {'c03.e0169': 'L\\subseteq N'},
  'proposicao': 'Inclusão lexical, premissa universal ou universo de referência explicitamente adotados no '
                'argumento A expressão desta ocorrência é L\\subseteq N.',
  'hipoteses': ['Conjuntos no mesmo universo; a inclusão não pressupõe existência de elementos.'],
  'alcance': 'hipotese',
  'observacao': 'Inclusão lexical, premissa universal ou universo de referência explicitamente adotados no '
                'argumento Não se contabiliza como prova de um resultado matemático.',
  'testemunhas': {'lean': [], 'py': [], 'wl': []},
  'pendencias': {'lean': '', 'py': '', 'wl': ''}},
 {'ids': ['c03.e0174'],
  'expressoes': {'c03.e0174': 'L\\subseteq N'},
  'proposicao': 'Inclusão lexical, premissa universal ou universo de referência explicitamente adotados no '
                'argumento A expressão desta ocorrência é L\\subseteq N.',
  'hipoteses': ['Conjuntos no mesmo universo; a inclusão não pressupõe existência de elementos.'],
  'alcance': 'hipotese',
  'observacao': 'Inclusão lexical, premissa universal ou universo de referência explicitamente adotados no '
                'argumento Não se contabiliza como prova de um resultado matemático.',
  'testemunhas': {'lean': [], 'py': [], 'wl': []},
  'pendencias': {'lean': '', 'py': '', 'wl': ''}},
 {'ids': ['c03.e0175'],
  'expressoes': {'c03.e0175': 'N\\subseteq M'},
  'proposicao': 'Inclusão lexical, premissa universal ou universo de referência explicitamente adotados no '
                'argumento A expressão desta ocorrência é N\\subseteq M.',
  'hipoteses': ['Conjuntos no mesmo universo; a inclusão não pressupõe existência de elementos.'],
  'alcance': 'hipotese',
  'observacao': 'Inclusão lexical, premissa universal ou universo de referência explicitamente adotados no '
                'argumento Não se contabiliza como prova de um resultado matemático.',
  'testemunhas': {'lean': [], 'py': [], 'wl': []},
  'pendencias': {'lean': '', 'py': '', 'wl': ''}},
 {'ids': ['c03.e0025'],
  'expressoes': {'c03.e0025': 'x\\in S'},
  'proposicao': 'Sintaxe da pertinência relaciona um indivíduo a um conjunto, em contraste com a inclusão A '
                'expressão desta ocorrência é x\\in S.',
  'hipoteses': ['x indivíduo; S conjunto; nenhuma pertinência concreta está sendo afirmada.'],
  'alcance': 'definicao',
  'observacao': 'Sintaxe da pertinência relaciona um indivíduo a um conjunto, em contraste com a inclusão '
                'Não se contabiliza como prova de um resultado matemático.',
  'testemunhas': {'lean': [], 'py': [], 'wl': []},
  'pendencias': {'lean': '', 'py': '', 'wl': ''}},
 {'ids': ['c03.e0027'],
  'expressoes': {'c03.e0027': 'L\\setminus S'},
  'proposicao': 'Diferença de conjuntos ou complemento relativo no universo declarado A expressão desta '
                'ocorrência é L\\setminus S.',
  'hipoteses': ['L,S,U subconjuntos do mesmo domínio; complemento é relativo a U.'],
  'alcance': 'definicao',
  'observacao': 'Diferença de conjuntos ou complemento relativo no universo declarado Não se contabiliza '
                'como prova de um resultado matemático.',
  'testemunhas': {'lean': [], 'py': [], 'wl': []},
  'pendencias': {'lean': '', 'py': '', 'wl': ''}},
 {'ids': ['c03.e0037'],
  'expressoes': {'c03.e0037': 'U\\setminus L'},
  'proposicao': 'Diferença de conjuntos ou complemento relativo no universo declarado A expressão desta '
                'ocorrência é U\\setminus L.',
  'hipoteses': ['L,S,U subconjuntos do mesmo domínio; complemento é relativo a U.'],
  'alcance': 'definicao',
  'observacao': 'Diferença de conjuntos ou complemento relativo no universo declarado Não se contabiliza '
                'como prova de um resultado matemático.',
  'testemunhas': {'lean': [], 'py': [], 'wl': []},
  'pendencias': {'lean': '', 'py': '', 'wl': ''}},
 {'ids': ['c03.e0030'],
  'expressoes': {'c03.e0030': 'S\\setminus L'},
  'proposicao': 'Sob S⊆L, a diferença S−L é vazia; a expressão aparece como objeto dessa consequência.',
  'hipoteses': ['S⊆L para a diferença; L⊆U para L∪(U−L)=U; interseção vazia não exige esta última inclusão.',
                'Certificado de dedução natural com introdução/eliminação de quantificadores, escopo de '
                'variáveis, substituição sem captura e controle de testemunha fresca; o domínio pode ser '
                'vazio. A dupla negação e o terceiro excluído são regras da lógica clássica.'],
  'alcance': 'completa',
  'observacao': 'Cada testemunha CAS verifica uma árvore finita de prova ou o esquema completo de indução, '
                'com suas condições laterais; não é amostragem de indivíduos ou de comprimentos.',
  'testemunhas': {'lean': [{'arquivo': 'Verificar.lean',
                            'nome': 'Chapter03.c03_r02.differenceEmpty',
                            'linha': 15,
                            'metodo': 'prova_geral'},
                           {'arquivo': 'Verificar.lean',
                            'nome': 'Chapter03.c03_r02.noOverlap',
                            'linha': 20,
                            'metodo': 'prova_geral'},
                           {'arquivo': 'Verificar.lean',
                            'nome': 'Chapter03.c03_r02.coverUniverse',
                            'linha': 25,
                            'metodo': 'prova_geral'}],
                  'py': [{'arquivo': 'deducao.py',
                          'nome': 'difference_empty',
                          'metodo': 'deducao_natural',
                          'linha': 181},
                         {'arquivo': 'deducao.py',
                          'nome': 'complement_disjoint',
                          'metodo': 'deducao_natural',
                          'linha': 182},
                         {'arquivo': 'deducao.py',
                          'nome': 'complement_cover',
                          'metodo': 'deducao_natural',
                          'linha': 183},
                         {'arquivo': 'deducao.py',
                          'nome': 'set_extensionality_definitions',
                          'metodo': 'deducao_natural',
                          'linha': 194}],
                  'wl': [{'arquivo': 'deducao.wl',
                          'nome': 'difference_empty',
                          'metodo': 'deducao_natural',
                          'linha': 43},
                         {'arquivo': 'deducao.wl',
                          'nome': 'complement_disjoint',
                          'metodo': 'deducao_natural',
                          'linha': 44},
                         {'arquivo': 'deducao.wl',
                          'nome': 'complement_cover',
                          'metodo': 'deducao_natural',
                          'linha': 45},
                         {'arquivo': 'deducao.wl',
                          'nome': 'set_extensionality_definitions',
                          'metodo': 'deducao_natural',
                          'linha': 56}]},
  'pendencias': {'lean': '', 'py': '', 'wl': ''}},
 {'ids': ['c03.e0046'],
  'expressoes': {'c03.e0046': '\\begin{aligned} '
                              'A&=\\{\\texttt{s},\\texttt{or},\\texttt{pr},\\texttt{endere}\\},\\\\ '
                              'B&=\\{\\texttt{s},\\texttt{or},\\texttt{pr},\\texttt{endere},\\texttt{bbe}\\}. '
                              '\\end{aligned}'},
  'proposicao': 'A e B são os conjuntos formados pelos segmentos das duas formas italianas publicadas A '
                'expressão desta ocorrência é \\begin{aligned} '
                'A&=\\{\\texttt{s},\\texttt{or},\\texttt{pr},\\texttt{endere}\\},\\\\ '
                'B&=\\{\\texttt{s},\\texttt{or},\\texttt{pr},\\texttt{endere},\\texttt{bbe}\\}. '
                '\\end{aligned}.',
  'hipoteses': ['Segmentações s|or|pr|endere e s|or|pr|endere|bbe; conjuntos descartam ordem e repetições.'],
  'alcance': 'definicao',
  'observacao': 'A e B são os conjuntos formados pelos segmentos das duas formas italianas publicadas Não se '
                'contabiliza como prova de um resultado matemático.',
  'testemunhas': {'lean': [], 'py': [], 'wl': []},
  'pendencias': {'lean': '', 'py': '', 'wl': ''}},
 {'ids': ['c03.e0049', 'c03.e0050', 'c03.e0051', 'c03.e0052', 'c03.e0060'],
  'expressoes': {'c03.e0049': 'A\\subseteq B',
                 'c03.e0050': '|A|=4',
                 'c03.e0051': '|B|=5',
                 'c03.e0052': '|A\\cap B|=4',
                 'c03.e0060': '|A\\cap C|=3'},
  'proposicao': 'Inclusão e tamanhos dos conjuntos de segmentos italianos publicados.',
  'hipoteses': ['A,B,C definidos pelas segmentações transcritas; endere e end são elementos distintos.'],
  'alcance': 'completa',
  'observacao': '',
  'testemunhas': {'lean': [{'arquivo': 'Verificar.lean',
                            'nome': 'Chapter03.c03_n01.publishedSegments',
                            'linha': 160,
                            'metodo': 'prova_geral'}],
                  'py': [{'arquivo': 'verificar.py',
                          'nome': 'c03_n01',
                          'linha': 69,
                          'metodo': 'identidade_simbolica'},
                         {'arquivo': 'verificar.py',
                          'nome': 'c03_n01',
                          'linha': 70,
                          'metodo': 'calculo_exato'},
                         {'arquivo': 'verificar.py',
                          'nome': 'c03_n01',
                          'linha': 71,
                          'metodo': 'calculo_exato'},
                         {'arquivo': 'verificar.py',
                          'nome': 'c03_n01',
                          'linha': 73,
                          'metodo': 'calculo_exato'}],
                  'wl': [{'arquivo': 'revisaointegral.wl',
                          'nome': 'published_segment_properties',
                          'linha': 16,
                          'metodo': 'calculo_exato'}]},
  'pendencias': {'lean': '', 'py': '', 'wl': ''}},
 {'ids': ['c03.e0056'],
  'expressoes': {'c03.e0056': '\\min(4,5)=4'},
  'proposicao': 'O menor dos tamanhos 4 e 5 é 4.',
  'hipoteses': ['Cardinalidades dos dois conjuntos não vazios publicados.'],
  'alcance': 'completa',
  'observacao': '',
  'testemunhas': {'lean': [{'arquivo': 'RevisaoIntegral.lean',
                            'nome': 'Chapter03IntegralReview.min_cardinalities',
                            'linha': 9,
                            'metodo': 'prova_geral'}],
                  'py': [{'arquivo': 'revisaointegral.py',
                          'nome': 'min_cardinalities',
                          'linha': 7,
                          'metodo': 'identidade_simbolica'}],
                  'wl': [{'arquivo': 'revisaointegral.wl',
                          'nome': 'min_cardinalities',
                          'linha': 6,
                          'metodo': 'identidade_simbolica'}]},
  'pendencias': {'lean': '', 'py': '', 'wl': ''}},
 {'ids': ['c03.e0071'],
  'expressoes': {'c03.e0071': '(\\textit{-a},\\textit{-u})'},
  'proposicao': 'Par de terminações já enumerado na relação morfológica; a ocorrência comenta que duas '
                'classes podem realizar o mesmo par A expressão desta ocorrência é '
                '(\\textit{-a},\\textit{-u}).',
  'hipoteses': ['As convenções e o domínio são os explicitados na prosa adjacente.'],
  'alcance': 'mencao',
  'observacao': 'Par de terminações já enumerado na relação morfológica; a ocorrência comenta que duas '
                'classes podem realizar o mesmo par Não se contabiliza como prova de um resultado '
                'matemático.',
  'testemunhas': {'lean': [], 'py': [], 'wl': []},
  'pendencias': {'lean': '', 'py': '', 'wl': ''}},
 {'ids': ['c03.e0075', 'c03.e0076', 'c03.e0077'],
  'expressoes': {'c03.e0075': 'g(1)=\\textit{-on}',
                 'c03.e0076': 'g(2)=\\textit{-on}',
                 'c03.e0077': 'g(1)=g(2)'},
  'proposicao': 'As classes 1 e 2 têm a mesma saída -on na função de genitivo plural.',
  'hipoteses': ['Função constante no domínio das oito classes; Lean Fin 8 usa índices 0 e 1 para as classes '
                '1 e 2.'],
  'alcance': 'completa',
  'observacao': '',
  'testemunhas': {'lean': [{'arquivo': 'RevisaoIntegral.lean',
                            'nome': 'Chapter03IntegralReview.genitive_plural_values',
                            'linha': 7,
                            'metodo': 'prova_geral'}],
                  'py': [{'arquivo': 'revisaointegral.py',
                          'nome': 'genitive_plural_values',
                          'linha': 6,
                          'metodo': 'identidade_simbolica'}],
                  'wl': [{'arquivo': 'revisaointegral.wl',
                          'nome': 'genitive_plural_values',
                          'linha': 5,
                          'metodo': 'identidade_simbolica'}]},
  'pendencias': {'lean': '', 'py': '', 'wl': ''}},
 {'ids': ['c03.e0100'],
  'expressoes': {'c03.e0100': 'p\\land q'},
  'proposicao': 'Definição bivalente do conectivo ou rótulo da coluna correspondente da tabela-verdade A '
                'expressão desta ocorrência é p\\land q.',
  'hipoteses': ['p,q proposições; conjunção e disjunção inclusiva clássicas; implicação material.'],
  'alcance': 'definicao',
  'observacao': 'Definição bivalente do conectivo ou rótulo da coluna correspondente da tabela-verdade Não '
                'se contabiliza como prova de um resultado matemático.',
  'testemunhas': {'lean': [], 'py': [], 'wl': []},
  'pendencias': {'lean': '', 'py': '', 'wl': ''}},
 {'ids': ['c03.e0101'],
  'expressoes': {'c03.e0101': 'p\\lor q'},
  'proposicao': 'Definição bivalente do conectivo ou rótulo da coluna correspondente da tabela-verdade A '
                'expressão desta ocorrência é p\\lor q.',
  'hipoteses': ['p,q proposições; conjunção e disjunção inclusiva clássicas; implicação material.'],
  'alcance': 'definicao',
  'observacao': 'Definição bivalente do conectivo ou rótulo da coluna correspondente da tabela-verdade Não '
                'se contabiliza como prova de um resultado matemático.',
  'testemunhas': {'lean': [], 'py': [], 'wl': []},
  'pendencias': {'lean': '', 'py': '', 'wl': ''}},
 {'ids': ['c03.e0102'],
  'expressoes': {'c03.e0102': '\\neg p'},
  'proposicao': 'Definição bivalente do conectivo ou rótulo da coluna correspondente da tabela-verdade A '
                'expressão desta ocorrência é \\neg p.',
  'hipoteses': ['p,q proposições; conjunção e disjunção inclusiva clássicas; implicação material.'],
  'alcance': 'definicao',
  'observacao': 'Definição bivalente do conectivo ou rótulo da coluna correspondente da tabela-verdade Não '
                'se contabiliza como prova de um resultado matemático.',
  'testemunhas': {'lean': [], 'py': [], 'wl': []},
  'pendencias': {'lean': '', 'py': '', 'wl': ''}},
 {'ids': ['c03.e0107'],
  'expressoes': {'c03.e0107': 'p\\Rightarrow q'},
  'proposicao': 'Definição bivalente do conectivo ou rótulo da coluna correspondente da tabela-verdade A '
                'expressão desta ocorrência é p\\Rightarrow q.',
  'hipoteses': ['p,q proposições; conjunção e disjunção inclusiva clássicas; implicação material.'],
  'alcance': 'definicao',
  'observacao': 'Definição bivalente do conectivo ou rótulo da coluna correspondente da tabela-verdade Não '
                'se contabiliza como prova de um resultado matemático.',
  'testemunhas': {'lean': [], 'py': [], 'wl': []},
  'pendencias': {'lean': '', 'py': '', 'wl': ''}},
 {'ids': ['c03.e0112'],
  'expressoes': {'c03.e0112': '\\neg p'},
  'proposicao': 'Definição bivalente do conectivo ou rótulo da coluna correspondente da tabela-verdade A '
                'expressão desta ocorrência é \\neg p.',
  'hipoteses': ['p,q proposições; conjunção e disjunção inclusiva clássicas; implicação material.'],
  'alcance': 'definicao',
  'observacao': 'Definição bivalente do conectivo ou rótulo da coluna correspondente da tabela-verdade Não '
                'se contabiliza como prova de um resultado matemático.',
  'testemunhas': {'lean': [], 'py': [], 'wl': []},
  'pendencias': {'lean': '', 'py': '', 'wl': ''}},
 {'ids': ['c03.e0113'],
  'expressoes': {'c03.e0113': 'p\\land q'},
  'proposicao': 'Definição bivalente do conectivo ou rótulo da coluna correspondente da tabela-verdade A '
                'expressão desta ocorrência é p\\land q.',
  'hipoteses': ['p,q proposições; conjunção e disjunção inclusiva clássicas; implicação material.'],
  'alcance': 'definicao',
  'observacao': 'Definição bivalente do conectivo ou rótulo da coluna correspondente da tabela-verdade Não '
                'se contabiliza como prova de um resultado matemático.',
  'testemunhas': {'lean': [], 'py': [], 'wl': []},
  'pendencias': {'lean': '', 'py': '', 'wl': ''}},
 {'ids': ['c03.e0114'],
  'expressoes': {'c03.e0114': 'p\\lor q'},
  'proposicao': 'Definição bivalente do conectivo ou rótulo da coluna correspondente da tabela-verdade A '
                'expressão desta ocorrência é p\\lor q.',
  'hipoteses': ['p,q proposições; conjunção e disjunção inclusiva clássicas; implicação material.'],
  'alcance': 'definicao',
  'observacao': 'Definição bivalente do conectivo ou rótulo da coluna correspondente da tabela-verdade Não '
                'se contabiliza como prova de um resultado matemático.',
  'testemunhas': {'lean': [], 'py': [], 'wl': []},
  'pendencias': {'lean': '', 'py': '', 'wl': ''}},
 {'ids': ['c03.e0115'],
  'expressoes': {'c03.e0115': 'p\\Rightarrow q'},
  'proposicao': 'Definição bivalente do conectivo ou rótulo da coluna correspondente da tabela-verdade A '
                'expressão desta ocorrência é p\\Rightarrow q.',
  'hipoteses': ['p,q proposições; conjunção e disjunção inclusiva clássicas; implicação material.'],
  'alcance': 'definicao',
  'observacao': 'Definição bivalente do conectivo ou rótulo da coluna correspondente da tabela-verdade Não '
                'se contabiliza como prova de um resultado matemático.',
  'testemunhas': {'lean': [], 'py': [], 'wl': []},
  'pendencias': {'lean': '', 'py': '', 'wl': ''}},
 {'ids': ['c03.e0104'],
  'expressoes': {'c03.e0104': 'p\\lor q'},
  'proposicao': 'Premissa proposicional mantida na inferência ou na seleção de linhas da tabela-verdade A '
                'expressão desta ocorrência é p\\lor q.',
  'hipoteses': ['p significa pediu café; q significa pediu chá; não são afirmações de um evento observado.'],
  'alcance': 'hipotese',
  'observacao': 'Premissa proposicional mantida na inferência ou na seleção de linhas da tabela-verdade Não '
                'se contabiliza como prova de um resultado matemático.',
  'testemunhas': {'lean': [], 'py': [], 'wl': []},
  'pendencias': {'lean': '', 'py': '', 'wl': ''}},
 {'ids': ['c03.e0105'],
  'expressoes': {'c03.e0105': '\\neg p'},
  'proposicao': 'Premissa proposicional mantida na inferência ou na seleção de linhas da tabela-verdade A '
                'expressão desta ocorrência é \\neg p.',
  'hipoteses': ['p significa pediu café; q significa pediu chá; não são afirmações de um evento observado.'],
  'alcance': 'hipotese',
  'observacao': 'Premissa proposicional mantida na inferência ou na seleção de linhas da tabela-verdade Não '
                'se contabiliza como prova de um resultado matemático.',
  'testemunhas': {'lean': [], 'py': [], 'wl': []},
  'pendencias': {'lean': '', 'py': '', 'wl': ''}},
 {'ids': ['c03.e0116'],
  'expressoes': {'c03.e0116': 'p\\lor q'},
  'proposicao': 'Premissa proposicional mantida na inferência ou na seleção de linhas da tabela-verdade A '
                'expressão desta ocorrência é p\\lor q.',
  'hipoteses': ['p significa pediu café; q significa pediu chá; não são afirmações de um evento observado.'],
  'alcance': 'hipotese',
  'observacao': 'Premissa proposicional mantida na inferência ou na seleção de linhas da tabela-verdade Não '
                'se contabiliza como prova de um resultado matemático.',
  'testemunhas': {'lean': [], 'py': [], 'wl': []},
  'pendencias': {'lean': '', 'py': '', 'wl': ''}},
 {'ids': ['c03.e0117'],
  'expressoes': {'c03.e0117': '\\neg p'},
  'proposicao': 'Premissa proposicional mantida na inferência ou na seleção de linhas da tabela-verdade A '
                'expressão desta ocorrência é \\neg p.',
  'hipoteses': ['p significa pediu café; q significa pediu chá; não são afirmações de um evento observado.'],
  'alcance': 'hipotese',
  'observacao': 'Premissa proposicional mantida na inferência ou na seleção de linhas da tabela-verdade Não '
                'se contabiliza como prova de um resultado matemático.',
  'testemunhas': {'lean': [], 'py': [], 'wl': []},
  'pendencias': {'lean': '', 'py': '', 'wl': ''}},
 {'ids': ['c03.e0119'],
  'expressoes': {'c03.e0119': 'p\\lor q'},
  'proposicao': 'Premissa proposicional mantida na inferência ou na seleção de linhas da tabela-verdade A '
                'expressão desta ocorrência é p\\lor q.',
  'hipoteses': ['p significa pediu café; q significa pediu chá; não são afirmações de um evento observado.'],
  'alcance': 'hipotese',
  'observacao': 'Premissa proposicional mantida na inferência ou na seleção de linhas da tabela-verdade Não '
                'se contabiliza como prova de um resultado matemático.',
  'testemunhas': {'lean': [], 'py': [], 'wl': []},
  'pendencias': {'lean': '', 'py': '', 'wl': ''}},
 {'ids': ['c03.e0122'],
  'expressoes': {'c03.e0122': 'p\\Rightarrow q'},
  'proposicao': 'Premissa proposicional mantida na inferência ou na seleção de linhas da tabela-verdade A '
                'expressão desta ocorrência é p\\Rightarrow q.',
  'hipoteses': ['p significa pediu café; q significa pediu chá; não são afirmações de um evento observado.'],
  'alcance': 'hipotese',
  'observacao': 'Premissa proposicional mantida na inferência ou na seleção de linhas da tabela-verdade Não '
                'se contabiliza como prova de um resultado matemático.',
  'testemunhas': {'lean': [], 'py': [], 'wl': []},
  'pendencias': {'lean': '', 'py': '', 'wl': ''}},
 {'ids': ['c03.e0123'],
  'expressoes': {'c03.e0123': 'p'},
  'proposicao': 'Premissa proposicional mantida na inferência ou na seleção de linhas da tabela-verdade A '
                'expressão desta ocorrência é p.',
  'hipoteses': ['p significa pediu café; q significa pediu chá; não são afirmações de um evento observado.'],
  'alcance': 'hipotese',
  'observacao': 'Premissa proposicional mantida na inferência ou na seleção de linhas da tabela-verdade Não '
                'se contabiliza como prova de um resultado matemático.',
  'testemunhas': {'lean': [], 'py': [], 'wl': []},
  'pendencias': {'lean': '', 'py': '', 'wl': ''}},
 {'ids': ['c03.e0126'],
  'expressoes': {'c03.e0126': 'p'},
  'proposicao': 'Premissa proposicional mantida na inferência ou na seleção de linhas da tabela-verdade A '
                'expressão desta ocorrência é p.',
  'hipoteses': ['p significa pediu café; q significa pediu chá; não são afirmações de um evento observado.'],
  'alcance': 'hipotese',
  'observacao': 'Premissa proposicional mantida na inferência ou na seleção de linhas da tabela-verdade Não '
                'se contabiliza como prova de um resultado matemático.',
  'testemunhas': {'lean': [], 'py': [], 'wl': []},
  'pendencias': {'lean': '', 'py': '', 'wl': ''}},
 {'ids': ['c03.e0106', 'c03.e0118'],
  'expressoes': {'c03.e0106': 'q', 'c03.e0118': 'q'},
  'proposicao': 'Das premissas p ou q e não p, conclui-se q.',
  'hipoteses': ['p,q proposições bivalentes; disjunção inclusiva e negação assumidas.'],
  'alcance': 'completa',
  'observacao': '',
  'testemunhas': {'lean': [{'arquivo': 'Verificar.lean',
                            'nome': 'Chapter03.c03_r04.disjunctionElimination',
                            'linha': 56,
                            'metodo': 'prova_geral'}],
                  'py': [{'arquivo': 'verificar.py',
                          'nome': 'c03_r04',
                          'linha': 35,
                          'metodo': 'calculo_exato'}],
                  'wl': [{'arquivo': 'verificar.wl',
                          'nome': 'c03_r04',
                          'linha': 15,
                          'metodo': 'identidade_simbolica'}]},
  'pendencias': {'lean': '', 'py': '', 'wl': ''}},
 {'ids': ['c03.e0120'],
  'expressoes': {'c03.e0120': 'q'},
  'proposicao': 'Somente p ou q não basta para concluir q: p verdadeiro e q falso é contramodelo.',
  'hipoteses': ['Lógica clássica; ausência da premissa não p.'],
  'alcance': 'completa',
  'observacao': '',
  'testemunhas': {'lean': [{'arquivo': 'RevisaoIntegral.lean',
                            'nome': 'Chapter03IntegralReview.disjunction_without_negation',
                            'linha': 11,
                            'metodo': 'prova_geral'}],
                  'py': [{'arquivo': 'revisaointegral.py',
                          'nome': 'disjunction_without_negation',
                          'linha': 8,
                          'metodo': 'identidade_simbolica'}],
                  'wl': [{'arquivo': 'revisaointegral.wl',
                          'nome': 'disjunction_without_negation',
                          'linha': 7,
                          'metodo': 'identidade_simbolica'}]},
  'pendencias': {'lean': '', 'py': '', 'wl': ''}},
 {'ids': ['c03.e0127'],
  'expressoes': {'c03.e0127': 'q'},
  'proposicao': 'Modus ponens: p implica q e p autorizam q.',
  'hipoteses': ['Ambas as premissas p→q e p são necessárias.'],
  'alcance': 'completa',
  'observacao': '',
  'testemunhas': {'lean': [{'arquivo': 'Verificar.lean',
                            'nome': 'Chapter03.c03_r04.modusPonens',
                            'linha': 57,
                            'metodo': 'prova_geral'}],
                  'py': [{'arquivo': 'verificar.py',
                          'nome': 'c03_r04',
                          'linha': 36,
                          'metodo': 'calculo_exato'}],
                  'wl': [{'arquivo': 'verificar.wl',
                          'nome': 'c03_r04',
                          'linha': 16,
                          'metodo': 'identidade_simbolica'}]},
  'pendencias': {'lean': '', 'py': '', 'wl': ''}},
 {'ids': ['c03.e0103'],
  'expressoes': {'c03.e0103': 'p'},
  'proposicao': 'A prosa identifica valorações verdadeiras ou falsas da tabela; não afirma p ou q '
                'incondicionalmente A expressão desta ocorrência é p.',
  'hipoteses': ['As convenções e o domínio são os explicitados na prosa adjacente.'],
  'alcance': 'mencao',
  'observacao': 'A prosa identifica valorações verdadeiras ou falsas da tabela; não afirma p ou q '
                'incondicionalmente Não se contabiliza como prova de um resultado matemático.',
  'testemunhas': {'lean': [], 'py': [], 'wl': []},
  'pendencias': {'lean': '', 'py': '', 'wl': ''}},
 {'ids': ['c03.e0108'],
  'expressoes': {'c03.e0108': 'p'},
  'proposicao': 'A prosa identifica valorações verdadeiras ou falsas da tabela; não afirma p ou q '
                'incondicionalmente A expressão desta ocorrência é p.',
  'hipoteses': ['As convenções e o domínio são os explicitados na prosa adjacente.'],
  'alcance': 'mencao',
  'observacao': 'A prosa identifica valorações verdadeiras ou falsas da tabela; não afirma p ou q '
                'incondicionalmente Não se contabiliza como prova de um resultado matemático.',
  'testemunhas': {'lean': [], 'py': [], 'wl': []},
  'pendencias': {'lean': '', 'py': '', 'wl': ''}},
 {'ids': ['c03.e0109'],
  'expressoes': {'c03.e0109': 'q'},
  'proposicao': 'A prosa identifica valorações verdadeiras ou falsas da tabela; não afirma p ou q '
                'incondicionalmente A expressão desta ocorrência é q.',
  'hipoteses': ['As convenções e o domínio são os explicitados na prosa adjacente.'],
  'alcance': 'mencao',
  'observacao': 'A prosa identifica valorações verdadeiras ou falsas da tabela; não afirma p ou q '
                'incondicionalmente Não se contabiliza como prova de um resultado matemático.',
  'testemunhas': {'lean': [], 'py': [], 'wl': []},
  'pendencias': {'lean': '', 'py': '', 'wl': ''}},
 {'ids': ['c03.e0121'],
  'expressoes': {'c03.e0121': 'p'},
  'proposicao': 'A prosa identifica valorações verdadeiras ou falsas da tabela; não afirma p ou q '
                'incondicionalmente A expressão desta ocorrência é p.',
  'hipoteses': ['As convenções e o domínio são os explicitados na prosa adjacente.'],
  'alcance': 'mencao',
  'observacao': 'A prosa identifica valorações verdadeiras ou falsas da tabela; não afirma p ou q '
                'incondicionalmente Não se contabiliza como prova de um resultado matemático.',
  'testemunhas': {'lean': [], 'py': [], 'wl': []},
  'pendencias': {'lean': '', 'py': '', 'wl': ''}},
 {'ids': ['c03.e0124'],
  'expressoes': {'c03.e0124': 'p'},
  'proposicao': 'A prosa identifica valorações verdadeiras ou falsas da tabela; não afirma p ou q '
                'incondicionalmente A expressão desta ocorrência é p.',
  'hipoteses': ['As convenções e o domínio são os explicitados na prosa adjacente.'],
  'alcance': 'mencao',
  'observacao': 'A prosa identifica valorações verdadeiras ou falsas da tabela; não afirma p ou q '
                'incondicionalmente Não se contabiliza como prova de um resultado matemático.',
  'testemunhas': {'lean': [], 'py': [], 'wl': []},
  'pendencias': {'lean': '', 'py': '', 'wl': ''}},
 {'ids': ['c03.e0125'],
  'expressoes': {'c03.e0125': 'q'},
  'proposicao': 'A prosa identifica valorações verdadeiras ou falsas da tabela; não afirma p ou q '
                'incondicionalmente A expressão desta ocorrência é q.',
  'hipoteses': ['As convenções e o domínio são os explicitados na prosa adjacente.'],
  'alcance': 'mencao',
  'observacao': 'A prosa identifica valorações verdadeiras ou falsas da tabela; não afirma p ou q '
                'incondicionalmente Não se contabiliza como prova de um resultado matemático.',
  'testemunhas': {'lean': [], 'py': [], 'wl': []},
  'pendencias': {'lean': '', 'py': '', 'wl': ''}},
 {'ids': ['c03.e0132'],
  'expressoes': {'c03.e0132': 'F(y)'},
  'proposicao': 'Predicados de fazendeiro, burro e relação de posse, com ordem dos argumentos declarada A '
                'expressão desta ocorrência é F(y).',
  'hipoteses': ['Domínio de indivíduos E; F,D unários; R binário; primeiro argumento é possuidor.'],
  'alcance': 'definicao',
  'observacao': 'Predicados de fazendeiro, burro e relação de posse, com ordem dos argumentos declarada Não '
                'se contabiliza como prova de um resultado matemático.',
  'testemunhas': {'lean': [], 'py': [], 'wl': []},
  'pendencias': {'lean': '', 'py': '', 'wl': ''}},
 {'ids': ['c03.e0133'],
  'expressoes': {'c03.e0133': 'D(x)'},
  'proposicao': 'Predicados de fazendeiro, burro e relação de posse, com ordem dos argumentos declarada A '
                'expressão desta ocorrência é D(x).',
  'hipoteses': ['Domínio de indivíduos E; F,D unários; R binário; primeiro argumento é possuidor.'],
  'alcance': 'definicao',
  'observacao': 'Predicados de fazendeiro, burro e relação de posse, com ordem dos argumentos declarada Não '
                'se contabiliza como prova de um resultado matemático.',
  'testemunhas': {'lean': [], 'py': [], 'wl': []},
  'pendencias': {'lean': '', 'py': '', 'wl': ''}},
 {'ids': ['c03.e0134'],
  'expressoes': {'c03.e0134': 'R(y,x)'},
  'proposicao': 'Predicados de fazendeiro, burro e relação de posse, com ordem dos argumentos declarada A '
                'expressão desta ocorrência é R(y,x).',
  'hipoteses': ['Domínio de indivíduos E; F,D unários; R binário; primeiro argumento é possuidor.'],
  'alcance': 'definicao',
  'observacao': 'Predicados de fazendeiro, burro e relação de posse, com ordem dos argumentos declarada Não '
                'se contabiliza como prova de um resultado matemático.',
  'testemunhas': {'lean': [], 'py': [], 'wl': []},
  'pendencias': {'lean': '', 'py': '', 'wl': ''}},
 {'ids': ['c03.e0135'],
  'expressoes': {'c03.e0135': 'R(y,x)'},
  'proposicao': 'Releitura de um predicado no escopo de quantificadores; suas condições são premissas locais '
                'da interpretação A expressão desta ocorrência é R(y,x).',
  'hipoteses': ['As convenções e o domínio são os explicitados na prosa adjacente.'],
  'alcance': 'mencao',
  'observacao': 'Releitura de um predicado no escopo de quantificadores; suas condições são premissas locais '
                'da interpretação Não se contabiliza como prova de um resultado matemático.',
  'testemunhas': {'lean': [], 'py': [], 'wl': []},
  'pendencias': {'lean': '', 'py': '', 'wl': ''}},
 {'ids': ['c03.e0138'],
  'expressoes': {'c03.e0138': 'F(y)'},
  'proposicao': 'Releitura de um predicado no escopo de quantificadores; suas condições são premissas locais '
                'da interpretação A expressão desta ocorrência é F(y).',
  'hipoteses': ['As convenções e o domínio são os explicitados na prosa adjacente.'],
  'alcance': 'mencao',
  'observacao': 'Releitura de um predicado no escopo de quantificadores; suas condições são premissas locais '
                'da interpretação Não se contabiliza como prova de um resultado matemático.',
  'testemunhas': {'lean': [], 'py': [], 'wl': []},
  'pendencias': {'lean': '', 'py': '', 'wl': ''}},
 {'ids': ['c03.e0140'],
  'expressoes': {'c03.e0140': 'D(x)'},
  'proposicao': 'Releitura de um predicado no escopo de quantificadores; suas condições são premissas locais '
                'da interpretação A expressão desta ocorrência é D(x).',
  'hipoteses': ['As convenções e o domínio são os explicitados na prosa adjacente.'],
  'alcance': 'mencao',
  'observacao': 'Releitura de um predicado no escopo de quantificadores; suas condições são premissas locais '
                'da interpretação Não se contabiliza como prova de um resultado matemático.',
  'testemunhas': {'lean': [], 'py': [], 'wl': []},
  'pendencias': {'lean': '', 'py': '', 'wl': ''}},
 {'ids': ['c03.e0141'],
  'expressoes': {'c03.e0141': 'R(y,x)'},
  'proposicao': 'Releitura de um predicado no escopo de quantificadores; suas condições são premissas locais '
                'da interpretação A expressão desta ocorrência é R(y,x).',
  'hipoteses': ['As convenções e o domínio são os explicitados na prosa adjacente.'],
  'alcance': 'mencao',
  'observacao': 'Releitura de um predicado no escopo de quantificadores; suas condições são premissas locais '
                'da interpretação Não se contabiliza como prova de um resultado matemático.',
  'testemunhas': {'lean': [], 'py': [], 'wl': []},
  'pendencias': {'lean': '', 'py': '', 'wl': ''}},
 {'ids': ['c03.e0155'],
  'expressoes': {'c03.e0155': 'F(y)'},
  'proposicao': 'Releitura de um predicado no escopo de quantificadores; suas condições são premissas locais '
                'da interpretação A expressão desta ocorrência é F(y).',
  'hipoteses': ['As convenções e o domínio são os explicitados na prosa adjacente.'],
  'alcance': 'mencao',
  'observacao': 'Releitura de um predicado no escopo de quantificadores; suas condições são premissas locais '
                'da interpretação Não se contabiliza como prova de um resultado matemático.',
  'testemunhas': {'lean': [], 'py': [], 'wl': []},
  'pendencias': {'lean': '', 'py': '', 'wl': ''}},
 {'ids': ['c03.e0157'],
  'expressoes': {'c03.e0157': 'D(x)'},
  'proposicao': 'Releitura de um predicado no escopo de quantificadores; suas condições são premissas locais '
                'da interpretação A expressão desta ocorrência é D(x).',
  'hipoteses': ['As convenções e o domínio são os explicitados na prosa adjacente.'],
  'alcance': 'mencao',
  'observacao': 'Releitura de um predicado no escopo de quantificadores; suas condições são premissas locais '
                'da interpretação Não se contabiliza como prova de um resultado matemático.',
  'testemunhas': {'lean': [], 'py': [], 'wl': []},
  'pendencias': {'lean': '', 'py': '', 'wl': ''}},
 {'ids': ['c03.e0156'],
  'expressoes': {'c03.e0156': 'R(y,x)'},
  'proposicao': 'Instanciar a condição universal com a testemunha comum fornece a relação R(y,x) para o '
                'fazendeiro fixado.',
  'hipoteses': ['Domínio E arbitrário; F,D predicados e R relação; nenhuma importação existencial é imposta '
                'à universal.',
                'x testemunha de D(x) e de ∀y(F(y)→R(y,x)); y arbitrário com F(y).',
                'Certificado de dedução natural com introdução/eliminação de quantificadores, escopo de '
                'variáveis, substituição sem captura e controle de testemunha fresca; o domínio pode ser '
                'vazio. A dupla negação e o terceiro excluído são regras da lógica clássica.'],
  'alcance': 'completa',
  'observacao': 'Cada testemunha CAS verifica uma árvore finita de prova ou o esquema completo de indução, '
                'com suas condições laterais; não é amostragem de indivíduos ou de comprimentos.',
  'testemunhas': {'lean': [{'arquivo': 'Condicoes.lean',
                            'nome': 'Chapter03Conditions.inverse_implies_surface',
                            'linha': 64,
                            'metodo': 'prova_geral'},
                           {'arquivo': 'Condicoes.lean',
                            'nome': 'Chapter03Conditions.surface_not_inverse',
                            'linha': 70,
                            'metodo': 'prova_geral'}],
                  'py': [{'arquivo': 'deducao.py',
                          'nome': 'common_witness_entails_surface',
                          'metodo': 'deducao_natural',
                          'linha': 185},
                         {'arquivo': 'deducao.py',
                          'nome': 'quantifier_swap_countermodel',
                          'metodo': 'calculo_exato',
                          'linha': 204},
                         {'arquivo': 'deducao.py',
                          'nome': 'no_quantifier_swap',
                          'metodo': 'calculo_exato',
                          'linha': 202},
                         {'arquivo': 'deducao.py',
                          'nome': 'no_escaping_existential_witness',
                          'metodo': 'calculo_exato',
                          'linha': 197}],
                  'wl': [{'arquivo': 'deducao.wl',
                          'nome': 'common_witness_entails_surface',
                          'metodo': 'deducao_natural',
                          'linha': 47},
                         {'arquivo': 'deducao.wl',
                          'nome': 'quantifier_swap_countermodel',
                          'metodo': 'calculo_exato',
                          'linha': 66},
                         {'arquivo': 'deducao.wl',
                          'nome': 'no_quantifier_swap',
                          'metodo': 'calculo_exato',
                          'linha': 64},
                         {'arquivo': 'deducao.wl',
                          'nome': 'no_escaping_existential_witness',
                          'metodo': 'calculo_exato',
                          'linha': 59}]},
  'pendencias': {'lean': '', 'py': '', 'wl': ''}},
 {'ids': ['c03.e0176'],
  'expressoes': {'c03.e0176': 'L\\subseteq M'},
  'proposicao': 'De L⊆N e N⊆M, conclui-se L⊆M por transitividade da inclusão.',
  'hipoteses': ['L,N,M subconjuntos do mesmo universo; L⊆N e N⊆M.',
                'Certificado de dedução natural com introdução/eliminação de quantificadores, escopo de '
                'variáveis, substituição sem captura e controle de testemunha fresca; o domínio pode ser '
                'vazio. A dupla negação e o terceiro excluído são regras da lógica clássica.'],
  'alcance': 'completa',
  'observacao': 'Cada testemunha CAS verifica uma árvore finita de prova ou o esquema completo de indução, '
                'com suas condições laterais; não é amostragem de indivíduos ou de comprimentos.',
  'testemunhas': {'lean': [{'arquivo': 'Verificar.lean',
                            'nome': 'Chapter03.c03_d01.inclusionChain',
                            'linha': 82,
                            'metodo': 'prova_geral'}],
                  'py': [{'arquivo': 'deducao.py',
                          'nome': 'subset_transitivity',
                          'metodo': 'deducao_natural',
                          'linha': 184}],
                  'wl': [{'arquivo': 'deducao.wl',
                          'nome': 'subset_transitivity',
                          'metodo': 'deducao_natural',
                          'linha': 46}]},
  'pendencias': {'lean': '', 'py': '', 'wl': ''}},
 {'ids': ['c03.e0177'],
  'expressoes': {'c03.e0177': 'P(x)'},
  'proposicao': 'Predicado arbitrário e negação de sua quantificação universal; a equivalência é examinada '
                'em c03.e0180 A expressão desta ocorrência é P(x).',
  'hipoteses': ['Lógica clássica; domínio fixado; nenhuma existência presumida.'],
  'alcance': 'definicao',
  'observacao': 'Predicado arbitrário e negação de sua quantificação universal; a equivalência é examinada '
                'em c03.e0180 Não se contabiliza como prova de um resultado matemático.',
  'testemunhas': {'lean': [], 'py': [], 'wl': []},
  'pendencias': {'lean': '', 'py': '', 'wl': ''}},
 {'ids': ['c03.e0178'],
  'expressoes': {'c03.e0178': '\\neg\\forall x\\,P(x)'},
  'proposicao': 'Predicado arbitrário e negação de sua quantificação universal; a equivalência é examinada '
                'em c03.e0180 A expressão desta ocorrência é \\neg\\forall x\\,P(x).',
  'hipoteses': ['Lógica clássica; domínio fixado; nenhuma existência presumida.'],
  'alcance': 'definicao',
  'observacao': 'Predicado arbitrário e negação de sua quantificação universal; a equivalência é examinada '
                'em c03.e0180 Não se contabiliza como prova de um resultado matemático.',
  'testemunhas': {'lean': [], 'py': [], 'wl': []},
  'pendencias': {'lean': '', 'py': '', 'wl': ''}},
 {'ids': ['c03.e0186'],
  'expressoes': {'c03.e0186': 'uv'},
  'proposicao': 'Duas grafias da concatenação de cadeias; o ponto não é multiplicação de palavras A '
                'expressão desta ocorrência é uv.',
  'hipoteses': ['As convenções e o domínio são os explicitados na prosa adjacente.'],
  'alcance': 'notacao',
  'observacao': 'Duas grafias da concatenação de cadeias; o ponto não é multiplicação de palavras Não se '
                'contabiliza como prova de um resultado matemático.',
  'testemunhas': {'lean': [], 'py': [], 'wl': []},
  'pendencias': {'lean': '', 'py': '', 'wl': ''}},
 {'ids': ['c03.e0187'],
  'expressoes': {'c03.e0187': 'u\\mathbin{\\cdot}v'},
  'proposicao': 'Duas grafias da concatenação de cadeias; o ponto não é multiplicação de palavras A '
                'expressão desta ocorrência é u\\mathbin{\\cdot}v.',
  'hipoteses': ['As convenções e o domínio são os explicitados na prosa adjacente.'],
  'alcance': 'notacao',
  'observacao': 'Duas grafias da concatenação de cadeias; o ponto não é multiplicação de palavras Não se '
                'contabiliza como prova de um resultado matemático.',
  'testemunhas': {'lean': [], 'py': [], 'wl': []},
  'pendencias': {'lean': '', 'py': '', 'wl': ''}},
 {'ids': ['c03.e0199'],
  'expressoes': {'c03.e0199': 'E\\to\\mathrm{Prop}'},
  'proposicao': 'Tipo de função ou termo lambda explicitamente introduzido na composição semântica A '
                'expressão desta ocorrência é E\\to\\mathrm{Prop}.',
  'hipoteses': ['E domínio de entidades; Prop proposições; entradas individuais e predicativas não são '
                'intercambiáveis.'],
  'alcance': 'definicao',
  'observacao': 'Tipo de função ou termo lambda explicitamente introduzido na composição semântica Não se '
                'contabiliza como prova de um resultado matemático.',
  'testemunhas': {'lean': [], 'py': [], 'wl': []},
  'pendencias': {'lean': '', 'py': '', 'wl': ''}},
 {'ids': ['c03.e0206'],
  'expressoes': {'c03.e0206': 'E\\to\\mathrm{Prop}'},
  'proposicao': 'Tipo de função ou termo lambda explicitamente introduzido na composição semântica A '
                'expressão desta ocorrência é E\\to\\mathrm{Prop}.',
  'hipoteses': ['E domínio de entidades; Prop proposições; entradas individuais e predicativas não são '
                'intercambiáveis.'],
  'alcance': 'definicao',
  'observacao': 'Tipo de função ou termo lambda explicitamente introduzido na composição semântica Não se '
                'contabiliza como prova de um resultado matemático.',
  'testemunhas': {'lean': [], 'py': [], 'wl': []},
  'pendencias': {'lean': '', 'py': '', 'wl': ''}},
 {'ids': ['c03.e0209'],
  'expressoes': {'c03.e0209': '\\lambda x.\\,W(x)'},
  'proposicao': 'Tipo de função ou termo lambda explicitamente introduzido na composição semântica A '
                'expressão desta ocorrência é \\lambda x.\\,W(x).',
  'hipoteses': ['E domínio de entidades; Prop proposições; entradas individuais e predicativas não são '
                'intercambiáveis.'],
  'alcance': 'definicao',
  'observacao': 'Tipo de função ou termo lambda explicitamente introduzido na composição semântica Não se '
                'contabiliza como prova de um resultado matemático.',
  'testemunhas': {'lean': [], 'py': [], 'wl': []},
  'pendencias': {'lean': '', 'py': '', 'wl': ''}},
 {'ids': ['c03.e0219'],
  'expressoes': {'c03.e0219': 'E\\to\\mathrm{Prop}'},
  'proposicao': 'Tipo de função ou termo lambda explicitamente introduzido na composição semântica A '
                'expressão desta ocorrência é E\\to\\mathrm{Prop}.',
  'hipoteses': ['E domínio de entidades; Prop proposições; entradas individuais e predicativas não são '
                'intercambiáveis.'],
  'alcance': 'definicao',
  'observacao': 'Tipo de função ou termo lambda explicitamente introduzido na composição semântica Não se '
                'contabiliza como prova de um resultado matemático.',
  'testemunhas': {'lean': [], 'py': [], 'wl': []},
  'pendencias': {'lean': '', 'py': '', 'wl': ''}},
 {'ids': ['c03.e0227'],
  'expressoes': {'c03.e0227': '(E\\to\\mathrm{Prop})\\to\\mathrm{Prop}'},
  'proposicao': 'Tipo de função ou termo lambda explicitamente introduzido na composição semântica A '
                'expressão desta ocorrência é (E\\to\\mathrm{Prop})\\to\\mathrm{Prop}.',
  'hipoteses': ['E domínio de entidades; Prop proposições; entradas individuais e predicativas não são '
                'intercambiáveis.'],
  'alcance': 'definicao',
  'observacao': 'Tipo de função ou termo lambda explicitamente introduzido na composição semântica Não se '
                'contabiliza como prova de um resultado matemático.',
  'testemunhas': {'lean': [], 'py': [], 'wl': []},
  'pendencias': {'lean': '', 'py': '', 'wl': ''}},
 {'ids': ['c03.e0228'],
  'expressoes': {'c03.e0228': 'E\\to\\mathrm{Prop}'},
  'proposicao': 'Tipo de função ou termo lambda explicitamente introduzido na composição semântica A '
                'expressão desta ocorrência é E\\to\\mathrm{Prop}.',
  'hipoteses': ['E domínio de entidades; Prop proposições; entradas individuais e predicativas não são '
                'intercambiáveis.'],
  'alcance': 'definicao',
  'observacao': 'Tipo de função ou termo lambda explicitamente introduzido na composição semântica Não se '
                'contabiliza como prova de um resultado matemático.',
  'testemunhas': {'lean': [], 'py': [], 'wl': []},
  'pendencias': {'lean': '', 'py': '', 'wl': ''}},
 {'ids': ['c03.e0233'],
  'expressoes': {'c03.e0233': '\\lambda z.\\,O(x,z)'},
  'proposicao': 'Tipo de função ou termo lambda explicitamente introduzido na composição semântica A '
                'expressão desta ocorrência é \\lambda z.\\,O(x,z).',
  'hipoteses': ['E domínio de entidades; Prop proposições; entradas individuais e predicativas não são '
                'intercambiáveis.'],
  'alcance': 'definicao',
  'observacao': 'Tipo de função ou termo lambda explicitamente introduzido na composição semântica Não se '
                'contabiliza como prova de um resultado matemático.',
  'testemunhas': {'lean': [], 'py': [], 'wl': []},
  'pendencias': {'lean': '', 'py': '', 'wl': ''}},
 {'ids': ['c03.e0253'],
  'expressoes': {'c03.e0253': '(E\\to\\mathrm{Prop})\\to\\mathrm{Prop}'},
  'proposicao': 'Tipo de função ou termo lambda explicitamente introduzido na composição semântica A '
                'expressão desta ocorrência é (E\\to\\mathrm{Prop})\\to\\mathrm{Prop}.',
  'hipoteses': ['E domínio de entidades; Prop proposições; entradas individuais e predicativas não são '
                'intercambiáveis.'],
  'alcance': 'definicao',
  'observacao': 'Tipo de função ou termo lambda explicitamente introduzido na composição semântica Não se '
                'contabiliza como prova de um resultado matemático.',
  'testemunhas': {'lean': [], 'py': [], 'wl': []},
  'pendencias': {'lean': '', 'py': '', 'wl': ''}},
 {'ids': ['c03.e0295'],
  'expressoes': {'c03.e0295': 'E\\to\\mathrm{Prop}'},
  'proposicao': 'Tipo de função ou termo lambda explicitamente introduzido na composição semântica A '
                'expressão desta ocorrência é E\\to\\mathrm{Prop}.',
  'hipoteses': ['E domínio de entidades; Prop proposições; entradas individuais e predicativas não são '
                'intercambiáveis.'],
  'alcance': 'definicao',
  'observacao': 'Tipo de função ou termo lambda explicitamente introduzido na composição semântica Não se '
                'contabiliza como prova de um resultado matemático.',
  'testemunhas': {'lean': [], 'py': [], 'wl': []},
  'pendencias': {'lean': '', 'py': '', 'wl': ''}},
 {'ids': ['c03.e0310'],
  'expressoes': {'c03.e0310': '\\mathrm{Prop}\\to\\mathrm{Prop}'},
  'proposicao': 'Tipo de função ou termo lambda explicitamente introduzido na composição semântica A '
                'expressão desta ocorrência é \\mathrm{Prop}\\to\\mathrm{Prop}.',
  'hipoteses': ['E domínio de entidades; Prop proposições; entradas individuais e predicativas não são '
                'intercambiáveis.'],
  'alcance': 'definicao',
  'observacao': 'Tipo de função ou termo lambda explicitamente introduzido na composição semântica Não se '
                'contabiliza como prova de um resultado matemático.',
  'testemunhas': {'lean': [], 'py': [], 'wl': []},
  'pendencias': {'lean': '', 'py': '', 'wl': ''}},
 {'ids': ['c03.e0201'],
  'expressoes': {'c03.e0201': 'W(x)'},
  'proposicao': 'Predicados lexicais W,T,O abreviam mulher, chá e pedir na análise publicada A expressão '
                'desta ocorrência é W(x).',
  'hipoteses': ['W,T:E→Prop; O:E→E→Prop; ordem de argumentos preservada.'],
  'alcance': 'definicao',
  'observacao': 'Predicados lexicais W,T,O abreviam mulher, chá e pedir na análise publicada Não se '
                'contabiliza como prova de um resultado matemático.',
  'testemunhas': {'lean': [], 'py': [], 'wl': []},
  'pendencias': {'lean': '', 'py': '', 'wl': ''}},
 {'ids': ['c03.e0202'],
  'expressoes': {'c03.e0202': 'T(y)'},
  'proposicao': 'Predicados lexicais W,T,O abreviam mulher, chá e pedir na análise publicada A expressão '
                'desta ocorrência é T(y).',
  'hipoteses': ['W,T:E→Prop; O:E→E→Prop; ordem de argumentos preservada.'],
  'alcance': 'definicao',
  'observacao': 'Predicados lexicais W,T,O abreviam mulher, chá e pedir na análise publicada Não se '
                'contabiliza como prova de um resultado matemático.',
  'testemunhas': {'lean': [], 'py': [], 'wl': []},
  'pendencias': {'lean': '', 'py': '', 'wl': ''}},
 {'ids': ['c03.e0203'],
  'expressoes': {'c03.e0203': 'O(x,y)'},
  'proposicao': 'Predicados lexicais W,T,O abreviam mulher, chá e pedir na análise publicada A expressão '
                'desta ocorrência é O(x,y).',
  'hipoteses': ['W,T:E→Prop; O:E→E→Prop; ordem de argumentos preservada.'],
  'alcance': 'definicao',
  'observacao': 'Predicados lexicais W,T,O abreviam mulher, chá e pedir na análise publicada Não se '
                'contabiliza como prova de um resultado matemático.',
  'testemunhas': {'lean': [], 'py': [], 'wl': []},
  'pendencias': {'lean': '', 'py': '', 'wl': ''}},
 {'ids': ['c03.e0266'],
  'expressoes': {'c03.e0266': 'H=\\lambda z.\\,\\exists y[T(y)\\land O(z,y)]'},
  'proposicao': 'H é a abreviação da propriedade de pedir alguma entidade que satisfaz T A expressão desta '
                'ocorrência é H=\\lambda z.\\,\\exists y[T(y)\\land O(z,y)].',
  'hipoteses': ['H:E→Prop; z variável ligada; y ligado pelo existencial; O(z,y) preserva ordem dos '
                'argumentos.'],
  'alcance': 'definicao',
  'observacao': 'H é a abreviação da propriedade de pedir alguma entidade que satisfaz T Não se contabiliza '
                'como prova de um resultado matemático.',
  'testemunhas': {'lean': [], 'py': [], 'wl': []},
  'pendencias': {'lean': '', 'py': '', 'wl': ''}},
 {'ids': ['c03.e0279'],
  'expressoes': {'c03.e0279': 'E_s(x)'},
  'proposicao': 'Predicados estudante, trabalhar e vir recebem nomes distintos da notação anterior A '
                'expressão desta ocorrência é E_s(x).',
  'hipoteses': ['E_s,T_r,C:E→Prop; subscritos distinguem símbolos.'],
  'alcance': 'definicao',
  'observacao': 'Predicados estudante, trabalhar e vir recebem nomes distintos da notação anterior Não se '
                'contabiliza como prova de um resultado matemático.',
  'testemunhas': {'lean': [], 'py': [], 'wl': []},
  'pendencias': {'lean': '', 'py': '', 'wl': ''}},
 {'ids': ['c03.e0280'],
  'expressoes': {'c03.e0280': 'T_r(x)'},
  'proposicao': 'Predicados estudante, trabalhar e vir recebem nomes distintos da notação anterior A '
                'expressão desta ocorrência é T_r(x).',
  'hipoteses': ['E_s,T_r,C:E→Prop; subscritos distinguem símbolos.'],
  'alcance': 'definicao',
  'observacao': 'Predicados estudante, trabalhar e vir recebem nomes distintos da notação anterior Não se '
                'contabiliza como prova de um resultado matemático.',
  'testemunhas': {'lean': [], 'py': [], 'wl': []},
  'pendencias': {'lean': '', 'py': '', 'wl': ''}},
 {'ids': ['c03.e0281'],
  'expressoes': {'c03.e0281': 'C(x)'},
  'proposicao': 'Predicados estudante, trabalhar e vir recebem nomes distintos da notação anterior A '
                'expressão desta ocorrência é C(x).',
  'hipoteses': ['E_s,T_r,C:E→Prop; subscritos distinguem símbolos.'],
  'alcance': 'definicao',
  'observacao': 'Predicados estudante, trabalhar e vir recebem nomes distintos da notação anterior Não se '
                'contabiliza como prova de um resultado matemático.',
  'testemunhas': {'lean': [], 'py': [], 'wl': []},
  'pendencias': {'lean': '', 'py': '', 'wl': ''}},
 {'ids': ['c03.e0286'],
  'expressoes': {'c03.e0286': 'E_s(x)'},
  'proposicao': 'Condições sobre o indivíduo ao qual será aplicada a premissa universal da oração relativa A '
                'expressão desta ocorrência é E_s(x).',
  'hipoteses': ['E_s(x) e T_r(x); ∀x[(E_s(x)∧T_r(x))→C(x)].'],
  'alcance': 'hipotese',
  'observacao': 'Condições sobre o indivíduo ao qual será aplicada a premissa universal da oração relativa '
                'Não se contabiliza como prova de um resultado matemático.',
  'testemunhas': {'lean': [], 'py': [], 'wl': []},
  'pendencias': {'lean': '', 'py': '', 'wl': ''}},
 {'ids': ['c03.e0287'],
  'expressoes': {'c03.e0287': 'T_r(x)'},
  'proposicao': 'Condições sobre o indivíduo ao qual será aplicada a premissa universal da oração relativa A '
                'expressão desta ocorrência é T_r(x).',
  'hipoteses': ['E_s(x) e T_r(x); ∀x[(E_s(x)∧T_r(x))→C(x)].'],
  'alcance': 'hipotese',
  'observacao': 'Condições sobre o indivíduo ao qual será aplicada a premissa universal da oração relativa '
                'Não se contabiliza como prova de um resultado matemático.',
  'testemunhas': {'lean': [], 'py': [], 'wl': []},
  'pendencias': {'lean': '', 'py': '', 'wl': ''}},
 {'ids': ['c03.e0288'],
  'expressoes': {'c03.e0288': 'C(x)'},
  'proposicao': 'As duas propriedades da restrição e a condição universal permitem concluir C(x).',
  'hipoteses': ['E_s,T_r,C predicados sobre E; a fórmula universal é premissa, não verdade afirmada sem '
                'hipótese.',
                'Certificado de dedução natural com introdução/eliminação de quantificadores, escopo de '
                'variáveis, substituição sem captura e controle de testemunha fresca; o domínio pode ser '
                'vazio. A dupla negação e o terceiro excluído são regras da lógica clássica.'],
  'alcance': 'completa',
  'observacao': 'Cada testemunha CAS verifica uma árvore finita de prova ou o esquema completo de indução, '
                'com suas condições laterais; não é amostragem de indivíduos ou de comprimentos.',
  'testemunhas': {'lean': [{'arquivo': 'Verificar.lean',
                            'nome': 'Chapter03.c03_p02.restrictedUniversal',
                            'linha': 125,
                            'metodo': 'prova_geral'}],
                  'py': [{'arquivo': 'deducao.py',
                          'nome': 'restricted_universal',
                          'metodo': 'deducao_natural',
                          'linha': 189},
                         {'arquivo': 'deducao.py',
                          'nome': 'no_invalid_generalization',
                          'metodo': 'calculo_exato',
                          'linha': 196},
                         {'arquivo': 'deducao.py',
                          'nome': 'no_invalid_modus_ponens',
                          'metodo': 'calculo_exato',
                          'linha': 199}],
                  'wl': [{'arquivo': 'deducao.wl',
                          'nome': 'restricted_universal',
                          'metodo': 'deducao_natural',
                          'linha': 51},
                         {'arquivo': 'deducao.wl',
                          'nome': 'no_invalid_generalization',
                          'metodo': 'calculo_exato',
                          'linha': 58},
                         {'arquivo': 'deducao.wl',
                          'nome': 'no_invalid_modus_ponens',
                          'metodo': 'calculo_exato',
                          'linha': 61}]},
  'pendencias': {'lean': '', 'py': '', 'wl': ''}},
 {'ids': ['c03.e0314'],
  'expressoes': {'c03.e0314': '\\operatorname{manage}(x,P)'},
  'proposicao': 'Predicado manage recebe uma entidade e uma proposição A expressão desta ocorrência é '
                '\\operatorname{manage}(x,P).',
  'hipoteses': ['Manage:E→Prop→Prop; a regra de veridicalidade é hipótese adicional, não decorre só do '
                'tipo.'],
  'alcance': 'definicao',
  'observacao': 'Predicado manage recebe uma entidade e uma proposição Não se contabiliza como prova de um '
                'resultado matemático.',
  'testemunhas': {'lean': [], 'py': [], 'wl': []},
  'pendencias': {'lean': '', 'py': '', 'wl': ''}},
 {'ids': ['c03.e0317'],
  'expressoes': {'c03.e0317': '\\exists x[E_s(x)\\land\\operatorname{manage}(x,C(x))].'},
  'proposicao': 'Representação da frase existencial com manage usada como premissa do argumento A expressão '
                'desta ocorrência é \\exists x[E_s(x)\\land\\operatorname{manage}(x,C(x))]..',
  'hipoteses': ['∃x[E_s(x)∧manage(x,C(x))]; não é observação empírica sobre estudantes.'],
  'alcance': 'hipotese',
  'observacao': 'Representação da frase existencial com manage usada como premissa do argumento Não se '
                'contabiliza como prova de um resultado matemático.',
  'testemunhas': {'lean': [], 'py': [], 'wl': []},
  'pendencias': {'lean': '', 'py': '', 'wl': ''}},
 {'ids': ['c03.e0321'],
  'expressoes': {'c03.e0321': 'P=C(x)'},
  'proposicao': 'Substituição da proposição C(x) no parâmetro P da regra de manage A expressão desta '
                'ocorrência é P=C(x).',
  'hipoteses': ['P:Prop; x é a testemunha existencial já escolhida.'],
  'alcance': 'definicao',
  'observacao': 'Substituição da proposição C(x) no parâmetro P da regra de manage Não se contabiliza como '
                'prova de um resultado matemático.',
  'testemunhas': {'lean': [], 'py': [], 'wl': []},
  'pendencias': {'lean': '', 'py': '', 'wl': ''}},
 {'ids': ['c03.e0320'],
  'expressoes': {'c03.e0320': 'E_s(x)'},
  'proposicao': 'Propriedade E_s(x) retida da testemunha da premissa existencial A expressão desta '
                'ocorrência é E_s(x).',
  'hipoteses': ['x testemunha de E_s(x) e manage(x,C(x)).'],
  'alcance': 'hipotese',
  'observacao': 'Propriedade E_s(x) retida da testemunha da premissa existencial Não se contabiliza como '
                'prova de um resultado matemático.',
  'testemunhas': {'lean': [], 'py': [], 'wl': []},
  'pendencias': {'lean': '', 'py': '', 'wl': ''}},
 {'ids': ['c03.e0322'],
  'expressoes': {'c03.e0322': 'C(x)'},
  'proposicao': 'A regra verídica de manage, aplicada à testemunha, permite concluir C(x).',
  'hipoteses': ['Uma testemunha x satisfaz Es(x) e ManageCome(x); a regra lexical ∀x[ManageCome(x)→C(x)] é '
                'assumida explicitamente. ManageCome(x) abrevia manage(x,C(x)).',
                'A introdução e eliminação de quantificadores verifica variáveis frescas, substituição sem '
                'captura e não escape da testemunha existencial.'],
  'alcance': 'completa',
  'observacao': 'O passo C(x) segue por eliminação de ∀ e de → para a testemunha local; a existência só é '
                'inferida antes de fechar seu escopo. Não é uma propriedade inferida apenas do tipo de '
                'manage.',
  'testemunhas': {'lean': [{'arquivo': 'Verificar.lean',
                            'nome': 'Chapter03.c03_p02.manageInference',
                            'metodo': 'prova_geral',
                            'linha': 135}],
                  'py': [{'arquivo': 'deducao.py',
                          'nome': 'manage_inference',
                          'metodo': 'deducao_natural',
                          'linha': 190},
                         {'arquivo': 'deducao.py',
                          'nome': 'no_undeclared_rule',
                          'metodo': 'calculo_exato',
                          'linha': 200}],
                  'wl': [{'arquivo': 'deducao.wl',
                          'nome': 'manage_inference',
                          'metodo': 'deducao_natural',
                          'linha': 52},
                         {'arquivo': 'deducao.wl',
                          'nome': 'no_undeclared_rule',
                          'metodo': 'calculo_exato',
                          'linha': 62}]},
  'pendencias': {'lean': '', 'py': '', 'wl': ''}},
 {'ids': ['c03.e0327'],
  'expressoes': {'c03.e0327': '\\begin{tabular}{cccc} \\toprule Classe & Genitivo singular & Acusativo '
                              'plural & Genitivo plural\\\\ \\midrule 1 & -u & -us & -on\\\\ 2 & '
                              '\\(-\\varnothing\\) & -es & -on\\\\ 3 & -s & -es & -on\\\\ 4 & -s & -is & '
                              '-on\\\\ 5 & -u & -a & -on\\\\ 6 & -u & -a & -on\\\\ 7 & -us & -i & -on\\\\ 8 '
                              '& -os & -a & -on\\\\ \\bottomrule \\end{tabular}'},
  'proposicao': 'Tabela de terminações é dado linguístico de entrada, não consequência matemática A '
                'expressão desta ocorrência é \\begin{tabular}{cccc} \\toprule Classe & Genitivo singular & '
                'Acusativo plural & Genitivo plural\\\\ \\midrule 1 & -u & -us & -on\\\\ 2 & '
                '\\(-\\varnothing\\) & -es & -on\\\\ 3 & -s & -es & -on\\\\ 4 & -s & -is & -on\\\\ 5 & -u & '
                '-a & -on\\\\ 6 & -u & -a & -on\\\\ 7 & -us & -i & -on\\\\ 8 & -os & -a & -on\\\\ '
                '\\bottomrule \\end{tabular}.',
  'hipoteses': ['Oito classes e três posições de caso/número da análise publicada; as operações posteriores '
                'usam essas colunas.'],
  'alcance': 'hipotese',
  'observacao': 'Tabela de terminações é dado linguístico de entrada, não consequência matemática Não se '
                'contabiliza como prova de um resultado matemático.',
  'testemunhas': {'lean': [], 'py': [], 'wl': []},
  'pendencias': {'lean': '', 'py': '', 'wl': ''}},
 {'ids': ['c03.e0329'],
  'expressoes': {'c03.e0329': '\\begin{figure}[H] \\centering \\avm{[ classe & 7 \\\\ caso & genitivo \\\\ '
                              'número & singular \\\\ terminação & -us ]} \\caption{Uma célula do paradigma '
                              'grego. Fonte: elaboração própria baseada em \\textcite[p.~434, tabela~1, '
                              'classe~7]{ackermanMalouf2013}, que retomam Ralli (1994, 2002).} '
                              '\\end{figure}'},
  'proposicao': 'O registro de traços identifica a célula de genitivo singular da classe 7, distinguindo-a '
                'de outra célula com a mesma terminação.',
  'hipoteses': ['Dados das colunas do paradigma; índices de Lean Fin 8 convertidos para classes 1..8.'],
  'alcance': 'completa',
  'observacao': '',
  'testemunhas': {'lean': [{'arquivo': 'Expressoes.lean',
                            'nome': 'Chapter03Expressions.feature_record',
                            'linha': 73,
                            'metodo': 'prova_geral'}],
                  'py': [{'arquivo': 'expressoes.py',
                          'nome': 'feature_record',
                          'linha': 36,
                          'metodo': 'calculo_exato'}],
                  'wl': [{'arquivo': 'revisaointegral.wl',
                          'nome': 'feature_record',
                          'linha': 12,
                          'metodo': 'calculo_exato'}]},
  'pendencias': {'lean': '', 'py': '', 'wl': ''}},
 {'ids': ['c03.e0004'],
  'expressoes': {'c03.e0004': 'A'},
  'proposicao': 'Nomes dos conjuntos de classes gregas e símbolos de interseção e união; não são novas '
                'contagens A expressão desta ocorrência é A.',
  'hipoteses': ['As convenções e o domínio são os explicitados na prosa adjacente.'],
  'alcance': 'notacao',
  'observacao': 'Nomes dos conjuntos de classes gregas e símbolos de interseção e união; não são novas '
                'contagens Não se contabiliza como prova de um resultado matemático.',
  'testemunhas': {'lean': [], 'py': [], 'wl': []},
  'pendencias': {'lean': '', 'py': '', 'wl': ''}},
 {'ids': ['c03.e0005'],
  'expressoes': {'c03.e0005': 'B'},
  'proposicao': 'Nomes dos conjuntos de classes gregas e símbolos de interseção e união; não são novas '
                'contagens A expressão desta ocorrência é B.',
  'hipoteses': ['As convenções e o domínio são os explicitados na prosa adjacente.'],
  'alcance': 'notacao',
  'observacao': 'Nomes dos conjuntos de classes gregas e símbolos de interseção e união; não são novas '
                'contagens Não se contabiliza como prova de um resultado matemático.',
  'testemunhas': {'lean': [], 'py': [], 'wl': []},
  'pendencias': {'lean': '', 'py': '', 'wl': ''}},
 {'ids': ['c03.e0008'],
  'expressoes': {'c03.e0008': 'A'},
  'proposicao': 'Nomes dos conjuntos de classes gregas e símbolos de interseção e união; não são novas '
                'contagens A expressão desta ocorrência é A.',
  'hipoteses': ['As convenções e o domínio são os explicitados na prosa adjacente.'],
  'alcance': 'notacao',
  'observacao': 'Nomes dos conjuntos de classes gregas e símbolos de interseção e união; não são novas '
                'contagens Não se contabiliza como prova de um resultado matemático.',
  'testemunhas': {'lean': [], 'py': [], 'wl': []},
  'pendencias': {'lean': '', 'py': '', 'wl': ''}},
 {'ids': ['c03.e0010'],
  'expressoes': {'c03.e0010': '\\cap'},
  'proposicao': 'Nomes dos conjuntos de classes gregas e símbolos de interseção e união; não são novas '
                'contagens A expressão desta ocorrência é \\cap.',
  'hipoteses': ['As convenções e o domínio são os explicitados na prosa adjacente.'],
  'alcance': 'notacao',
  'observacao': 'Nomes dos conjuntos de classes gregas e símbolos de interseção e união; não são novas '
                'contagens Não se contabiliza como prova de um resultado matemático.',
  'testemunhas': {'lean': [], 'py': [], 'wl': []},
  'pendencias': {'lean': '', 'py': '', 'wl': ''}},
 {'ids': ['c03.e0011'],
  'expressoes': {'c03.e0011': '\\cup'},
  'proposicao': 'Nomes dos conjuntos de classes gregas e símbolos de interseção e união; não são novas '
                'contagens A expressão desta ocorrência é \\cup.',
  'hipoteses': ['As convenções e o domínio são os explicitados na prosa adjacente.'],
  'alcance': 'notacao',
  'observacao': 'Nomes dos conjuntos de classes gregas e símbolos de interseção e união; não são novas '
                'contagens Não se contabiliza como prova de um resultado matemático.',
  'testemunhas': {'lean': [], 'py': [], 'wl': []},
  'pendencias': {'lean': '', 'py': '', 'wl': ''}},
 {'ids': ['c03.e0019'],
  'expressoes': {'c03.e0019': 'A'},
  'proposicao': 'Nomes dos conjuntos de classes gregas e símbolos de interseção e união; não são novas '
                'contagens A expressão desta ocorrência é A.',
  'hipoteses': ['As convenções e o domínio são os explicitados na prosa adjacente.'],
  'alcance': 'notacao',
  'observacao': 'Nomes dos conjuntos de classes gregas e símbolos de interseção e união; não são novas '
                'contagens Não se contabiliza como prova de um resultado matemático.',
  'testemunhas': {'lean': [], 'py': [], 'wl': []},
  'pendencias': {'lean': '', 'py': '', 'wl': ''}},
 {'ids': ['c03.e0020'],
  'expressoes': {'c03.e0020': 'A'},
  'proposicao': 'Nomes dos conjuntos de classes gregas e símbolos de interseção e união; não são novas '
                'contagens A expressão desta ocorrência é A.',
  'hipoteses': ['As convenções e o domínio são os explicitados na prosa adjacente.'],
  'alcance': 'notacao',
  'observacao': 'Nomes dos conjuntos de classes gregas e símbolos de interseção e união; não são novas '
                'contagens Não se contabiliza como prova de um resultado matemático.',
  'testemunhas': {'lean': [], 'py': [], 'wl': []},
  'pendencias': {'lean': '', 'py': '', 'wl': ''}},
 {'ids': ['c03.e0013'],
  'expressoes': {'c03.e0013': '|A|'},
  'proposicao': 'As barras denotam cardinalidade de um conjunto finito A expressão desta ocorrência é |A|.',
  'hipoteses': ['A finito; conta cada identificador uma vez.'],
  'alcance': 'definicao',
  'observacao': 'As barras denotam cardinalidade de um conjunto finito Não se contabiliza como prova de um '
                'resultado matemático.',
  'testemunhas': {'lean': [], 'py': [], 'wl': []},
  'pendencias': {'lean': '', 'py': '', 'wl': ''}},
 {'ids': ['c03.e0021'],
  'expressoes': {'c03.e0021': 'S'},
  'proposicao': 'Notação de conjuntos, indivíduo, inclusão, implicação e vazio no argumento de relações '
                'lexicais A expressão desta ocorrência é S.',
  'hipoteses': ['As convenções e o domínio são os explicitados na prosa adjacente.'],
  'alcance': 'notacao',
  'observacao': 'Notação de conjuntos, indivíduo, inclusão, implicação e vazio no argumento de relações '
                'lexicais Não se contabiliza como prova de um resultado matemático.',
  'testemunhas': {'lean': [], 'py': [], 'wl': []},
  'pendencias': {'lean': '', 'py': '', 'wl': ''}},
 {'ids': ['c03.e0022'],
  'expressoes': {'c03.e0022': 'L'},
  'proposicao': 'Notação de conjuntos, indivíduo, inclusão, implicação e vazio no argumento de relações '
                'lexicais A expressão desta ocorrência é L.',
  'hipoteses': ['As convenções e o domínio são os explicitados na prosa adjacente.'],
  'alcance': 'notacao',
  'observacao': 'Notação de conjuntos, indivíduo, inclusão, implicação e vazio no argumento de relações '
                'lexicais Não se contabiliza como prova de um resultado matemático.',
  'testemunhas': {'lean': [], 'py': [], 'wl': []},
  'pendencias': {'lean': '', 'py': '', 'wl': ''}},
 {'ids': ['c03.e0024'],
  'expressoes': {'c03.e0024': '\\subseteq'},
  'proposicao': 'Notação de conjuntos, indivíduo, inclusão, implicação e vazio no argumento de relações '
                'lexicais A expressão desta ocorrência é \\subseteq.',
  'hipoteses': ['As convenções e o domínio são os explicitados na prosa adjacente.'],
  'alcance': 'notacao',
  'observacao': 'Notação de conjuntos, indivíduo, inclusão, implicação e vazio no argumento de relações '
                'lexicais Não se contabiliza como prova de um resultado matemático.',
  'testemunhas': {'lean': [], 'py': [], 'wl': []},
  'pendencias': {'lean': '', 'py': '', 'wl': ''}},
 {'ids': ['c03.e0026'],
  'expressoes': {'c03.e0026': 'x'},
  'proposicao': 'Notação de conjuntos, indivíduo, inclusão, implicação e vazio no argumento de relações '
                'lexicais A expressão desta ocorrência é x.',
  'hipoteses': ['As convenções e o domínio são os explicitados na prosa adjacente.'],
  'alcance': 'notacao',
  'observacao': 'Notação de conjuntos, indivíduo, inclusão, implicação e vazio no argumento de relações '
                'lexicais Não se contabiliza como prova de um resultado matemático.',
  'testemunhas': {'lean': [], 'py': [], 'wl': []},
  'pendencias': {'lean': '', 'py': '', 'wl': ''}},
 {'ids': ['c03.e0028'],
  'expressoes': {'c03.e0028': 'L'},
  'proposicao': 'Notação de conjuntos, indivíduo, inclusão, implicação e vazio no argumento de relações '
                'lexicais A expressão desta ocorrência é L.',
  'hipoteses': ['As convenções e o domínio são os explicitados na prosa adjacente.'],
  'alcance': 'notacao',
  'observacao': 'Notação de conjuntos, indivíduo, inclusão, implicação e vazio no argumento de relações '
                'lexicais Não se contabiliza como prova de um resultado matemático.',
  'testemunhas': {'lean': [], 'py': [], 'wl': []},
  'pendencias': {'lean': '', 'py': '', 'wl': ''}},
 {'ids': ['c03.e0029'],
  'expressoes': {'c03.e0029': 'S'},
  'proposicao': 'Notação de conjuntos, indivíduo, inclusão, implicação e vazio no argumento de relações '
                'lexicais A expressão desta ocorrência é S.',
  'hipoteses': ['As convenções e o domínio são os explicitados na prosa adjacente.'],
  'alcance': 'notacao',
  'observacao': 'Notação de conjuntos, indivíduo, inclusão, implicação e vazio no argumento de relações '
                'lexicais Não se contabiliza como prova de um resultado matemático.',
  'testemunhas': {'lean': [], 'py': [], 'wl': []},
  'pendencias': {'lean': '', 'py': '', 'wl': ''}},
 {'ids': ['c03.e0031'],
  'expressoes': {'c03.e0031': '\\varnothing'},
  'proposicao': 'Notação de conjuntos, indivíduo, inclusão, implicação e vazio no argumento de relações '
                'lexicais A expressão desta ocorrência é \\varnothing.',
  'hipoteses': ['As convenções e o domínio são os explicitados na prosa adjacente.'],
  'alcance': 'notacao',
  'observacao': 'Notação de conjuntos, indivíduo, inclusão, implicação e vazio no argumento de relações '
                'lexicais Não se contabiliza como prova de um resultado matemático.',
  'testemunhas': {'lean': [], 'py': [], 'wl': []},
  'pendencias': {'lean': '', 'py': '', 'wl': ''}},
 {'ids': ['c03.e0032'],
  'expressoes': {'c03.e0032': '\\Longrightarrow'},
  'proposicao': 'Notação de conjuntos, indivíduo, inclusão, implicação e vazio no argumento de relações '
                'lexicais A expressão desta ocorrência é \\Longrightarrow.',
  'hipoteses': ['As convenções e o domínio são os explicitados na prosa adjacente.'],
  'alcance': 'notacao',
  'observacao': 'Notação de conjuntos, indivíduo, inclusão, implicação e vazio no argumento de relações '
                'lexicais Não se contabiliza como prova de um resultado matemático.',
  'testemunhas': {'lean': [], 'py': [], 'wl': []},
  'pendencias': {'lean': '', 'py': '', 'wl': ''}},
 {'ids': ['c03.e0034'],
  'expressoes': {'c03.e0034': '\\varnothing'},
  'proposicao': 'Notação de conjuntos, indivíduo, inclusão, implicação e vazio no argumento de relações '
                'lexicais A expressão desta ocorrência é \\varnothing.',
  'hipoteses': ['As convenções e o domínio são os explicitados na prosa adjacente.'],
  'alcance': 'notacao',
  'observacao': 'Notação de conjuntos, indivíduo, inclusão, implicação e vazio no argumento de relações '
                'lexicais Não se contabiliza como prova de um resultado matemático.',
  'testemunhas': {'lean': [], 'py': [], 'wl': []},
  'pendencias': {'lean': '', 'py': '', 'wl': ''}},
 {'ids': ['c03.e0035'],
  'expressoes': {'c03.e0035': 'U'},
  'proposicao': 'Notação de conjuntos, indivíduo, inclusão, implicação e vazio no argumento de relações '
                'lexicais A expressão desta ocorrência é U.',
  'hipoteses': ['As convenções e o domínio são os explicitados na prosa adjacente.'],
  'alcance': 'notacao',
  'observacao': 'Notação de conjuntos, indivíduo, inclusão, implicação e vazio no argumento de relações '
                'lexicais Não se contabiliza como prova de um resultado matemático.',
  'testemunhas': {'lean': [], 'py': [], 'wl': []},
  'pendencias': {'lean': '', 'py': '', 'wl': ''}},
 {'ids': ['c03.e0038'],
  'expressoes': {'c03.e0038': 'L'},
  'proposicao': 'Notação de conjuntos, indivíduo, inclusão, implicação e vazio no argumento de relações '
                'lexicais A expressão desta ocorrência é L.',
  'hipoteses': ['As convenções e o domínio são os explicitados na prosa adjacente.'],
  'alcance': 'notacao',
  'observacao': 'Notação de conjuntos, indivíduo, inclusão, implicação e vazio no argumento de relações '
                'lexicais Não se contabiliza como prova de um resultado matemático.',
  'testemunhas': {'lean': [], 'py': [], 'wl': []},
  'pendencias': {'lean': '', 'py': '', 'wl': ''}},
 {'ids': ['c03.e0039'],
  'expressoes': {'c03.e0039': 'U'},
  'proposicao': 'Notação de conjuntos, indivíduo, inclusão, implicação e vazio no argumento de relações '
                'lexicais A expressão desta ocorrência é U.',
  'hipoteses': ['As convenções e o domínio são os explicitados na prosa adjacente.'],
  'alcance': 'notacao',
  'observacao': 'Notação de conjuntos, indivíduo, inclusão, implicação e vazio no argumento de relações '
                'lexicais Não se contabiliza como prova de um resultado matemático.',
  'testemunhas': {'lean': [], 'py': [], 'wl': []},
  'pendencias': {'lean': '', 'py': '', 'wl': ''}},
 {'ids': ['c03.e0041'],
  'expressoes': {'c03.e0041': 'L'},
  'proposicao': 'Notação de conjuntos, indivíduo, inclusão, implicação e vazio no argumento de relações '
                'lexicais A expressão desta ocorrência é L.',
  'hipoteses': ['As convenções e o domínio são os explicitados na prosa adjacente.'],
  'alcance': 'notacao',
  'observacao': 'Notação de conjuntos, indivíduo, inclusão, implicação e vazio no argumento de relações '
                'lexicais Não se contabiliza como prova de um resultado matemático.',
  'testemunhas': {'lean': [], 'py': [], 'wl': []},
  'pendencias': {'lean': '', 'py': '', 'wl': ''}},
 {'ids': ['c03.e0042'],
  'expressoes': {'c03.e0042': 'U'},
  'proposicao': 'Notação de conjuntos, indivíduo, inclusão, implicação e vazio no argumento de relações '
                'lexicais A expressão desta ocorrência é U.',
  'hipoteses': ['As convenções e o domínio são os explicitados na prosa adjacente.'],
  'alcance': 'notacao',
  'observacao': 'Notação de conjuntos, indivíduo, inclusão, implicação e vazio no argumento de relações '
                'lexicais Não se contabiliza como prova de um resultado matemático.',
  'testemunhas': {'lean': [], 'py': [], 'wl': []},
  'pendencias': {'lean': '', 'py': '', 'wl': ''}},
 {'ids': ['c03.e0043'],
  'expressoes': {'c03.e0043': 'L'},
  'proposicao': 'Notação de conjuntos, indivíduo, inclusão, implicação e vazio no argumento de relações '
                'lexicais A expressão desta ocorrência é L.',
  'hipoteses': ['As convenções e o domínio são os explicitados na prosa adjacente.'],
  'alcance': 'notacao',
  'observacao': 'Notação de conjuntos, indivíduo, inclusão, implicação e vazio no argumento de relações '
                'lexicais Não se contabiliza como prova de um resultado matemático.',
  'testemunhas': {'lean': [], 'py': [], 'wl': []},
  'pendencias': {'lean': '', 'py': '', 'wl': ''}},
 {'ids': ['c03.e0044'],
  'expressoes': {'c03.e0044': 'A'},
  'proposicao': 'Nomes dos conjuntos de segmentos italianos, do coeficiente e da operação mínimo; não '
                'afirmam resultado independente das contas A expressão desta ocorrência é A.',
  'hipoteses': ['As convenções e o domínio são os explicitados na prosa adjacente.'],
  'alcance': 'notacao',
  'observacao': 'Nomes dos conjuntos de segmentos italianos, do coeficiente e da operação mínimo; não '
                'afirmam resultado independente das contas Não se contabiliza como prova de um resultado '
                'matemático.',
  'testemunhas': {'lean': [], 'py': [], 'wl': []},
  'pendencias': {'lean': '', 'py': '', 'wl': ''}},
 {'ids': ['c03.e0045'],
  'expressoes': {'c03.e0045': 'B'},
  'proposicao': 'Nomes dos conjuntos de segmentos italianos, do coeficiente e da operação mínimo; não '
                'afirmam resultado independente das contas A expressão desta ocorrência é B.',
  'hipoteses': ['As convenções e o domínio são os explicitados na prosa adjacente.'],
  'alcance': 'notacao',
  'observacao': 'Nomes dos conjuntos de segmentos italianos, do coeficiente e da operação mínimo; não '
                'afirmam resultado independente das contas Não se contabiliza como prova de um resultado '
                'matemático.',
  'testemunhas': {'lean': [], 'py': [], 'wl': []},
  'pendencias': {'lean': '', 'py': '', 'wl': ''}},
 {'ids': ['c03.e0047'],
  'expressoes': {'c03.e0047': 'A'},
  'proposicao': 'Nomes dos conjuntos de segmentos italianos, do coeficiente e da operação mínimo; não '
                'afirmam resultado independente das contas A expressão desta ocorrência é A.',
  'hipoteses': ['As convenções e o domínio são os explicitados na prosa adjacente.'],
  'alcance': 'notacao',
  'observacao': 'Nomes dos conjuntos de segmentos italianos, do coeficiente e da operação mínimo; não '
                'afirmam resultado independente das contas Não se contabiliza como prova de um resultado '
                'matemático.',
  'testemunhas': {'lean': [], 'py': [], 'wl': []},
  'pendencias': {'lean': '', 'py': '', 'wl': ''}},
 {'ids': ['c03.e0048'],
  'expressoes': {'c03.e0048': 'B'},
  'proposicao': 'Nomes dos conjuntos de segmentos italianos, do coeficiente e da operação mínimo; não '
                'afirmam resultado independente das contas A expressão desta ocorrência é B.',
  'hipoteses': ['As convenções e o domínio são os explicitados na prosa adjacente.'],
  'alcance': 'notacao',
  'observacao': 'Nomes dos conjuntos de segmentos italianos, do coeficiente e da operação mínimo; não '
                'afirmam resultado independente das contas Não se contabiliza como prova de um resultado '
                'matemático.',
  'testemunhas': {'lean': [], 'py': [], 'wl': []},
  'pendencias': {'lean': '', 'py': '', 'wl': ''}},
 {'ids': ['c03.e0053'],
  'expressoes': {'c03.e0053': '\\operatorname{overlap}'},
  'proposicao': 'Nomes dos conjuntos de segmentos italianos, do coeficiente e da operação mínimo; não '
                'afirmam resultado independente das contas A expressão desta ocorrência é '
                '\\operatorname{overlap}.',
  'hipoteses': ['As convenções e o domínio são os explicitados na prosa adjacente.'],
  'alcance': 'notacao',
  'observacao': 'Nomes dos conjuntos de segmentos italianos, do coeficiente e da operação mínimo; não '
                'afirmam resultado independente das contas Não se contabiliza como prova de um resultado '
                'matemático.',
  'testemunhas': {'lean': [], 'py': [], 'wl': []},
  'pendencias': {'lean': '', 'py': '', 'wl': ''}},
 {'ids': ['c03.e0054'],
  'expressoes': {'c03.e0054': '\\min'},
  'proposicao': 'Nomes dos conjuntos de segmentos italianos, do coeficiente e da operação mínimo; não '
                'afirmam resultado independente das contas A expressão desta ocorrência é \\min.',
  'hipoteses': ['As convenções e o domínio são os explicitados na prosa adjacente.'],
  'alcance': 'notacao',
  'observacao': 'Nomes dos conjuntos de segmentos italianos, do coeficiente e da operação mínimo; não '
                'afirmam resultado independente das contas Não se contabiliza como prova de um resultado '
                'matemático.',
  'testemunhas': {'lean': [], 'py': [], 'wl': []},
  'pendencias': {'lean': '', 'py': '', 'wl': ''}},
 {'ids': ['c03.e0058'],
  'expressoes': {'c03.e0058': 'C'},
  'proposicao': 'Nomes dos conjuntos de segmentos italianos, do coeficiente e da operação mínimo; não '
                'afirmam resultado independente das contas A expressão desta ocorrência é C.',
  'hipoteses': ['As convenções e o domínio são os explicitados na prosa adjacente.'],
  'alcance': 'notacao',
  'observacao': 'Nomes dos conjuntos de segmentos italianos, do coeficiente e da operação mínimo; não '
                'afirmam resultado independente das contas Não se contabiliza como prova de um resultado '
                'matemático.',
  'testemunhas': {'lean': [], 'py': [], 'wl': []},
  'pendencias': {'lean': '', 'py': '', 'wl': ''}},
 {'ids': ['c03.e0059'],
  'expressoes': {'c03.e0059': 'A'},
  'proposicao': 'Nomes dos conjuntos de segmentos italianos, do coeficiente e da operação mínimo; não '
                'afirmam resultado independente das contas A expressão desta ocorrência é A.',
  'hipoteses': ['As convenções e o domínio são os explicitados na prosa adjacente.'],
  'alcance': 'notacao',
  'observacao': 'Nomes dos conjuntos de segmentos italianos, do coeficiente e da operação mínimo; não '
                'afirmam resultado independente das contas Não se contabiliza como prova de um resultado '
                'matemático.',
  'testemunhas': {'lean': [], 'py': [], 'wl': []},
  'pendencias': {'lean': '', 'py': '', 'wl': ''}},
 {'ids': ['c03.e0062'],
  'expressoes': {'c03.e0062': 'D_s'},
  'proposicao': 'Nomes dos conjuntos de segmentos italianos, do coeficiente e da operação mínimo; não '
                'afirmam resultado independente das contas A expressão desta ocorrência é D_s.',
  'hipoteses': ['As convenções e o domínio são os explicitados na prosa adjacente.'],
  'alcance': 'notacao',
  'observacao': 'Nomes dos conjuntos de segmentos italianos, do coeficiente e da operação mínimo; não '
                'afirmam resultado independente das contas Não se contabiliza como prova de um resultado '
                'matemático.',
  'testemunhas': {'lean': [], 'py': [], 'wl': []},
  'pendencias': {'lean': '', 'py': '', 'wl': ''}},
 {'ids': ['c03.e0063'],
  'expressoes': {'c03.e0063': 'A'},
  'proposicao': 'Nomes dos conjuntos de segmentos italianos, do coeficiente e da operação mínimo; não '
                'afirmam resultado independente das contas A expressão desta ocorrência é A.',
  'hipoteses': ['As convenções e o domínio são os explicitados na prosa adjacente.'],
  'alcance': 'notacao',
  'observacao': 'Nomes dos conjuntos de segmentos italianos, do coeficiente e da operação mínimo; não '
                'afirmam resultado independente das contas Não se contabiliza como prova de um resultado '
                'matemático.',
  'testemunhas': {'lean': [], 'py': [], 'wl': []},
  'pendencias': {'lean': '', 'py': '', 'wl': ''}},
 {'ids': ['c03.e0064'],
  'expressoes': {'c03.e0064': 'D_s'},
  'proposicao': 'Nomes dos conjuntos de segmentos italianos, do coeficiente e da operação mínimo; não '
                'afirmam resultado independente das contas A expressão desta ocorrência é D_s.',
  'hipoteses': ['As convenções e o domínio são os explicitados na prosa adjacente.'],
  'alcance': 'notacao',
  'observacao': 'Nomes dos conjuntos de segmentos italianos, do coeficiente e da operação mínimo; não '
                'afirmam resultado independente das contas Não se contabiliza como prova de um resultado '
                'matemático.',
  'testemunhas': {'lean': [], 'py': [], 'wl': []},
  'pendencias': {'lean': '', 'py': '', 'wl': ''}},
 {'ids': ['c03.e0069'],
  'expressoes': {'c03.e0069': 'R'},
  'proposicao': 'R nomeia relação de terminações; g é função por classe; D é seu domínio declarado A '
                'expressão desta ocorrência é R.',
  'hipoteses': ['As convenções e o domínio são os explicitados na prosa adjacente.'],
  'alcance': 'notacao',
  'observacao': 'R nomeia relação de terminações; g é função por classe; D é seu domínio declarado Não se '
                'contabiliza como prova de um resultado matemático.',
  'testemunhas': {'lean': [], 'py': [], 'wl': []},
  'pendencias': {'lean': '', 'py': '', 'wl': ''}},
 {'ids': ['c03.e0072'],
  'expressoes': {'c03.e0072': 'R'},
  'proposicao': 'R nomeia relação de terminações; g é função por classe; D é seu domínio declarado A '
                'expressão desta ocorrência é R.',
  'hipoteses': ['As convenções e o domínio são os explicitados na prosa adjacente.'],
  'alcance': 'notacao',
  'observacao': 'R nomeia relação de terminações; g é função por classe; D é seu domínio declarado Não se '
                'contabiliza como prova de um resultado matemático.',
  'testemunhas': {'lean': [], 'py': [], 'wl': []},
  'pendencias': {'lean': '', 'py': '', 'wl': ''}},
 {'ids': ['c03.e0073'],
  'expressoes': {'c03.e0073': 'g'},
  'proposicao': 'R nomeia relação de terminações; g é função por classe; D é seu domínio declarado A '
                'expressão desta ocorrência é g.',
  'hipoteses': ['As convenções e o domínio são os explicitados na prosa adjacente.'],
  'alcance': 'notacao',
  'observacao': 'R nomeia relação de terminações; g é função por classe; D é seu domínio declarado Não se '
                'contabiliza como prova de um resultado matemático.',
  'testemunhas': {'lean': [], 'py': [], 'wl': []},
  'pendencias': {'lean': '', 'py': '', 'wl': ''}},
 {'ids': ['c03.e0074'],
  'expressoes': {'c03.e0074': 'D'},
  'proposicao': 'R nomeia relação de terminações; g é função por classe; D é seu domínio declarado A '
                'expressão desta ocorrência é D.',
  'hipoteses': ['As convenções e o domínio são os explicitados na prosa adjacente.'],
  'alcance': 'notacao',
  'observacao': 'R nomeia relação de terminações; g é função por classe; D é seu domínio declarado Não se '
                'contabiliza como prova de um resultado matemático.',
  'testemunhas': {'lean': [], 'py': [], 'wl': []},
  'pendencias': {'lean': '', 'py': '', 'wl': ''}},
 {'ids': ['c03.e0078'],
  'expressoes': {'c03.e0078': 'a'},
  'proposicao': 'Notação da função de acusativo e da equivalência entre classes; -a é terminação, enquanto a '
                'é nome de função A expressão desta ocorrência é a.',
  'hipoteses': ['As convenções e o domínio são os explicitados na prosa adjacente.'],
  'alcance': 'notacao',
  'observacao': 'Notação da função de acusativo e da equivalência entre classes; -a é terminação, enquanto a '
                'é nome de função Não se contabiliza como prova de um resultado matemático.',
  'testemunhas': {'lean': [], 'py': [], 'wl': []},
  'pendencias': {'lean': '', 'py': '', 'wl': ''}},
 {'ids': ['c03.e0080'],
  'expressoes': {'c03.e0080': 'a'},
  'proposicao': 'Notação da função de acusativo e da equivalência entre classes; -a é terminação, enquanto a '
                'é nome de função A expressão desta ocorrência é a.',
  'hipoteses': ['As convenções e o domínio são os explicitados na prosa adjacente.'],
  'alcance': 'notacao',
  'observacao': 'Notação da função de acusativo e da equivalência entre classes; -a é terminação, enquanto a '
                'é nome de função Não se contabiliza como prova de um resultado matemático.',
  'testemunhas': {'lean': [], 'py': [], 'wl': []},
  'pendencias': {'lean': '', 'py': '', 'wl': ''}},
 {'ids': ['c03.e0081'],
  'expressoes': {'c03.e0081': '\\textit{-a}'},
  'proposicao': 'Notação da função de acusativo e da equivalência entre classes; -a é terminação, enquanto a '
                'é nome de função A expressão desta ocorrência é \\textit{-a}.',
  'hipoteses': ['As convenções e o domínio são os explicitados na prosa adjacente.'],
  'alcance': 'notacao',
  'observacao': 'Notação da função de acusativo e da equivalência entre classes; -a é terminação, enquanto a '
                'é nome de função Não se contabiliza como prova de um resultado matemático.',
  'testemunhas': {'lean': [], 'py': [], 'wl': []},
  'pendencias': {'lean': '', 'py': '', 'wl': ''}},
 {'ids': ['c03.e0082'],
  'expressoes': {'c03.e0082': 'd'},
  'proposicao': 'Notação da função de acusativo e da equivalência entre classes; -a é terminação, enquanto a '
                'é nome de função A expressão desta ocorrência é d.',
  'hipoteses': ['As convenções e o domínio são os explicitados na prosa adjacente.'],
  'alcance': 'notacao',
  'observacao': 'Notação da função de acusativo e da equivalência entre classes; -a é terminação, enquanto a '
                'é nome de função Não se contabiliza como prova de um resultado matemático.',
  'testemunhas': {'lean': [], 'py': [], 'wl': []},
  'pendencias': {'lean': '', 'py': '', 'wl': ''}},
 {'ids': ['c03.e0083'],
  'expressoes': {'c03.e0083': 'e'},
  'proposicao': 'Notação da função de acusativo e da equivalência entre classes; -a é terminação, enquanto a '
                'é nome de função A expressão desta ocorrência é e.',
  'hipoteses': ['As convenções e o domínio são os explicitados na prosa adjacente.'],
  'alcance': 'notacao',
  'observacao': 'Notação da função de acusativo e da equivalência entre classes; -a é terminação, enquanto a '
                'é nome de função Não se contabiliza como prova de um resultado matemático.',
  'testemunhas': {'lean': [], 'py': [], 'wl': []},
  'pendencias': {'lean': '', 'py': '', 'wl': ''}},
 {'ids': ['c03.e0086'],
  'expressoes': {'c03.e0086': '\\sim'},
  'proposicao': 'Notação da função de acusativo e da equivalência entre classes; -a é terminação, enquanto a '
                'é nome de função A expressão desta ocorrência é \\sim.',
  'hipoteses': ['As convenções e o domínio são os explicitados na prosa adjacente.'],
  'alcance': 'notacao',
  'observacao': 'Notação da função de acusativo e da equivalência entre classes; -a é terminação, enquanto a '
                'é nome de função Não se contabiliza como prova de um resultado matemático.',
  'testemunhas': {'lean': [], 'py': [], 'wl': []},
  'pendencias': {'lean': '', 'py': '', 'wl': ''}},
 {'ids': ['c03.e0087'],
  'expressoes': {'c03.e0087': 'd'},
  'proposicao': 'Notação da função de acusativo e da equivalência entre classes; -a é terminação, enquanto a '
                'é nome de função A expressão desta ocorrência é d.',
  'hipoteses': ['As convenções e o domínio são os explicitados na prosa adjacente.'],
  'alcance': 'notacao',
  'observacao': 'Notação da função de acusativo e da equivalência entre classes; -a é terminação, enquanto a '
                'é nome de função Não se contabiliza como prova de um resultado matemático.',
  'testemunhas': {'lean': [], 'py': [], 'wl': []},
  'pendencias': {'lean': '', 'py': '', 'wl': ''}},
 {'ids': ['c03.e0088'],
  'expressoes': {'c03.e0088': 'e'},
  'proposicao': 'Notação da função de acusativo e da equivalência entre classes; -a é terminação, enquanto a '
                'é nome de função A expressão desta ocorrência é e.',
  'hipoteses': ['As convenções e o domínio são os explicitados na prosa adjacente.'],
  'alcance': 'notacao',
  'observacao': 'Notação da função de acusativo e da equivalência entre classes; -a é terminação, enquanto a '
                'é nome de função Não se contabiliza como prova de um resultado matemático.',
  'testemunhas': {'lean': [], 'py': [], 'wl': []},
  'pendencias': {'lean': '', 'py': '', 'wl': ''}},
 {'ids': ['c03.e0095'],
  'expressoes': {'c03.e0095': 'f'},
  'proposicao': 'Notação da função de acusativo e da equivalência entre classes; -a é terminação, enquanto a '
                'é nome de função A expressão desta ocorrência é f.',
  'hipoteses': ['As convenções e o domínio são os explicitados na prosa adjacente.'],
  'alcance': 'notacao',
  'observacao': 'Notação da função de acusativo e da equivalência entre classes; -a é terminação, enquanto a '
                'é nome de função Não se contabiliza como prova de um resultado matemático.',
  'testemunhas': {'lean': [], 'py': [], 'wl': []},
  'pendencias': {'lean': '', 'py': '', 'wl': ''}},
 {'ids': ['c03.e0098'],
  'expressoes': {'c03.e0098': 'p'},
  'proposicao': 'p e q identificam as proposições ou as colunas de valoração da tabela de café e chá A '
                'expressão desta ocorrência é p.',
  'hipoteses': ['As convenções e o domínio são os explicitados na prosa adjacente.'],
  'alcance': 'notacao',
  'observacao': 'p e q identificam as proposições ou as colunas de valoração da tabela de café e chá Não se '
                'contabiliza como prova de um resultado matemático.',
  'testemunhas': {'lean': [], 'py': [], 'wl': []},
  'pendencias': {'lean': '', 'py': '', 'wl': ''}},
 {'ids': ['c03.e0099'],
  'expressoes': {'c03.e0099': 'q'},
  'proposicao': 'p e q identificam as proposições ou as colunas de valoração da tabela de café e chá A '
                'expressão desta ocorrência é q.',
  'hipoteses': ['As convenções e o domínio são os explicitados na prosa adjacente.'],
  'alcance': 'notacao',
  'observacao': 'p e q identificam as proposições ou as colunas de valoração da tabela de café e chá Não se '
                'contabiliza como prova de um resultado matemático.',
  'testemunhas': {'lean': [], 'py': [], 'wl': []},
  'pendencias': {'lean': '', 'py': '', 'wl': ''}},
 {'ids': ['c03.e0110'],
  'expressoes': {'c03.e0110': 'p'},
  'proposicao': 'p e q identificam as proposições ou as colunas de valoração da tabela de café e chá A '
                'expressão desta ocorrência é p.',
  'hipoteses': ['As convenções e o domínio são os explicitados na prosa adjacente.'],
  'alcance': 'notacao',
  'observacao': 'p e q identificam as proposições ou as colunas de valoração da tabela de café e chá Não se '
                'contabiliza como prova de um resultado matemático.',
  'testemunhas': {'lean': [], 'py': [], 'wl': []},
  'pendencias': {'lean': '', 'py': '', 'wl': ''}},
 {'ids': ['c03.e0111'],
  'expressoes': {'c03.e0111': 'q'},
  'proposicao': 'p e q identificam as proposições ou as colunas de valoração da tabela de café e chá A '
                'expressão desta ocorrência é q.',
  'hipoteses': ['As convenções e o domínio são os explicitados na prosa adjacente.'],
  'alcance': 'notacao',
  'observacao': 'p e q identificam as proposições ou as colunas de valoração da tabela de café e chá Não se '
                'contabiliza como prova de um resultado matemático.',
  'testemunhas': {'lean': [], 'py': [], 'wl': []},
  'pendencias': {'lean': '', 'py': '', 'wl': ''}},
 {'ids': ['c03.e0128'],
  'expressoes': {'c03.e0128': '\\forall'},
  'proposicao': 'Símbolos de quantificação e suas variáveis ligadas na leitura dos dois escopos; não '
                'designam indivíduos observados A expressão desta ocorrência é \\forall.',
  'hipoteses': ['As convenções e o domínio são os explicitados na prosa adjacente.'],
  'alcance': 'notacao',
  'observacao': 'Símbolos de quantificação e suas variáveis ligadas na leitura dos dois escopos; não '
                'designam indivíduos observados Não se contabiliza como prova de um resultado matemático.',
  'testemunhas': {'lean': [], 'py': [], 'wl': []},
  'pendencias': {'lean': '', 'py': '', 'wl': ''}},
 {'ids': ['c03.e0129'],
  'expressoes': {'c03.e0129': '\\exists'},
  'proposicao': 'Símbolos de quantificação e suas variáveis ligadas na leitura dos dois escopos; não '
                'designam indivíduos observados A expressão desta ocorrência é \\exists.',
  'hipoteses': ['As convenções e o domínio são os explicitados na prosa adjacente.'],
  'alcance': 'notacao',
  'observacao': 'Símbolos de quantificação e suas variáveis ligadas na leitura dos dois escopos; não '
                'designam indivíduos observados Não se contabiliza como prova de um resultado matemático.',
  'testemunhas': {'lean': [], 'py': [], 'wl': []},
  'pendencias': {'lean': '', 'py': '', 'wl': ''}},
 {'ids': ['c03.e0130'],
  'expressoes': {'c03.e0130': 'x'},
  'proposicao': 'Símbolos de quantificação e suas variáveis ligadas na leitura dos dois escopos; não '
                'designam indivíduos observados A expressão desta ocorrência é x.',
  'hipoteses': ['As convenções e o domínio são os explicitados na prosa adjacente.'],
  'alcance': 'notacao',
  'observacao': 'Símbolos de quantificação e suas variáveis ligadas na leitura dos dois escopos; não '
                'designam indivíduos observados Não se contabiliza como prova de um resultado matemático.',
  'testemunhas': {'lean': [], 'py': [], 'wl': []},
  'pendencias': {'lean': '', 'py': '', 'wl': ''}},
 {'ids': ['c03.e0131'],
  'expressoes': {'c03.e0131': 'y'},
  'proposicao': 'Símbolos de quantificação e suas variáveis ligadas na leitura dos dois escopos; não '
                'designam indivíduos observados A expressão desta ocorrência é y.',
  'hipoteses': ['As convenções e o domínio são os explicitados na prosa adjacente.'],
  'alcance': 'notacao',
  'observacao': 'Símbolos de quantificação e suas variáveis ligadas na leitura dos dois escopos; não '
                'designam indivíduos observados Não se contabiliza como prova de um resultado matemático.',
  'testemunhas': {'lean': [], 'py': [], 'wl': []},
  'pendencias': {'lean': '', 'py': '', 'wl': ''}},
 {'ids': ['c03.e0137'],
  'expressoes': {'c03.e0137': 'y'},
  'proposicao': 'Símbolos de quantificação e suas variáveis ligadas na leitura dos dois escopos; não '
                'designam indivíduos observados A expressão desta ocorrência é y.',
  'hipoteses': ['As convenções e o domínio são os explicitados na prosa adjacente.'],
  'alcance': 'notacao',
  'observacao': 'Símbolos de quantificação e suas variáveis ligadas na leitura dos dois escopos; não '
                'designam indivíduos observados Não se contabiliza como prova de um resultado matemático.',
  'testemunhas': {'lean': [], 'py': [], 'wl': []},
  'pendencias': {'lean': '', 'py': '', 'wl': ''}},
 {'ids': ['c03.e0139'],
  'expressoes': {'c03.e0139': 'x'},
  'proposicao': 'Símbolos de quantificação e suas variáveis ligadas na leitura dos dois escopos; não '
                'designam indivíduos observados A expressão desta ocorrência é x.',
  'hipoteses': ['As convenções e o domínio são os explicitados na prosa adjacente.'],
  'alcance': 'notacao',
  'observacao': 'Símbolos de quantificação e suas variáveis ligadas na leitura dos dois escopos; não '
                'designam indivíduos observados Não se contabiliza como prova de um resultado matemático.',
  'testemunhas': {'lean': [], 'py': [], 'wl': []},
  'pendencias': {'lean': '', 'py': '', 'wl': ''}},
 {'ids': ['c03.e0142'],
  'expressoes': {'c03.e0142': 'y'},
  'proposicao': 'Símbolos de quantificação e suas variáveis ligadas na leitura dos dois escopos; não '
                'designam indivíduos observados A expressão desta ocorrência é y.',
  'hipoteses': ['As convenções e o domínio são os explicitados na prosa adjacente.'],
  'alcance': 'notacao',
  'observacao': 'Símbolos de quantificação e suas variáveis ligadas na leitura dos dois escopos; não '
                'designam indivíduos observados Não se contabiliza como prova de um resultado matemático.',
  'testemunhas': {'lean': [], 'py': [], 'wl': []},
  'pendencias': {'lean': '', 'py': '', 'wl': ''}},
 {'ids': ['c03.e0143'],
  'expressoes': {'c03.e0143': 'x'},
  'proposicao': 'Símbolos de quantificação e suas variáveis ligadas na leitura dos dois escopos; não '
                'designam indivíduos observados A expressão desta ocorrência é x.',
  'hipoteses': ['As convenções e o domínio são os explicitados na prosa adjacente.'],
  'alcance': 'notacao',
  'observacao': 'Símbolos de quantificação e suas variáveis ligadas na leitura dos dois escopos; não '
                'designam indivíduos observados Não se contabiliza como prova de um resultado matemático.',
  'testemunhas': {'lean': [], 'py': [], 'wl': []},
  'pendencias': {'lean': '', 'py': '', 'wl': ''}},
 {'ids': ['c03.e0145'],
  'expressoes': {'c03.e0145': 'x'},
  'proposicao': 'Símbolos de quantificação e suas variáveis ligadas na leitura dos dois escopos; não '
                'designam indivíduos observados A expressão desta ocorrência é x.',
  'hipoteses': ['As convenções e o domínio são os explicitados na prosa adjacente.'],
  'alcance': 'notacao',
  'observacao': 'Símbolos de quantificação e suas variáveis ligadas na leitura dos dois escopos; não '
                'designam indivíduos observados Não se contabiliza como prova de um resultado matemático.',
  'testemunhas': {'lean': [], 'py': [], 'wl': []},
  'pendencias': {'lean': '', 'py': '', 'wl': ''}},
 {'ids': ['c03.e0146'],
  'expressoes': {'c03.e0146': 'x'},
  'proposicao': 'Símbolos de quantificação e suas variáveis ligadas na leitura dos dois escopos; não '
                'designam indivíduos observados A expressão desta ocorrência é x.',
  'hipoteses': ['As convenções e o domínio são os explicitados na prosa adjacente.'],
  'alcance': 'notacao',
  'observacao': 'Símbolos de quantificação e suas variáveis ligadas na leitura dos dois escopos; não '
                'designam indivíduos observados Não se contabiliza como prova de um resultado matemático.',
  'testemunhas': {'lean': [], 'py': [], 'wl': []},
  'pendencias': {'lean': '', 'py': '', 'wl': ''}},
 {'ids': ['c03.e0147'],
  'expressoes': {'c03.e0147': 'y'},
  'proposicao': 'Símbolos de quantificação e suas variáveis ligadas na leitura dos dois escopos; não '
                'designam indivíduos observados A expressão desta ocorrência é y.',
  'hipoteses': ['As convenções e o domínio são os explicitados na prosa adjacente.'],
  'alcance': 'notacao',
  'observacao': 'Símbolos de quantificação e suas variáveis ligadas na leitura dos dois escopos; não '
                'designam indivíduos observados Não se contabiliza como prova de um resultado matemático.',
  'testemunhas': {'lean': [], 'py': [], 'wl': []},
  'pendencias': {'lean': '', 'py': '', 'wl': ''}},
 {'ids': ['c03.e0148'],
  'expressoes': {'c03.e0148': 'y'},
  'proposicao': 'Símbolos de quantificação e suas variáveis ligadas na leitura dos dois escopos; não '
                'designam indivíduos observados A expressão desta ocorrência é y.',
  'hipoteses': ['As convenções e o domínio são os explicitados na prosa adjacente.'],
  'alcance': 'notacao',
  'observacao': 'Símbolos de quantificação e suas variáveis ligadas na leitura dos dois escopos; não '
                'designam indivíduos observados Não se contabiliza como prova de um resultado matemático.',
  'testemunhas': {'lean': [], 'py': [], 'wl': []},
  'pendencias': {'lean': '', 'py': '', 'wl': ''}},
 {'ids': ['c03.e0149'],
  'expressoes': {'c03.e0149': 'x'},
  'proposicao': 'Símbolos de quantificação e suas variáveis ligadas na leitura dos dois escopos; não '
                'designam indivíduos observados A expressão desta ocorrência é x.',
  'hipoteses': ['As convenções e o domínio são os explicitados na prosa adjacente.'],
  'alcance': 'notacao',
  'observacao': 'Símbolos de quantificação e suas variáveis ligadas na leitura dos dois escopos; não '
                'designam indivíduos observados Não se contabiliza como prova de um resultado matemático.',
  'testemunhas': {'lean': [], 'py': [], 'wl': []},
  'pendencias': {'lean': '', 'py': '', 'wl': ''}},
 {'ids': ['c03.e0150'],
  'expressoes': {'c03.e0150': '\\forall y'},
  'proposicao': 'Símbolos de quantificação e suas variáveis ligadas na leitura dos dois escopos; não '
                'designam indivíduos observados A expressão desta ocorrência é \\forall y.',
  'hipoteses': ['As convenções e o domínio são os explicitados na prosa adjacente.'],
  'alcance': 'notacao',
  'observacao': 'Símbolos de quantificação e suas variáveis ligadas na leitura dos dois escopos; não '
                'designam indivíduos observados Não se contabiliza como prova de um resultado matemático.',
  'testemunhas': {'lean': [], 'py': [], 'wl': []},
  'pendencias': {'lean': '', 'py': '', 'wl': ''}},
 {'ids': ['c03.e0151'],
  'expressoes': {'c03.e0151': 'y'},
  'proposicao': 'Símbolos de quantificação e suas variáveis ligadas na leitura dos dois escopos; não '
                'designam indivíduos observados A expressão desta ocorrência é y.',
  'hipoteses': ['As convenções e o domínio são os explicitados na prosa adjacente.'],
  'alcance': 'notacao',
  'observacao': 'Símbolos de quantificação e suas variáveis ligadas na leitura dos dois escopos; não '
                'designam indivíduos observados Não se contabiliza como prova de um resultado matemático.',
  'testemunhas': {'lean': [], 'py': [], 'wl': []},
  'pendencias': {'lean': '', 'py': '', 'wl': ''}},
 {'ids': ['c03.e0152'],
  'expressoes': {'c03.e0152': '\\exists x'},
  'proposicao': 'Símbolos de quantificação e suas variáveis ligadas na leitura dos dois escopos; não '
                'designam indivíduos observados A expressão desta ocorrência é \\exists x.',
  'hipoteses': ['As convenções e o domínio são os explicitados na prosa adjacente.'],
  'alcance': 'notacao',
  'observacao': 'Símbolos de quantificação e suas variáveis ligadas na leitura dos dois escopos; não '
                'designam indivíduos observados Não se contabiliza como prova de um resultado matemático.',
  'testemunhas': {'lean': [], 'py': [], 'wl': []},
  'pendencias': {'lean': '', 'py': '', 'wl': ''}},
 {'ids': ['c03.e0153'],
  'expressoes': {'c03.e0153': 'x'},
  'proposicao': 'Símbolos de quantificação e suas variáveis ligadas na leitura dos dois escopos; não '
                'designam indivíduos observados A expressão desta ocorrência é x.',
  'hipoteses': ['As convenções e o domínio são os explicitados na prosa adjacente.'],
  'alcance': 'notacao',
  'observacao': 'Símbolos de quantificação e suas variáveis ligadas na leitura dos dois escopos; não '
                'designam indivíduos observados Não se contabiliza como prova de um resultado matemático.',
  'testemunhas': {'lean': [], 'py': [], 'wl': []},
  'pendencias': {'lean': '', 'py': '', 'wl': ''}},
 {'ids': ['c03.e0154'],
  'expressoes': {'c03.e0154': 'y'},
  'proposicao': 'Símbolos de quantificação e suas variáveis ligadas na leitura dos dois escopos; não '
                'designam indivíduos observados A expressão desta ocorrência é y.',
  'hipoteses': ['As convenções e o domínio são os explicitados na prosa adjacente.'],
  'alcance': 'notacao',
  'observacao': 'Símbolos de quantificação e suas variáveis ligadas na leitura dos dois escopos; não '
                'designam indivíduos observados Não se contabiliza como prova de um resultado matemático.',
  'testemunhas': {'lean': [], 'py': [], 'wl': []},
  'pendencias': {'lean': '', 'py': '', 'wl': ''}},
 {'ids': ['c03.e0158'],
  'expressoes': {'c03.e0158': 'S'},
  'proposicao': 'Nomes dos conjuntos ou indivíduo percorrido na inferência de inclusão e símbolo de '
                'equivalência lógica A expressão desta ocorrência é S.',
  'hipoteses': ['As convenções e o domínio são os explicitados na prosa adjacente.'],
  'alcance': 'notacao',
  'observacao': 'Nomes dos conjuntos ou indivíduo percorrido na inferência de inclusão e símbolo de '
                'equivalência lógica Não se contabiliza como prova de um resultado matemático.',
  'testemunhas': {'lean': [], 'py': [], 'wl': []},
  'pendencias': {'lean': '', 'py': '', 'wl': ''}},
 {'ids': ['c03.e0159'],
  'expressoes': {'c03.e0159': 'L'},
  'proposicao': 'Nomes dos conjuntos ou indivíduo percorrido na inferência de inclusão e símbolo de '
                'equivalência lógica A expressão desta ocorrência é L.',
  'hipoteses': ['As convenções e o domínio são os explicitados na prosa adjacente.'],
  'alcance': 'notacao',
  'observacao': 'Nomes dos conjuntos ou indivíduo percorrido na inferência de inclusão e símbolo de '
                'equivalência lógica Não se contabiliza como prova de um resultado matemático.',
  'testemunhas': {'lean': [], 'py': [], 'wl': []},
  'pendencias': {'lean': '', 'py': '', 'wl': ''}},
 {'ids': ['c03.e0160'],
  'expressoes': {'c03.e0160': 'N'},
  'proposicao': 'Nomes dos conjuntos ou indivíduo percorrido na inferência de inclusão e símbolo de '
                'equivalência lógica A expressão desta ocorrência é N.',
  'hipoteses': ['As convenções e o domínio são os explicitados na prosa adjacente.'],
  'alcance': 'notacao',
  'observacao': 'Nomes dos conjuntos ou indivíduo percorrido na inferência de inclusão e símbolo de '
                'equivalência lógica Não se contabiliza como prova de um resultado matemático.',
  'testemunhas': {'lean': [], 'py': [], 'wl': []},
  'pendencias': {'lean': '', 'py': '', 'wl': ''}},
 {'ids': ['c03.e0161'],
  'expressoes': {'c03.e0161': 'M'},
  'proposicao': 'Nomes dos conjuntos ou indivíduo percorrido na inferência de inclusão e símbolo de '
                'equivalência lógica A expressão desta ocorrência é M.',
  'hipoteses': ['As convenções e o domínio são os explicitados na prosa adjacente.'],
  'alcance': 'notacao',
  'observacao': 'Nomes dos conjuntos ou indivíduo percorrido na inferência de inclusão e símbolo de '
                'equivalência lógica Não se contabiliza como prova de um resultado matemático.',
  'testemunhas': {'lean': [], 'py': [], 'wl': []},
  'pendencias': {'lean': '', 'py': '', 'wl': ''}},
 {'ids': ['c03.e0165'],
  'expressoes': {'c03.e0165': 'x'},
  'proposicao': 'Nomes dos conjuntos ou indivíduo percorrido na inferência de inclusão e símbolo de '
                'equivalência lógica A expressão desta ocorrência é x.',
  'hipoteses': ['As convenções e o domínio são os explicitados na prosa adjacente.'],
  'alcance': 'notacao',
  'observacao': 'Nomes dos conjuntos ou indivíduo percorrido na inferência de inclusão e símbolo de '
                'equivalência lógica Não se contabiliza como prova de um resultado matemático.',
  'testemunhas': {'lean': [], 'py': [], 'wl': []},
  'pendencias': {'lean': '', 'py': '', 'wl': ''}},
 {'ids': ['c03.e0166'],
  'expressoes': {'c03.e0166': 'S'},
  'proposicao': 'Nomes dos conjuntos ou indivíduo percorrido na inferência de inclusão e símbolo de '
                'equivalência lógica A expressão desta ocorrência é S.',
  'hipoteses': ['As convenções e o domínio são os explicitados na prosa adjacente.'],
  'alcance': 'notacao',
  'observacao': 'Nomes dos conjuntos ou indivíduo percorrido na inferência de inclusão e símbolo de '
                'equivalência lógica Não se contabiliza como prova de um resultado matemático.',
  'testemunhas': {'lean': [], 'py': [], 'wl': []},
  'pendencias': {'lean': '', 'py': '', 'wl': ''}},
 {'ids': ['c03.e0168'],
  'expressoes': {'c03.e0168': 'L'},
  'proposicao': 'Nomes dos conjuntos ou indivíduo percorrido na inferência de inclusão e símbolo de '
                'equivalência lógica A expressão desta ocorrência é L.',
  'hipoteses': ['As convenções e o domínio são os explicitados na prosa adjacente.'],
  'alcance': 'notacao',
  'observacao': 'Nomes dos conjuntos ou indivíduo percorrido na inferência de inclusão e símbolo de '
                'equivalência lógica Não se contabiliza como prova de um resultado matemático.',
  'testemunhas': {'lean': [], 'py': [], 'wl': []},
  'pendencias': {'lean': '', 'py': '', 'wl': ''}},
 {'ids': ['c03.e0170'],
  'expressoes': {'c03.e0170': 'N'},
  'proposicao': 'Nomes dos conjuntos ou indivíduo percorrido na inferência de inclusão e símbolo de '
                'equivalência lógica A expressão desta ocorrência é N.',
  'hipoteses': ['As convenções e o domínio são os explicitados na prosa adjacente.'],
  'alcance': 'notacao',
  'observacao': 'Nomes dos conjuntos ou indivíduo percorrido na inferência de inclusão e símbolo de '
                'equivalência lógica Não se contabiliza como prova de um resultado matemático.',
  'testemunhas': {'lean': [], 'py': [], 'wl': []},
  'pendencias': {'lean': '', 'py': '', 'wl': ''}},
 {'ids': ['c03.e0171'],
  'expressoes': {'c03.e0171': 'x'},
  'proposicao': 'Nomes dos conjuntos ou indivíduo percorrido na inferência de inclusão e símbolo de '
                'equivalência lógica A expressão desta ocorrência é x.',
  'hipoteses': ['As convenções e o domínio são os explicitados na prosa adjacente.'],
  'alcance': 'notacao',
  'observacao': 'Nomes dos conjuntos ou indivíduo percorrido na inferência de inclusão e símbolo de '
                'equivalência lógica Não se contabiliza como prova de um resultado matemático.',
  'testemunhas': {'lean': [], 'py': [], 'wl': []},
  'pendencias': {'lean': '', 'py': '', 'wl': ''}},
 {'ids': ['c03.e0172'],
  'expressoes': {'c03.e0172': 'S'},
  'proposicao': 'Nomes dos conjuntos ou indivíduo percorrido na inferência de inclusão e símbolo de '
                'equivalência lógica A expressão desta ocorrência é S.',
  'hipoteses': ['As convenções e o domínio são os explicitados na prosa adjacente.'],
  'alcance': 'notacao',
  'observacao': 'Nomes dos conjuntos ou indivíduo percorrido na inferência de inclusão e símbolo de '
                'equivalência lógica Não se contabiliza como prova de um resultado matemático.',
  'testemunhas': {'lean': [], 'py': [], 'wl': []},
  'pendencias': {'lean': '', 'py': '', 'wl': ''}},
 {'ids': ['c03.e0179'],
  'expressoes': {'c03.e0179': '\\Longleftrightarrow'},
  'proposicao': 'Nomes dos conjuntos ou indivíduo percorrido na inferência de inclusão e símbolo de '
                'equivalência lógica A expressão desta ocorrência é \\Longleftrightarrow.',
  'hipoteses': ['As convenções e o domínio são os explicitados na prosa adjacente.'],
  'alcance': 'notacao',
  'observacao': 'Nomes dos conjuntos ou indivíduo percorrido na inferência de inclusão e símbolo de '
                'equivalência lógica Não se contabiliza como prova de um resultado matemático.',
  'testemunhas': {'lean': [], 'py': [], 'wl': []},
  'pendencias': {'lean': '', 'py': '', 'wl': ''}},
 {'ids': ['c03.e0182'],
  'expressoes': {'c03.e0182': '\\Sigma'},
  'proposicao': 'Alfabeto, cadeias, partes concatenadas e cadeia vazia; sigma do alfabeto é distinguido do '
                'somatório A expressão desta ocorrência é \\Sigma.',
  'hipoteses': ['As convenções e o domínio são os explicitados na prosa adjacente.'],
  'alcance': 'notacao',
  'observacao': 'Alfabeto, cadeias, partes concatenadas e cadeia vazia; sigma do alfabeto é distinguido do '
                'somatório Não se contabiliza como prova de um resultado matemático.',
  'testemunhas': {'lean': [], 'py': [], 'wl': []},
  'pendencias': {'lean': '', 'py': '', 'wl': ''}},
 {'ids': ['c03.e0183'],
  'expressoes': {'c03.e0183': '\\sum'},
  'proposicao': 'Alfabeto, cadeias, partes concatenadas e cadeia vazia; sigma do alfabeto é distinguido do '
                'somatório A expressão desta ocorrência é \\sum.',
  'hipoteses': ['As convenções e o domínio são os explicitados na prosa adjacente.'],
  'alcance': 'notacao',
  'observacao': 'Alfabeto, cadeias, partes concatenadas e cadeia vazia; sigma do alfabeto é distinguido do '
                'somatório Não se contabiliza como prova de um resultado matemático.',
  'testemunhas': {'lean': [], 'py': [], 'wl': []},
  'pendencias': {'lean': '', 'py': '', 'wl': ''}},
 {'ids': ['c03.e0184'],
  'expressoes': {'c03.e0184': 'u'},
  'proposicao': 'Alfabeto, cadeias, partes concatenadas e cadeia vazia; sigma do alfabeto é distinguido do '
                'somatório A expressão desta ocorrência é u.',
  'hipoteses': ['As convenções e o domínio são os explicitados na prosa adjacente.'],
  'alcance': 'notacao',
  'observacao': 'Alfabeto, cadeias, partes concatenadas e cadeia vazia; sigma do alfabeto é distinguido do '
                'somatório Não se contabiliza como prova de um resultado matemático.',
  'testemunhas': {'lean': [], 'py': [], 'wl': []},
  'pendencias': {'lean': '', 'py': '', 'wl': ''}},
 {'ids': ['c03.e0185'],
  'expressoes': {'c03.e0185': 'v'},
  'proposicao': 'Alfabeto, cadeias, partes concatenadas e cadeia vazia; sigma do alfabeto é distinguido do '
                'somatório A expressão desta ocorrência é v.',
  'hipoteses': ['As convenções e o domínio são os explicitados na prosa adjacente.'],
  'alcance': 'notacao',
  'observacao': 'Alfabeto, cadeias, partes concatenadas e cadeia vazia; sigma do alfabeto é distinguido do '
                'somatório Não se contabiliza como prova de um resultado matemático.',
  'testemunhas': {'lean': [], 'py': [], 'wl': []},
  'pendencias': {'lean': '', 'py': '', 'wl': ''}},
 {'ids': ['c03.e0189'],
  'expressoes': {'c03.e0189': 'a'},
  'proposicao': 'Alfabeto, cadeias, partes concatenadas e cadeia vazia; sigma do alfabeto é distinguido do '
                'somatório A expressão desta ocorrência é a.',
  'hipoteses': ['As convenções e o domínio são os explicitados na prosa adjacente.'],
  'alcance': 'notacao',
  'observacao': 'Alfabeto, cadeias, partes concatenadas e cadeia vazia; sigma do alfabeto é distinguido do '
                'somatório Não se contabiliza como prova de um resultado matemático.',
  'testemunhas': {'lean': [], 'py': [], 'wl': []},
  'pendencias': {'lean': '', 'py': '', 'wl': ''}},
 {'ids': ['c03.e0190'],
  'expressoes': {'c03.e0190': 'b'},
  'proposicao': 'Alfabeto, cadeias, partes concatenadas e cadeia vazia; sigma do alfabeto é distinguido do '
                'somatório A expressão desta ocorrência é b.',
  'hipoteses': ['As convenções e o domínio são os explicitados na prosa adjacente.'],
  'alcance': 'notacao',
  'observacao': 'Alfabeto, cadeias, partes concatenadas e cadeia vazia; sigma do alfabeto é distinguido do '
                'somatório Não se contabiliza como prova de um resultado matemático.',
  'testemunhas': {'lean': [], 'py': [], 'wl': []},
  'pendencias': {'lean': '', 'py': '', 'wl': ''}},
 {'ids': ['c03.e0191'],
  'expressoes': {'c03.e0191': 'c'},
  'proposicao': 'Alfabeto, cadeias, partes concatenadas e cadeia vazia; sigma do alfabeto é distinguido do '
                'somatório A expressão desta ocorrência é c.',
  'hipoteses': ['As convenções e o domínio são os explicitados na prosa adjacente.'],
  'alcance': 'notacao',
  'observacao': 'Alfabeto, cadeias, partes concatenadas e cadeia vazia; sigma do alfabeto é distinguido do '
                'somatório Não se contabiliza como prova de um resultado matemático.',
  'testemunhas': {'lean': [], 'py': [], 'wl': []},
  'pendencias': {'lean': '', 'py': '', 'wl': ''}},
 {'ids': ['c03.e0194'],
  'expressoes': {'c03.e0194': '\\varepsilon'},
  'proposicao': 'Alfabeto, cadeias, partes concatenadas e cadeia vazia; sigma do alfabeto é distinguido do '
                'somatório A expressão desta ocorrência é \\varepsilon.',
  'hipoteses': ['As convenções e o domínio são os explicitados na prosa adjacente.'],
  'alcance': 'notacao',
  'observacao': 'Alfabeto, cadeias, partes concatenadas e cadeia vazia; sigma do alfabeto é distinguido do '
                'somatório Não se contabiliza como prova de um resultado matemático.',
  'testemunhas': {'lean': [], 'py': [], 'wl': []},
  'pendencias': {'lean': '', 'py': '', 'wl': ''}},
 {'ids': ['c03.e0197'],
  'expressoes': {'c03.e0197': 'E'},
  'proposicao': 'Tipos básicos, conectivo, predicados e variáveis na introdução do cálculo lambda; nenhuma '
                'proposição é afirmada pela simples ocorrência do nome A expressão desta ocorrência é E.',
  'hipoteses': ['As convenções e o domínio são os explicitados na prosa adjacente.'],
  'alcance': 'notacao',
  'observacao': 'Tipos básicos, conectivo, predicados e variáveis na introdução do cálculo lambda; nenhuma '
                'proposição é afirmada pela simples ocorrência do nome Não se contabiliza como prova de um '
                'resultado matemático.',
  'testemunhas': {'lean': [], 'py': [], 'wl': []},
  'pendencias': {'lean': '', 'py': '', 'wl': ''}},
 {'ids': ['c03.e0198'],
  'expressoes': {'c03.e0198': '\\mathrm{Prop}'},
  'proposicao': 'Tipos básicos, conectivo, predicados e variáveis na introdução do cálculo lambda; nenhuma '
                'proposição é afirmada pela simples ocorrência do nome A expressão desta ocorrência é '
                '\\mathrm{Prop}.',
  'hipoteses': ['As convenções e o domínio são os explicitados na prosa adjacente.'],
  'alcance': 'notacao',
  'observacao': 'Tipos básicos, conectivo, predicados e variáveis na introdução do cálculo lambda; nenhuma '
                'proposição é afirmada pela simples ocorrência do nome Não se contabiliza como prova de um '
                'resultado matemático.',
  'testemunhas': {'lean': [], 'py': [], 'wl': []},
  'pendencias': {'lean': '', 'py': '', 'wl': ''}},
 {'ids': ['c03.e0200'],
  'expressoes': {'c03.e0200': '\\Rightarrow'},
  'proposicao': 'Tipos básicos, conectivo, predicados e variáveis na introdução do cálculo lambda; nenhuma '
                'proposição é afirmada pela simples ocorrência do nome A expressão desta ocorrência é '
                '\\Rightarrow.',
  'hipoteses': ['As convenções e o domínio são os explicitados na prosa adjacente.'],
  'alcance': 'notacao',
  'observacao': 'Tipos básicos, conectivo, predicados e variáveis na introdução do cálculo lambda; nenhuma '
                'proposição é afirmada pela simples ocorrência do nome Não se contabiliza como prova de um '
                'resultado matemático.',
  'testemunhas': {'lean': [], 'py': [], 'wl': []},
  'pendencias': {'lean': '', 'py': '', 'wl': ''}},
 {'ids': ['c03.e0204'],
  'expressoes': {'c03.e0204': 'W'},
  'proposicao': 'Tipos básicos, conectivo, predicados e variáveis na introdução do cálculo lambda; nenhuma '
                'proposição é afirmada pela simples ocorrência do nome A expressão desta ocorrência é W.',
  'hipoteses': ['As convenções e o domínio são os explicitados na prosa adjacente.'],
  'alcance': 'notacao',
  'observacao': 'Tipos básicos, conectivo, predicados e variáveis na introdução do cálculo lambda; nenhuma '
                'proposição é afirmada pela simples ocorrência do nome Não se contabiliza como prova de um '
                'resultado matemático.',
  'testemunhas': {'lean': [], 'py': [], 'wl': []},
  'pendencias': {'lean': '', 'py': '', 'wl': ''}},
 {'ids': ['c03.e0205'],
  'expressoes': {'c03.e0205': 'T'},
  'proposicao': 'Tipos básicos, conectivo, predicados e variáveis na introdução do cálculo lambda; nenhuma '
                'proposição é afirmada pela simples ocorrência do nome A expressão desta ocorrência é T.',
  'hipoteses': ['As convenções e o domínio são os explicitados na prosa adjacente.'],
  'alcance': 'notacao',
  'observacao': 'Tipos básicos, conectivo, predicados e variáveis na introdução do cálculo lambda; nenhuma '
                'proposição é afirmada pela simples ocorrência do nome Não se contabiliza como prova de um '
                'resultado matemático.',
  'testemunhas': {'lean': [], 'py': [], 'wl': []},
  'pendencias': {'lean': '', 'py': '', 'wl': ''}},
 {'ids': ['c03.e0207'],
  'expressoes': {'c03.e0207': 'O'},
  'proposicao': 'Tipos básicos, conectivo, predicados e variáveis na introdução do cálculo lambda; nenhuma '
                'proposição é afirmada pela simples ocorrência do nome A expressão desta ocorrência é O.',
  'hipoteses': ['As convenções e o domínio são os explicitados na prosa adjacente.'],
  'alcance': 'notacao',
  'observacao': 'Tipos básicos, conectivo, predicados e variáveis na introdução do cálculo lambda; nenhuma '
                'proposição é afirmada pela simples ocorrência do nome Não se contabiliza como prova de um '
                'resultado matemático.',
  'testemunhas': {'lean': [], 'py': [], 'wl': []},
  'pendencias': {'lean': '', 'py': '', 'wl': ''}},
 {'ids': ['c03.e0208'],
  'expressoes': {'c03.e0208': '\\lambda'},
  'proposicao': 'Tipos básicos, conectivo, predicados e variáveis na introdução do cálculo lambda; nenhuma '
                'proposição é afirmada pela simples ocorrência do nome A expressão desta ocorrência é '
                '\\lambda.',
  'hipoteses': ['As convenções e o domínio são os explicitados na prosa adjacente.'],
  'alcance': 'notacao',
  'observacao': 'Tipos básicos, conectivo, predicados e variáveis na introdução do cálculo lambda; nenhuma '
                'proposição é afirmada pela simples ocorrência do nome Não se contabiliza como prova de um '
                'resultado matemático.',
  'testemunhas': {'lean': [], 'py': [], 'wl': []},
  'pendencias': {'lean': '', 'py': '', 'wl': ''}},
 {'ids': ['c03.e0210'],
  'expressoes': {'c03.e0210': 'x'},
  'proposicao': 'Tipos básicos, conectivo, predicados e variáveis na introdução do cálculo lambda; nenhuma '
                'proposição é afirmada pela simples ocorrência do nome A expressão desta ocorrência é x.',
  'hipoteses': ['As convenções e o domínio são os explicitados na prosa adjacente.'],
  'alcance': 'notacao',
  'observacao': 'Tipos básicos, conectivo, predicados e variáveis na introdução do cálculo lambda; nenhuma '
                'proposição é afirmada pela simples ocorrência do nome Não se contabiliza como prova de um '
                'resultado matemático.',
  'testemunhas': {'lean': [], 'py': [], 'wl': []},
  'pendencias': {'lean': '', 'py': '', 'wl': ''}},
 {'ids': ['c03.e0211'],
  'expressoes': {'c03.e0211': 'P'},
  'proposicao': 'Tipos básicos, conectivo, predicados e variáveis na introdução do cálculo lambda; nenhuma '
                'proposição é afirmada pela simples ocorrência do nome A expressão desta ocorrência é P.',
  'hipoteses': ['As convenções e o domínio são os explicitados na prosa adjacente.'],
  'alcance': 'notacao',
  'observacao': 'Tipos básicos, conectivo, predicados e variáveis na introdução do cálculo lambda; nenhuma '
                'proposição é afirmada pela simples ocorrência do nome Não se contabiliza como prova de um '
                'resultado matemático.',
  'testemunhas': {'lean': [], 'py': [], 'wl': []},
  'pendencias': {'lean': '', 'py': '', 'wl': ''}},
 {'ids': ['c03.e0212'],
  'expressoes': {'c03.e0212': 'W'},
  'proposicao': 'Tipos básicos, conectivo, predicados e variáveis na introdução do cálculo lambda; nenhuma '
                'proposição é afirmada pela simples ocorrência do nome A expressão desta ocorrência é W.',
  'hipoteses': ['As convenções e o domínio são os explicitados na prosa adjacente.'],
  'alcance': 'notacao',
  'observacao': 'Tipos básicos, conectivo, predicados e variáveis na introdução do cálculo lambda; nenhuma '
                'proposição é afirmada pela simples ocorrência do nome Não se contabiliza como prova de um '
                'resultado matemático.',
  'testemunhas': {'lean': [], 'py': [], 'wl': []},
  'pendencias': {'lean': '', 'py': '', 'wl': ''}},
 {'ids': ['c03.e0214'],
  'expressoes': {'c03.e0214': 'P'},
  'proposicao': 'Tipos básicos, conectivo, predicados e variáveis na introdução do cálculo lambda; nenhuma '
                'proposição é afirmada pela simples ocorrência do nome A expressão desta ocorrência é P.',
  'hipoteses': ['As convenções e o domínio são os explicitados na prosa adjacente.'],
  'alcance': 'notacao',
  'observacao': 'Tipos básicos, conectivo, predicados e variáveis na introdução do cálculo lambda; nenhuma '
                'proposição é afirmada pela simples ocorrência do nome Não se contabiliza como prova de um '
                'resultado matemático.',
  'testemunhas': {'lean': [], 'py': [], 'wl': []},
  'pendencias': {'lean': '', 'py': '', 'wl': ''}},
 {'ids': ['c03.e0215'],
  'expressoes': {'c03.e0215': 'W'},
  'proposicao': 'Tipos básicos, conectivo, predicados e variáveis na introdução do cálculo lambda; nenhuma '
                'proposição é afirmada pela simples ocorrência do nome A expressão desta ocorrência é W.',
  'hipoteses': ['As convenções e o domínio são os explicitados na prosa adjacente.'],
  'alcance': 'notacao',
  'observacao': 'Tipos básicos, conectivo, predicados e variáveis na introdução do cálculo lambda; nenhuma '
                'proposição é afirmada pela simples ocorrência do nome Não se contabiliza como prova de um '
                'resultado matemático.',
  'testemunhas': {'lean': [], 'py': [], 'wl': []},
  'pendencias': {'lean': '', 'py': '', 'wl': ''}},
 {'ids': ['c03.e0216'],
  'expressoes': {'c03.e0216': 'x'},
  'proposicao': 'Tipos básicos, conectivo, predicados e variáveis na introdução do cálculo lambda; nenhuma '
                'proposição é afirmada pela simples ocorrência do nome A expressão desta ocorrência é x.',
  'hipoteses': ['As convenções e o domínio são os explicitados na prosa adjacente.'],
  'alcance': 'notacao',
  'observacao': 'Tipos básicos, conectivo, predicados e variáveis na introdução do cálculo lambda; nenhuma '
                'proposição é afirmada pela simples ocorrência do nome Não se contabiliza como prova de um '
                'resultado matemático.',
  'testemunhas': {'lean': [], 'py': [], 'wl': []},
  'pendencias': {'lean': '', 'py': '', 'wl': ''}},
 {'ids': ['c03.e0217'],
  'expressoes': {'c03.e0217': 'F'},
  'proposicao': 'Tipos básicos, conectivo, predicados e variáveis na introdução do cálculo lambda; nenhuma '
                'proposição é afirmada pela simples ocorrência do nome A expressão desta ocorrência é F.',
  'hipoteses': ['As convenções e o domínio são os explicitados na prosa adjacente.'],
  'alcance': 'notacao',
  'observacao': 'Tipos básicos, conectivo, predicados e variáveis na introdução do cálculo lambda; nenhuma '
                'proposição é afirmada pela simples ocorrência do nome Não se contabiliza como prova de um '
                'resultado matemático.',
  'testemunhas': {'lean': [], 'py': [], 'wl': []},
  'pendencias': {'lean': '', 'py': '', 'wl': ''}},
 {'ids': ['c03.e0218'],
  'expressoes': {'c03.e0218': 'G'},
  'proposicao': 'Tipos básicos, conectivo, predicados e variáveis na introdução do cálculo lambda; nenhuma '
                'proposição é afirmada pela simples ocorrência do nome A expressão desta ocorrência é G.',
  'hipoteses': ['As convenções e o domínio são os explicitados na prosa adjacente.'],
  'alcance': 'notacao',
  'observacao': 'Tipos básicos, conectivo, predicados e variáveis na introdução do cálculo lambda; nenhuma '
                'proposição é afirmada pela simples ocorrência do nome Não se contabiliza como prova de um '
                'resultado matemático.',
  'testemunhas': {'lean': [], 'py': [], 'wl': []},
  'pendencias': {'lean': '', 'py': '', 'wl': ''}},
 {'ids': ['c03.e0221'],
  'expressoes': {'c03.e0221': 'F'},
  'proposicao': 'Tipos básicos, conectivo, predicados e variáveis na introdução do cálculo lambda; nenhuma '
                'proposição é afirmada pela simples ocorrência do nome A expressão desta ocorrência é F.',
  'hipoteses': ['As convenções e o domínio são os explicitados na prosa adjacente.'],
  'alcance': 'notacao',
  'observacao': 'Tipos básicos, conectivo, predicados e variáveis na introdução do cálculo lambda; nenhuma '
                'proposição é afirmada pela simples ocorrência do nome Não se contabiliza como prova de um '
                'resultado matemático.',
  'testemunhas': {'lean': [], 'py': [], 'wl': []},
  'pendencias': {'lean': '', 'py': '', 'wl': ''}},
 {'ids': ['c03.e0222'],
  'expressoes': {'c03.e0222': 'G'},
  'proposicao': 'Tipos básicos, conectivo, predicados e variáveis na introdução do cálculo lambda; nenhuma '
                'proposição é afirmada pela simples ocorrência do nome A expressão desta ocorrência é G.',
  'hipoteses': ['As convenções e o domínio são os explicitados na prosa adjacente.'],
  'alcance': 'notacao',
  'observacao': 'Tipos básicos, conectivo, predicados e variáveis na introdução do cálculo lambda; nenhuma '
                'proposição é afirmada pela simples ocorrência do nome Não se contabiliza como prova de um '
                'resultado matemático.',
  'testemunhas': {'lean': [], 'py': [], 'wl': []},
  'pendencias': {'lean': '', 'py': '', 'wl': ''}},
 {'ids': ['c03.e0223'],
  'expressoes': {'c03.e0223': 'x'},
  'proposicao': 'Tipos básicos, conectivo, predicados e variáveis na introdução do cálculo lambda; nenhuma '
                'proposição é afirmada pela simples ocorrência do nome A expressão desta ocorrência é x.',
  'hipoteses': ['As convenções e o domínio são os explicitados na prosa adjacente.'],
  'alcance': 'notacao',
  'observacao': 'Tipos básicos, conectivo, predicados e variáveis na introdução do cálculo lambda; nenhuma '
                'proposição é afirmada pela simples ocorrência do nome Não se contabiliza como prova de um '
                'resultado matemático.',
  'testemunhas': {'lean': [], 'py': [], 'wl': []},
  'pendencias': {'lean': '', 'py': '', 'wl': ''}},
 {'ids': ['c03.e0224'],
  'expressoes': {'c03.e0224': 'W'},
  'proposicao': 'Tipos básicos, conectivo, predicados e variáveis na introdução do cálculo lambda; nenhuma '
                'proposição é afirmada pela simples ocorrência do nome A expressão desta ocorrência é W.',
  'hipoteses': ['As convenções e o domínio são os explicitados na prosa adjacente.'],
  'alcance': 'notacao',
  'observacao': 'Tipos básicos, conectivo, predicados e variáveis na introdução do cálculo lambda; nenhuma '
                'proposição é afirmada pela simples ocorrência do nome Não se contabiliza como prova de um '
                'resultado matemático.',
  'testemunhas': {'lean': [], 'py': [], 'wl': []},
  'pendencias': {'lean': '', 'py': '', 'wl': ''}},
 {'ids': ['c03.e0226'],
  'expressoes': {'c03.e0226': 'Q_W'},
  'proposicao': 'Tipos básicos, conectivo, predicados e variáveis na introdução do cálculo lambda; nenhuma '
                'proposição é afirmada pela simples ocorrência do nome A expressão desta ocorrência é Q_W.',
  'hipoteses': ['As convenções e o domínio são os explicitados na prosa adjacente.'],
  'alcance': 'notacao',
  'observacao': 'Tipos básicos, conectivo, predicados e variáveis na introdução do cálculo lambda; nenhuma '
                'proposição é afirmada pela simples ocorrência do nome Não se contabiliza como prova de um '
                'resultado matemático.',
  'testemunhas': {'lean': [], 'py': [], 'wl': []},
  'pendencias': {'lean': '', 'py': '', 'wl': ''}},
 {'ids': ['c03.e0230'],
  'expressoes': {'c03.e0230': 'y'},
  'proposicao': 'Variáveis ligadas, predicado recebido e argumento ainda livre durante a aplicação do '
                'quantificador do objeto A expressão desta ocorrência é y.',
  'hipoteses': ['As convenções e o domínio são os explicitados na prosa adjacente.'],
  'alcance': 'notacao',
  'observacao': 'Variáveis ligadas, predicado recebido e argumento ainda livre durante a aplicação do '
                'quantificador do objeto Não se contabiliza como prova de um resultado matemático.',
  'testemunhas': {'lean': [], 'py': [], 'wl': []},
  'pendencias': {'lean': '', 'py': '', 'wl': ''}},
 {'ids': ['c03.e0231'],
  'expressoes': {'c03.e0231': 'F'},
  'proposicao': 'Variáveis ligadas, predicado recebido e argumento ainda livre durante a aplicação do '
                'quantificador do objeto A expressão desta ocorrência é F.',
  'hipoteses': ['As convenções e o domínio são os explicitados na prosa adjacente.'],
  'alcance': 'notacao',
  'observacao': 'Variáveis ligadas, predicado recebido e argumento ainda livre durante a aplicação do '
                'quantificador do objeto Não se contabiliza como prova de um resultado matemático.',
  'testemunhas': {'lean': [], 'py': [], 'wl': []},
  'pendencias': {'lean': '', 'py': '', 'wl': ''}},
 {'ids': ['c03.e0232'],
  'expressoes': {'c03.e0232': 'x'},
  'proposicao': 'Variáveis ligadas, predicado recebido e argumento ainda livre durante a aplicação do '
                'quantificador do objeto A expressão desta ocorrência é x.',
  'hipoteses': ['As convenções e o domínio são os explicitados na prosa adjacente.'],
  'alcance': 'notacao',
  'observacao': 'Variáveis ligadas, predicado recebido e argumento ainda livre durante a aplicação do '
                'quantificador do objeto Não se contabiliza como prova de um resultado matemático.',
  'testemunhas': {'lean': [], 'py': [], 'wl': []},
  'pendencias': {'lean': '', 'py': '', 'wl': ''}},
 {'ids': ['c03.e0234'],
  'expressoes': {'c03.e0234': 'z'},
  'proposicao': 'Variáveis ligadas, predicado recebido e argumento ainda livre durante a aplicação do '
                'quantificador do objeto A expressão desta ocorrência é z.',
  'hipoteses': ['As convenções e o domínio são os explicitados na prosa adjacente.'],
  'alcance': 'notacao',
  'observacao': 'Variáveis ligadas, predicado recebido e argumento ainda livre durante a aplicação do '
                'quantificador do objeto Não se contabiliza como prova de um resultado matemático.',
  'testemunhas': {'lean': [], 'py': [], 'wl': []},
  'pendencias': {'lean': '', 'py': '', 'wl': ''}},
 {'ids': ['c03.e0235'],
  'expressoes': {'c03.e0235': 'y'},
  'proposicao': 'Variáveis ligadas, predicado recebido e argumento ainda livre durante a aplicação do '
                'quantificador do objeto A expressão desta ocorrência é y.',
  'hipoteses': ['As convenções e o domínio são os explicitados na prosa adjacente.'],
  'alcance': 'notacao',
  'observacao': 'Variáveis ligadas, predicado recebido e argumento ainda livre durante a aplicação do '
                'quantificador do objeto Não se contabiliza como prova de um resultado matemático.',
  'testemunhas': {'lean': [], 'py': [], 'wl': []},
  'pendencias': {'lean': '', 'py': '', 'wl': ''}},
 {'ids': ['c03.e0236'],
  'expressoes': {'c03.e0236': 'Q_T'},
  'proposicao': 'Variáveis ligadas, predicado recebido e argumento ainda livre durante a aplicação do '
                'quantificador do objeto A expressão desta ocorrência é Q_T.',
  'hipoteses': ['As convenções e o domínio são os explicitados na prosa adjacente.'],
  'alcance': 'notacao',
  'observacao': 'Variáveis ligadas, predicado recebido e argumento ainda livre durante a aplicação do '
                'quantificador do objeto Não se contabiliza como prova de um resultado matemático.',
  'testemunhas': {'lean': [], 'py': [], 'wl': []},
  'pendencias': {'lean': '', 'py': '', 'wl': ''}},
 {'ids': ['c03.e0238'],
  'expressoes': {'c03.e0238': 'Q_T'},
  'proposicao': 'Variáveis ligadas, predicado recebido e argumento ainda livre durante a aplicação do '
                'quantificador do objeto A expressão desta ocorrência é Q_T.',
  'hipoteses': ['As convenções e o domínio são os explicitados na prosa adjacente.'],
  'alcance': 'notacao',
  'observacao': 'Variáveis ligadas, predicado recebido e argumento ainda livre durante a aplicação do '
                'quantificador do objeto Não se contabiliza como prova de um resultado matemático.',
  'testemunhas': {'lean': [], 'py': [], 'wl': []},
  'pendencias': {'lean': '', 'py': '', 'wl': ''}},
 {'ids': ['c03.e0239'],
  'expressoes': {'c03.e0239': 'F'},
  'proposicao': 'Variáveis ligadas, predicado recebido e argumento ainda livre durante a aplicação do '
                'quantificador do objeto A expressão desta ocorrência é F.',
  'hipoteses': ['As convenções e o domínio são os explicitados na prosa adjacente.'],
  'alcance': 'notacao',
  'observacao': 'Variáveis ligadas, predicado recebido e argumento ainda livre durante a aplicação do '
                'quantificador do objeto Não se contabiliza como prova de um resultado matemático.',
  'testemunhas': {'lean': [], 'py': [], 'wl': []},
  'pendencias': {'lean': '', 'py': '', 'wl': ''}},
 {'ids': ['c03.e0241'],
  'expressoes': {'c03.e0241': 'y'},
  'proposicao': 'Variáveis ligadas, predicado recebido e argumento ainda livre durante a aplicação do '
                'quantificador do objeto A expressão desta ocorrência é y.',
  'hipoteses': ['As convenções e o domínio são os explicitados na prosa adjacente.'],
  'alcance': 'notacao',
  'observacao': 'Variáveis ligadas, predicado recebido e argumento ainda livre durante a aplicação do '
                'quantificador do objeto Não se contabiliza como prova de um resultado matemático.',
  'testemunhas': {'lean': [], 'py': [], 'wl': []},
  'pendencias': {'lean': '', 'py': '', 'wl': ''}},
 {'ids': ['c03.e0242'],
  'expressoes': {'c03.e0242': 'z'},
  'proposicao': 'Variáveis ligadas, predicado recebido e argumento ainda livre durante a aplicação do '
                'quantificador do objeto A expressão desta ocorrência é z.',
  'hipoteses': ['As convenções e o domínio são os explicitados na prosa adjacente.'],
  'alcance': 'notacao',
  'observacao': 'Variáveis ligadas, predicado recebido e argumento ainda livre durante a aplicação do '
                'quantificador do objeto Não se contabiliza como prova de um resultado matemático.',
  'testemunhas': {'lean': [], 'py': [], 'wl': []},
  'pendencias': {'lean': '', 'py': '', 'wl': ''}},
 {'ids': ['c03.e0243'],
  'expressoes': {'c03.e0243': 'y'},
  'proposicao': 'Variáveis ligadas, predicado recebido e argumento ainda livre durante a aplicação do '
                'quantificador do objeto A expressão desta ocorrência é y.',
  'hipoteses': ['As convenções e o domínio são os explicitados na prosa adjacente.'],
  'alcance': 'notacao',
  'observacao': 'Variáveis ligadas, predicado recebido e argumento ainda livre durante a aplicação do '
                'quantificador do objeto Não se contabiliza como prova de um resultado matemático.',
  'testemunhas': {'lean': [], 'py': [], 'wl': []},
  'pendencias': {'lean': '', 'py': '', 'wl': ''}},
 {'ids': ['c03.e0245'],
  'expressoes': {'c03.e0245': 'y'},
  'proposicao': 'Variáveis ligadas, predicado recebido e argumento ainda livre durante a aplicação do '
                'quantificador do objeto A expressão desta ocorrência é y.',
  'hipoteses': ['As convenções e o domínio são os explicitados na prosa adjacente.'],
  'alcance': 'notacao',
  'observacao': 'Variáveis ligadas, predicado recebido e argumento ainda livre durante a aplicação do '
                'quantificador do objeto Não se contabiliza como prova de um resultado matemático.',
  'testemunhas': {'lean': [], 'py': [], 'wl': []},
  'pendencias': {'lean': '', 'py': '', 'wl': ''}},
 {'ids': ['c03.e0246'],
  'expressoes': {'c03.e0246': 'z'},
  'proposicao': 'Variáveis ligadas, predicado recebido e argumento ainda livre durante a aplicação do '
                'quantificador do objeto A expressão desta ocorrência é z.',
  'hipoteses': ['As convenções e o domínio são os explicitados na prosa adjacente.'],
  'alcance': 'notacao',
  'observacao': 'Variáveis ligadas, predicado recebido e argumento ainda livre durante a aplicação do '
                'quantificador do objeto Não se contabiliza como prova de um resultado matemático.',
  'testemunhas': {'lean': [], 'py': [], 'wl': []},
  'pendencias': {'lean': '', 'py': '', 'wl': ''}},
 {'ids': ['c03.e0247'],
  'expressoes': {'c03.e0247': 'x'},
  'proposicao': 'Variáveis ligadas, predicado recebido e argumento ainda livre durante a aplicação do '
                'quantificador do objeto A expressão desta ocorrência é x.',
  'hipoteses': ['As convenções e o domínio são os explicitados na prosa adjacente.'],
  'alcance': 'notacao',
  'observacao': 'Variáveis ligadas, predicado recebido e argumento ainda livre durante a aplicação do '
                'quantificador do objeto Não se contabiliza como prova de um resultado matemático.',
  'testemunhas': {'lean': [], 'py': [], 'wl': []},
  'pendencias': {'lean': '', 'py': '', 'wl': ''}},
 {'ids': ['c03.e0248'],
  'expressoes': {'c03.e0248': 'x'},
  'proposicao': 'Variáveis ligadas, predicado recebido e argumento ainda livre durante a aplicação do '
                'quantificador do objeto A expressão desta ocorrência é x.',
  'hipoteses': ['As convenções e o domínio são os explicitados na prosa adjacente.'],
  'alcance': 'notacao',
  'observacao': 'Variáveis ligadas, predicado recebido e argumento ainda livre durante a aplicação do '
                'quantificador do objeto Não se contabiliza como prova de um resultado matemático.',
  'testemunhas': {'lean': [], 'py': [], 'wl': []},
  'pendencias': {'lean': '', 'py': '', 'wl': ''}},
 {'ids': ['c03.e0249'],
  'expressoes': {'c03.e0249': 'x'},
  'proposicao': 'Variáveis ligadas, predicado recebido e argumento ainda livre durante a aplicação do '
                'quantificador do objeto A expressão desta ocorrência é x.',
  'hipoteses': ['As convenções e o domínio são os explicitados na prosa adjacente.'],
  'alcance': 'notacao',
  'observacao': 'Variáveis ligadas, predicado recebido e argumento ainda livre durante a aplicação do '
                'quantificador do objeto Não se contabiliza como prova de um resultado matemático.',
  'testemunhas': {'lean': [], 'py': [], 'wl': []},
  'pendencias': {'lean': '', 'py': '', 'wl': ''}},
 {'ids': ['c03.e0240'],
  'expressoes': {'c03.e0240': 'F(y)'},
  'proposicao': 'Aplicação de predicado exibida ao explicar substituição de variável; não afirma que o '
                'predicado seja verdadeiro A expressão desta ocorrência é F(y).',
  'hipoteses': ['As convenções e o domínio são os explicitados na prosa adjacente.'],
  'alcance': 'mencao',
  'observacao': 'Aplicação de predicado exibida ao explicar substituição de variável; não afirma que o '
                'predicado seja verdadeiro Não se contabiliza como prova de um resultado matemático.',
  'testemunhas': {'lean': [], 'py': [], 'wl': []},
  'pendencias': {'lean': '', 'py': '', 'wl': ''}},
 {'ids': ['c03.e0244'],
  'expressoes': {'c03.e0244': 'O(x,z)'},
  'proposicao': 'Aplicação de predicado exibida ao explicar substituição de variável; não afirma que o '
                'predicado seja verdadeiro A expressão desta ocorrência é O(x,z).',
  'hipoteses': ['As convenções e o domínio são os explicitados na prosa adjacente.'],
  'alcance': 'mencao',
  'observacao': 'Aplicação de predicado exibida ao explicar substituição de variável; não afirma que o '
                'predicado seja verdadeiro Não se contabiliza como prova de um resultado matemático.',
  'testemunhas': {'lean': [], 'py': [], 'wl': []},
  'pendencias': {'lean': '', 'py': '', 'wl': ''}},
 {'ids': ['c03.e0250'],
  'expressoes': {'c03.e0250': 'V'},
  'proposicao': 'Nomes do verbo, quantificadores e propriedade intermediária durante a composição; os passos '
                'de redução correspondentes são examinados separadamente A expressão desta ocorrência é V.',
  'hipoteses': ['As convenções e o domínio são os explicitados na prosa adjacente.'],
  'alcance': 'notacao',
  'observacao': 'Nomes do verbo, quantificadores e propriedade intermediária durante a composição; os passos '
                'de redução correspondentes são examinados separadamente Não se contabiliza como prova de um '
                'resultado matemático.',
  'testemunhas': {'lean': [], 'py': [], 'wl': []},
  'pendencias': {'lean': '', 'py': '', 'wl': ''}},
 {'ids': ['c03.e0251'],
  'expressoes': {'c03.e0251': 'Q_1'},
  'proposicao': 'Nomes do verbo, quantificadores e propriedade intermediária durante a composição; os passos '
                'de redução correspondentes são examinados separadamente A expressão desta ocorrência é Q_1.',
  'hipoteses': ['As convenções e o domínio são os explicitados na prosa adjacente.'],
  'alcance': 'notacao',
  'observacao': 'Nomes do verbo, quantificadores e propriedade intermediária durante a composição; os passos '
                'de redução correspondentes são examinados separadamente Não se contabiliza como prova de um '
                'resultado matemático.',
  'testemunhas': {'lean': [], 'py': [], 'wl': []},
  'pendencias': {'lean': '', 'py': '', 'wl': ''}},
 {'ids': ['c03.e0252'],
  'expressoes': {'c03.e0252': 'Q_2'},
  'proposicao': 'Nomes do verbo, quantificadores e propriedade intermediária durante a composição; os passos '
                'de redução correspondentes são examinados separadamente A expressão desta ocorrência é Q_2.',
  'hipoteses': ['As convenções e o domínio são os explicitados na prosa adjacente.'],
  'alcance': 'notacao',
  'observacao': 'Nomes do verbo, quantificadores e propriedade intermediária durante a composição; os passos '
                'de redução correspondentes são examinados separadamente Não se contabiliza como prova de um '
                'resultado matemático.',
  'testemunhas': {'lean': [], 'py': [], 'wl': []},
  'pendencias': {'lean': '', 'py': '', 'wl': ''}},
 {'ids': ['c03.e0254'],
  'expressoes': {'c03.e0254': 'Q_T'},
  'proposicao': 'Nomes do verbo, quantificadores e propriedade intermediária durante a composição; os passos '
                'de redução correspondentes são examinados separadamente A expressão desta ocorrência é Q_T.',
  'hipoteses': ['As convenções e o domínio são os explicitados na prosa adjacente.'],
  'alcance': 'notacao',
  'observacao': 'Nomes do verbo, quantificadores e propriedade intermediária durante a composição; os passos '
                'de redução correspondentes são examinados separadamente Não se contabiliza como prova de um '
                'resultado matemático.',
  'testemunhas': {'lean': [], 'py': [], 'wl': []},
  'pendencias': {'lean': '', 'py': '', 'wl': ''}},
 {'ids': ['c03.e0255'],
  'expressoes': {'c03.e0255': 'Q_W'},
  'proposicao': 'Nomes do verbo, quantificadores e propriedade intermediária durante a composição; os passos '
                'de redução correspondentes são examinados separadamente A expressão desta ocorrência é Q_W.',
  'hipoteses': ['As convenções e o domínio são os explicitados na prosa adjacente.'],
  'alcance': 'notacao',
  'observacao': 'Nomes do verbo, quantificadores e propriedade intermediária durante a composição; os passos '
                'de redução correspondentes são examinados separadamente Não se contabiliza como prova de um '
                'resultado matemático.',
  'testemunhas': {'lean': [], 'py': [], 'wl': []},
  'pendencias': {'lean': '', 'py': '', 'wl': ''}},
 {'ids': ['c03.e0257'],
  'expressoes': {'c03.e0257': 'Q_T'},
  'proposicao': 'Nomes do verbo, quantificadores e propriedade intermediária durante a composição; os passos '
                'de redução correspondentes são examinados separadamente A expressão desta ocorrência é Q_T.',
  'hipoteses': ['As convenções e o domínio são os explicitados na prosa adjacente.'],
  'alcance': 'notacao',
  'observacao': 'Nomes do verbo, quantificadores e propriedade intermediária durante a composição; os passos '
                'de redução correspondentes são examinados separadamente Não se contabiliza como prova de um '
                'resultado matemático.',
  'testemunhas': {'lean': [], 'py': [], 'wl': []},
  'pendencias': {'lean': '', 'py': '', 'wl': ''}},
 {'ids': ['c03.e0258'],
  'expressoes': {'c03.e0258': 'Q_W'},
  'proposicao': 'Nomes do verbo, quantificadores e propriedade intermediária durante a composição; os passos '
                'de redução correspondentes são examinados separadamente A expressão desta ocorrência é Q_W.',
  'hipoteses': ['As convenções e o domínio são os explicitados na prosa adjacente.'],
  'alcance': 'notacao',
  'observacao': 'Nomes do verbo, quantificadores e propriedade intermediária durante a composição; os passos '
                'de redução correspondentes são examinados separadamente Não se contabiliza como prova de um '
                'resultado matemático.',
  'testemunhas': {'lean': [], 'py': [], 'wl': []},
  'pendencias': {'lean': '', 'py': '', 'wl': ''}},
 {'ids': ['c03.e0261'],
  'expressoes': {'c03.e0261': 'Q_1'},
  'proposicao': 'Nomes do verbo, quantificadores e propriedade intermediária durante a composição; os passos '
                'de redução correspondentes são examinados separadamente A expressão desta ocorrência é Q_1.',
  'hipoteses': ['As convenções e o domínio são os explicitados na prosa adjacente.'],
  'alcance': 'notacao',
  'observacao': 'Nomes do verbo, quantificadores e propriedade intermediária durante a composição; os passos '
                'de redução correspondentes são examinados separadamente Não se contabiliza como prova de um '
                'resultado matemático.',
  'testemunhas': {'lean': [], 'py': [], 'wl': []},
  'pendencias': {'lean': '', 'py': '', 'wl': ''}},
 {'ids': ['c03.e0262'],
  'expressoes': {'c03.e0262': 'Q_2'},
  'proposicao': 'Nomes do verbo, quantificadores e propriedade intermediária durante a composição; os passos '
                'de redução correspondentes são examinados separadamente A expressão desta ocorrência é Q_2.',
  'hipoteses': ['As convenções e o domínio são os explicitados na prosa adjacente.'],
  'alcance': 'notacao',
  'observacao': 'Nomes do verbo, quantificadores e propriedade intermediária durante a composição; os passos '
                'de redução correspondentes são examinados separadamente Não se contabiliza como prova de um '
                'resultado matemático.',
  'testemunhas': {'lean': [], 'py': [], 'wl': []},
  'pendencias': {'lean': '', 'py': '', 'wl': ''}},
 {'ids': ['c03.e0263'],
  'expressoes': {'c03.e0263': 'Q_T'},
  'proposicao': 'Nomes do verbo, quantificadores e propriedade intermediária durante a composição; os passos '
                'de redução correspondentes são examinados separadamente A expressão desta ocorrência é Q_T.',
  'hipoteses': ['As convenções e o domínio são os explicitados na prosa adjacente.'],
  'alcance': 'notacao',
  'observacao': 'Nomes do verbo, quantificadores e propriedade intermediária durante a composição; os passos '
                'de redução correspondentes são examinados separadamente Não se contabiliza como prova de um '
                'resultado matemático.',
  'testemunhas': {'lean': [], 'py': [], 'wl': []},
  'pendencias': {'lean': '', 'py': '', 'wl': ''}},
 {'ids': ['c03.e0265'],
  'expressoes': {'c03.e0265': 'Q_W'},
  'proposicao': 'Nomes do verbo, quantificadores e propriedade intermediária durante a composição; os passos '
                'de redução correspondentes são examinados separadamente A expressão desta ocorrência é Q_W.',
  'hipoteses': ['As convenções e o domínio são os explicitados na prosa adjacente.'],
  'alcance': 'notacao',
  'observacao': 'Nomes do verbo, quantificadores e propriedade intermediária durante a composição; os passos '
                'de redução correspondentes são examinados separadamente Não se contabiliza como prova de um '
                'resultado matemático.',
  'testemunhas': {'lean': [], 'py': [], 'wl': []},
  'pendencias': {'lean': '', 'py': '', 'wl': ''}},
 {'ids': ['c03.e0267'],
  'expressoes': {'c03.e0267': 'H'},
  'proposicao': 'Nomes do verbo, quantificadores e propriedade intermediária durante a composição; os passos '
                'de redução correspondentes são examinados separadamente A expressão desta ocorrência é H.',
  'hipoteses': ['As convenções e o domínio são os explicitados na prosa adjacente.'],
  'alcance': 'notacao',
  'observacao': 'Nomes do verbo, quantificadores e propriedade intermediária durante a composição; os passos '
                'de redução correspondentes são examinados separadamente Não se contabiliza como prova de um '
                'resultado matemático.',
  'testemunhas': {'lean': [], 'py': [], 'wl': []},
  'pendencias': {'lean': '', 'py': '', 'wl': ''}},
 {'ids': ['c03.e0268'],
  'expressoes': {'c03.e0268': 'Q_W'},
  'proposicao': 'Nomes do verbo, quantificadores e propriedade intermediária durante a composição; os passos '
                'de redução correspondentes são examinados separadamente A expressão desta ocorrência é Q_W.',
  'hipoteses': ['As convenções e o domínio são os explicitados na prosa adjacente.'],
  'alcance': 'notacao',
  'observacao': 'Nomes do verbo, quantificadores e propriedade intermediária durante a composição; os passos '
                'de redução correspondentes são examinados separadamente Não se contabiliza como prova de um '
                'resultado matemático.',
  'testemunhas': {'lean': [], 'py': [], 'wl': []},
  'pendencias': {'lean': '', 'py': '', 'wl': ''}},
 {'ids': ['c03.e0269'],
  'expressoes': {'c03.e0269': 'H'},
  'proposicao': 'Nomes do verbo, quantificadores e propriedade intermediária durante a composição; os passos '
                'de redução correspondentes são examinados separadamente A expressão desta ocorrência é H.',
  'hipoteses': ['As convenções e o domínio são os explicitados na prosa adjacente.'],
  'alcance': 'notacao',
  'observacao': 'Nomes do verbo, quantificadores e propriedade intermediária durante a composição; os passos '
                'de redução correspondentes são examinados separadamente Não se contabiliza como prova de um '
                'resultado matemático.',
  'testemunhas': {'lean': [], 'py': [], 'wl': []},
  'pendencias': {'lean': '', 'py': '', 'wl': ''}},
 {'ids': ['c03.e0271'],
  'expressoes': {'c03.e0271': 'G'},
  'proposicao': 'Nomes do verbo, quantificadores e propriedade intermediária durante a composição; os passos '
                'de redução correspondentes são examinados separadamente A expressão desta ocorrência é G.',
  'hipoteses': ['As convenções e o domínio são os explicitados na prosa adjacente.'],
  'alcance': 'notacao',
  'observacao': 'Nomes do verbo, quantificadores e propriedade intermediária durante a composição; os passos '
                'de redução correspondentes são examinados separadamente Não se contabiliza como prova de um '
                'resultado matemático.',
  'testemunhas': {'lean': [], 'py': [], 'wl': []},
  'pendencias': {'lean': '', 'py': '', 'wl': ''}},
 {'ids': ['c03.e0272'],
  'expressoes': {'c03.e0272': 'H'},
  'proposicao': 'Nomes do verbo, quantificadores e propriedade intermediária durante a composição; os passos '
                'de redução correspondentes são examinados separadamente A expressão desta ocorrência é H.',
  'hipoteses': ['As convenções e o domínio são os explicitados na prosa adjacente.'],
  'alcance': 'notacao',
  'observacao': 'Nomes do verbo, quantificadores e propriedade intermediária durante a composição; os passos '
                'de redução correspondentes são examinados separadamente Não se contabiliza como prova de um '
                'resultado matemático.',
  'testemunhas': {'lean': [], 'py': [], 'wl': []},
  'pendencias': {'lean': '', 'py': '', 'wl': ''}},
 {'ids': ['c03.e0274'],
  'expressoes': {'c03.e0274': 'z'},
  'proposicao': 'Nomes do verbo, quantificadores e propriedade intermediária durante a composição; os passos '
                'de redução correspondentes são examinados separadamente A expressão desta ocorrência é z.',
  'hipoteses': ['As convenções e o domínio são os explicitados na prosa adjacente.'],
  'alcance': 'notacao',
  'observacao': 'Nomes do verbo, quantificadores e propriedade intermediária durante a composição; os passos '
                'de redução correspondentes são examinados separadamente Não se contabiliza como prova de um '
                'resultado matemático.',
  'testemunhas': {'lean': [], 'py': [], 'wl': []},
  'pendencias': {'lean': '', 'py': '', 'wl': ''}},
 {'ids': ['c03.e0275'],
  'expressoes': {'c03.e0275': 'x'},
  'proposicao': 'Nomes do verbo, quantificadores e propriedade intermediária durante a composição; os passos '
                'de redução correspondentes são examinados separadamente A expressão desta ocorrência é x.',
  'hipoteses': ['As convenções e o domínio são os explicitados na prosa adjacente.'],
  'alcance': 'notacao',
  'observacao': 'Nomes do verbo, quantificadores e propriedade intermediária durante a composição; os passos '
                'de redução correspondentes são examinados separadamente Não se contabiliza como prova de um '
                'resultado matemático.',
  'testemunhas': {'lean': [], 'py': [], 'wl': []},
  'pendencias': {'lean': '', 'py': '', 'wl': ''}},
 {'ids': ['c03.e0276'],
  'expressoes': {'c03.e0276': 'W'},
  'proposicao': 'Nomes do verbo, quantificadores e propriedade intermediária durante a composição; os passos '
                'de redução correspondentes são examinados separadamente A expressão desta ocorrência é W.',
  'hipoteses': ['As convenções e o domínio são os explicitados na prosa adjacente.'],
  'alcance': 'notacao',
  'observacao': 'Nomes do verbo, quantificadores e propriedade intermediária durante a composição; os passos '
                'de redução correspondentes são examinados separadamente Não se contabiliza como prova de um '
                'resultado matemático.',
  'testemunhas': {'lean': [], 'py': [], 'wl': []},
  'pendencias': {'lean': '', 'py': '', 'wl': ''}},
 {'ids': ['c03.e0277'],
  'expressoes': {'c03.e0277': 'T'},
  'proposicao': 'Nomes do verbo, quantificadores e propriedade intermediária durante a composição; os passos '
                'de redução correspondentes são examinados separadamente A expressão desta ocorrência é T.',
  'hipoteses': ['As convenções e o domínio são os explicitados na prosa adjacente.'],
  'alcance': 'notacao',
  'observacao': 'Nomes do verbo, quantificadores e propriedade intermediária durante a composição; os passos '
                'de redução correspondentes são examinados separadamente Não se contabiliza como prova de um '
                'resultado matemático.',
  'testemunhas': {'lean': [], 'py': [], 'wl': []},
  'pendencias': {'lean': '', 'py': '', 'wl': ''}},
 {'ids': ['c03.e0278'],
  'expressoes': {'c03.e0278': 'O'},
  'proposicao': 'Nomes do verbo, quantificadores e propriedade intermediária durante a composição; os passos '
                'de redução correspondentes são examinados separadamente A expressão desta ocorrência é O.',
  'hipoteses': ['As convenções e o domínio são os explicitados na prosa adjacente.'],
  'alcance': 'notacao',
  'observacao': 'Nomes do verbo, quantificadores e propriedade intermediária durante a composição; os passos '
                'de redução correspondentes são examinados separadamente Não se contabiliza como prova de um '
                'resultado matemático.',
  'testemunhas': {'lean': [], 'py': [], 'wl': []},
  'pendencias': {'lean': '', 'py': '', 'wl': ''}},
 {'ids': ['c03.e0273'],
  'expressoes': {'c03.e0273': 'H(x)'},
  'proposicao': 'Aplicação H(x) identificada na etapa de substituir a entrada da propriedade já definida; a '
                'redução completa está em c03.e0270 A expressão desta ocorrência é H(x).',
  'hipoteses': ['As convenções e o domínio são os explicitados na prosa adjacente.'],
  'alcance': 'mencao',
  'observacao': 'Aplicação H(x) identificada na etapa de substituir a entrada da propriedade já definida; a '
                'redução completa está em c03.e0270 Não se contabiliza como prova de um resultado '
                'matemático.',
  'testemunhas': {'lean': [], 'py': [], 'wl': []},
  'pendencias': {'lean': '', 'py': '', 'wl': ''}},
 {'ids': ['c03.e0282'],
  'expressoes': {'c03.e0282': 'E_s'},
  'proposicao': 'Predicados, universo ou conjuntos retomados ao explicar restrição, inclusão e importação '
                'existencial; os nomes não são afirmações de existência A expressão desta ocorrência é E_s.',
  'hipoteses': ['As convenções e o domínio são os explicitados na prosa adjacente.'],
  'alcance': 'notacao',
  'observacao': 'Predicados, universo ou conjuntos retomados ao explicar restrição, inclusão e importação '
                'existencial; os nomes não são afirmações de existência Não se contabiliza como prova de um '
                'resultado matemático.',
  'testemunhas': {'lean': [], 'py': [], 'wl': []},
  'pendencias': {'lean': '', 'py': '', 'wl': ''}},
 {'ids': ['c03.e0283'],
  'expressoes': {'c03.e0283': 'T_r'},
  'proposicao': 'Predicados, universo ou conjuntos retomados ao explicar restrição, inclusão e importação '
                'existencial; os nomes não são afirmações de existência A expressão desta ocorrência é T_r.',
  'hipoteses': ['As convenções e o domínio são os explicitados na prosa adjacente.'],
  'alcance': 'notacao',
  'observacao': 'Predicados, universo ou conjuntos retomados ao explicar restrição, inclusão e importação '
                'existencial; os nomes não são afirmações de existência Não se contabiliza como prova de um '
                'resultado matemático.',
  'testemunhas': {'lean': [], 'py': [], 'wl': []},
  'pendencias': {'lean': '', 'py': '', 'wl': ''}},
 {'ids': ['c03.e0284'],
  'expressoes': {'c03.e0284': 'E'},
  'proposicao': 'Predicados, universo ou conjuntos retomados ao explicar restrição, inclusão e importação '
                'existencial; os nomes não são afirmações de existência A expressão desta ocorrência é E.',
  'hipoteses': ['As convenções e o domínio são os explicitados na prosa adjacente.'],
  'alcance': 'notacao',
  'observacao': 'Predicados, universo ou conjuntos retomados ao explicar restrição, inclusão e importação '
                'existencial; os nomes não são afirmações de existência Não se contabiliza como prova de um '
                'resultado matemático.',
  'testemunhas': {'lean': [], 'py': [], 'wl': []},
  'pendencias': {'lean': '', 'py': '', 'wl': ''}},
 {'ids': ['c03.e0289'],
  'expressoes': {'c03.e0289': 'A'},
  'proposicao': 'Predicados, universo ou conjuntos retomados ao explicar restrição, inclusão e importação '
                'existencial; os nomes não são afirmações de existência A expressão desta ocorrência é A.',
  'hipoteses': ['As convenções e o domínio são os explicitados na prosa adjacente.'],
  'alcance': 'notacao',
  'observacao': 'Predicados, universo ou conjuntos retomados ao explicar restrição, inclusão e importação '
                'existencial; os nomes não são afirmações de existência Não se contabiliza como prova de um '
                'resultado matemático.',
  'testemunhas': {'lean': [], 'py': [], 'wl': []},
  'pendencias': {'lean': '', 'py': '', 'wl': ''}},
 {'ids': ['c03.e0290'],
  'expressoes': {'c03.e0290': 'B'},
  'proposicao': 'Predicados, universo ou conjuntos retomados ao explicar restrição, inclusão e importação '
                'existencial; os nomes não são afirmações de existência A expressão desta ocorrência é B.',
  'hipoteses': ['As convenções e o domínio são os explicitados na prosa adjacente.'],
  'alcance': 'notacao',
  'observacao': 'Predicados, universo ou conjuntos retomados ao explicar restrição, inclusão e importação '
                'existencial; os nomes não são afirmações de existência Não se contabiliza como prova de um '
                'resultado matemático.',
  'testemunhas': {'lean': [], 'py': [], 'wl': []},
  'pendencias': {'lean': '', 'py': '', 'wl': ''}},
 {'ids': ['c03.e0296'],
  'expressoes': {'c03.e0296': 'F,G,H'},
  'proposicao': 'Predicados, universo ou conjuntos retomados ao explicar restrição, inclusão e importação '
                'existencial; os nomes não são afirmações de existência A expressão desta ocorrência é '
                'F,G,H.',
  'hipoteses': ['As convenções e o domínio são os explicitados na prosa adjacente.'],
  'alcance': 'notacao',
  'observacao': 'Predicados, universo ou conjuntos retomados ao explicar restrição, inclusão e importação '
                'existencial; os nomes não são afirmações de existência Não se contabiliza como prova de um '
                'resultado matemático.',
  'testemunhas': {'lean': [], 'py': [], 'wl': []},
  'pendencias': {'lean': '', 'py': '', 'wl': ''}},
 {'ids': ['c03.e0300'],
  'expressoes': {'c03.e0300': 'G'},
  'proposicao': 'Predicados, universo ou conjuntos retomados ao explicar restrição, inclusão e importação '
                'existencial; os nomes não são afirmações de existência A expressão desta ocorrência é G.',
  'hipoteses': ['As convenções e o domínio são os explicitados na prosa adjacente.'],
  'alcance': 'notacao',
  'observacao': 'Predicados, universo ou conjuntos retomados ao explicar restrição, inclusão e importação '
                'existencial; os nomes não são afirmações de existência Não se contabiliza como prova de um '
                'resultado matemático.',
  'testemunhas': {'lean': [], 'py': [], 'wl': []},
  'pendencias': {'lean': '', 'py': '', 'wl': ''}},
 {'ids': ['c03.e0301'],
  'expressoes': {'c03.e0301': 'H'},
  'proposicao': 'Predicados, universo ou conjuntos retomados ao explicar restrição, inclusão e importação '
                'existencial; os nomes não são afirmações de existência A expressão desta ocorrência é H.',
  'hipoteses': ['As convenções e o domínio são os explicitados na prosa adjacente.'],
  'alcance': 'notacao',
  'observacao': 'Predicados, universo ou conjuntos retomados ao explicar restrição, inclusão e importação '
                'existencial; os nomes não são afirmações de existência Não se contabiliza como prova de um '
                'resultado matemático.',
  'testemunhas': {'lean': [], 'py': [], 'wl': []},
  'pendencias': {'lean': '', 'py': '', 'wl': ''}},
 {'ids': ['c03.e0305'],
  'expressoes': {'c03.e0305': 'A'},
  'proposicao': 'Predicados, universo ou conjuntos retomados ao explicar restrição, inclusão e importação '
                'existencial; os nomes não são afirmações de existência A expressão desta ocorrência é A.',
  'hipoteses': ['As convenções e o domínio são os explicitados na prosa adjacente.'],
  'alcance': 'notacao',
  'observacao': 'Predicados, universo ou conjuntos retomados ao explicar restrição, inclusão e importação '
                'existencial; os nomes não são afirmações de existência Não se contabiliza como prova de um '
                'resultado matemático.',
  'testemunhas': {'lean': [], 'py': [], 'wl': []},
  'pendencias': {'lean': '', 'py': '', 'wl': ''}},
 {'ids': ['c03.e0306'],
  'expressoes': {'c03.e0306': 'A'},
  'proposicao': 'Predicados, universo ou conjuntos retomados ao explicar restrição, inclusão e importação '
                'existencial; os nomes não são afirmações de existência A expressão desta ocorrência é A.',
  'hipoteses': ['As convenções e o domínio são os explicitados na prosa adjacente.'],
  'alcance': 'notacao',
  'observacao': 'Predicados, universo ou conjuntos retomados ao explicar restrição, inclusão e importação '
                'existencial; os nomes não são afirmações de existência Não se contabiliza como prova de um '
                'resultado matemático.',
  'testemunhas': {'lean': [], 'py': [], 'wl': []},
  'pendencias': {'lean': '', 'py': '', 'wl': ''}},
 {'ids': ['c03.e0308'],
  'expressoes': {'c03.e0308': 'A'},
  'proposicao': 'Predicados, universo ou conjuntos retomados ao explicar restrição, inclusão e importação '
                'existencial; os nomes não são afirmações de existência A expressão desta ocorrência é A.',
  'hipoteses': ['As convenções e o domínio são os explicitados na prosa adjacente.'],
  'alcance': 'notacao',
  'observacao': 'Predicados, universo ou conjuntos retomados ao explicar restrição, inclusão e importação '
                'existencial; os nomes não são afirmações de existência Não se contabiliza como prova de um '
                'resultado matemático.',
  'testemunhas': {'lean': [], 'py': [], 'wl': []},
  'pendencias': {'lean': '', 'py': '', 'wl': ''}},
 {'ids': ['c03.e0309'],
  'expressoes': {'c03.e0309': 'M'},
  'proposicao': 'Operador modal, proposição ou entidade da representação de possibilidade e de manage; o '
                'operador e seu conteúdo são mantidos distintos A expressão desta ocorrência é M.',
  'hipoteses': ['As convenções e o domínio são os explicitados na prosa adjacente.'],
  'alcance': 'notacao',
  'observacao': 'Operador modal, proposição ou entidade da representação de possibilidade e de manage; o '
                'operador e seu conteúdo são mantidos distintos Não se contabiliza como prova de um '
                'resultado matemático.',
  'testemunhas': {'lean': [], 'py': [], 'wl': []},
  'pendencias': {'lean': '', 'py': '', 'wl': ''}},
 {'ids': ['c03.e0312'],
  'expressoes': {'c03.e0312': 'C(x)'},
  'proposicao': 'Operador modal, proposição ou entidade da representação de possibilidade e de manage; o '
                'operador e seu conteúdo são mantidos distintos A expressão desta ocorrência é C(x).',
  'hipoteses': ['As convenções e o domínio são os explicitados na prosa adjacente.'],
  'alcance': 'notacao',
  'observacao': 'Operador modal, proposição ou entidade da representação de possibilidade e de manage; o '
                'operador e seu conteúdo são mantidos distintos Não se contabiliza como prova de um '
                'resultado matemático.',
  'testemunhas': {'lean': [], 'py': [], 'wl': []},
  'pendencias': {'lean': '', 'py': '', 'wl': ''}},
 {'ids': ['c03.e0313'],
  'expressoes': {'c03.e0313': 'M'},
  'proposicao': 'Operador modal, proposição ou entidade da representação de possibilidade e de manage; o '
                'operador e seu conteúdo são mantidos distintos A expressão desta ocorrência é M.',
  'hipoteses': ['As convenções e o domínio são os explicitados na prosa adjacente.'],
  'alcance': 'notacao',
  'observacao': 'Operador modal, proposição ou entidade da representação de possibilidade e de manage; o '
                'operador e seu conteúdo são mantidos distintos Não se contabiliza como prova de um '
                'resultado matemático.',
  'testemunhas': {'lean': [], 'py': [], 'wl': []},
  'pendencias': {'lean': '', 'py': '', 'wl': ''}},
 {'ids': ['c03.e0315'],
  'expressoes': {'c03.e0315': 'x'},
  'proposicao': 'Operador modal, proposição ou entidade da representação de possibilidade e de manage; o '
                'operador e seu conteúdo são mantidos distintos A expressão desta ocorrência é x.',
  'hipoteses': ['As convenções e o domínio são os explicitados na prosa adjacente.'],
  'alcance': 'notacao',
  'observacao': 'Operador modal, proposição ou entidade da representação de possibilidade e de manage; o '
                'operador e seu conteúdo são mantidos distintos Não se contabiliza como prova de um '
                'resultado matemático.',
  'testemunhas': {'lean': [], 'py': [], 'wl': []},
  'pendencias': {'lean': '', 'py': '', 'wl': ''}},
 {'ids': ['c03.e0316'],
  'expressoes': {'c03.e0316': 'P'},
  'proposicao': 'Operador modal, proposição ou entidade da representação de possibilidade e de manage; o '
                'operador e seu conteúdo são mantidos distintos A expressão desta ocorrência é P.',
  'hipoteses': ['As convenções e o domínio são os explicitados na prosa adjacente.'],
  'alcance': 'notacao',
  'observacao': 'Operador modal, proposição ou entidade da representação de possibilidade e de manage; o '
                'operador e seu conteúdo são mantidos distintos Não se contabiliza como prova de um '
                'resultado matemático.',
  'testemunhas': {'lean': [], 'py': [], 'wl': []},
  'pendencias': {'lean': '', 'py': '', 'wl': ''}},
 {'ids': ['c03.e0319'],
  'expressoes': {'c03.e0319': 'P'},
  'proposicao': 'Operador modal, proposição ou entidade da representação de possibilidade e de manage; o '
                'operador e seu conteúdo são mantidos distintos A expressão desta ocorrência é P.',
  'hipoteses': ['As convenções e o domínio são os explicitados na prosa adjacente.'],
  'alcance': 'notacao',
  'observacao': 'Operador modal, proposição ou entidade da representação de possibilidade e de manage; o '
                'operador e seu conteúdo são mantidos distintos Não se contabiliza como prova de um '
                'resultado matemático.',
  'testemunhas': {'lean': [], 'py': [], 'wl': []},
  'pendencias': {'lean': '', 'py': '', 'wl': ''}}]
