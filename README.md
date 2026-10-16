# Verificação matemática de Introdução a Métodos Formais em Linguística

Este projeto reúne as demonstrações e os verificadores matemáticos de *Introdução a Métodos Formais em Linguística*, organizados em nove capítulos para exame. É um projeto autônomo de verificação: seus programas contêm os enunciados, as hipóteses, os dados e os certificados necessários aos cálculos. Basta este repositório, com os ambientes de linguagem e as bibliotecas declaradas instalados, para executar as verificações.

A revisão percorreu toda a exposição matemática, incluindo resultados apresentados em prosa, condições de validade, cálculos intermediários e dados numéricos das ilustrações. Todas as **958 ocorrências de resultados matemáticos** identificadas em um inventário de 2.997 ocorrências receberam verificação integral em **Lean, Python e Wolfram**. As 54 ocorrências que anteriormente tinham controles parciais em pelo menos um desses sistemas foram completadas com demonstrações gerais e aplicações que preservam as condições de validade. São ocorrências de resultados, não 958 teoremas distintos: uma demonstração pode fundamentar várias aplicações. As outras 606 ocorrências correspondem a definições ou condições, e 1.433 a notação ou menções examinadas. Definições, hipóteses empíricas e nomes de conceitos não são contados como teoremas demonstrados.

O conjunto contém **418 programas matemáticos: 157 Python, 102 Lean e 159 Wolfram**, executados nos ambientes nativos. A revisão de correspondência e as leituras adversariais sustentam a avaliação de abrangência; a execução em cada ambiente nativo reproduz as provas e os cálculos explícitos. Uma execução bem-sucedida, isoladamente,  não demonstra que qualquer texto externo esteja livre de erros.

## Alcance da checagem em três sistemas

| Sistema | O que verifica | Como interpretar o resultado |
|---|---|---|
| Lean 4 e Mathlib | Enunciados tipados, provas gerais, domínios e cálculos exatos. | O núcleo confere um termo de prova de que a conclusão decorre das hipóteses declaradas. |
| Python 3, SymPy e mpmath | Aritmética racional, identidades simbólicas, enumerações finitas, limites de aproximação e certificados de dedução. | O alcance depende do procedimento concreto: uma enumeração finita não é uma prova sobre todos os reais. |
| Wolfram Language | Cálculos exatos, simplificação sob hipóteses, eliminação de quantificadores e verificação de certificados. | Fornece uma implementação adicional; um resultado simbólico não é identificado com uma prova conferida pelo núcleo de Lean. |

A combinação reduz o risco de erros de cálculo, de implementação e de domínio. Os três sistemas verificam integralmente os resultados catalogados, mas isso não significa três descobertas ou demonstrações concebidas de maneira independente. Python e Wolfram podem conferir o mesmo certificado por implementações distintas. Provas sobre funções arbitrárias, medidas, dimensões variáveis e sequências de comprimento não limitado usam regras gerais, quantificação ou indução; a enumeração de alguns exemplos não substitui essas provas.

Os arquivos conservam as hipóteses necessárias: denominadores positivos ou não nulos, distribuições normalizadas, condições de integrabilidade e diferenciabilidade, compatibilidade de dimensões e independência quando exigida. Probabilidade zero é tratada sem impor positividade estrita a toda a distribuição. Atualizações estritamente crescentes ou decrescentes distinguem vetores nulos de não nulos. Contramodelos exatos verificam limites das afirmações, como correlação zero com dependência não linear e falha da desigualdade triangular para distâncias ao quadrado.

## Demonstrações gerais e aproximações certificadas

A extensão da cobertura inclui indução sobre somas e listas finitas de comprimento arbitrário, preservação e inversão de ordem, potências racionais, monotonicidade de exponenciais e logaritmos, regras de derivação e teoremas de integração. As provas analíticas explicitam continuidade, diferenciabilidade, integrabilidade e domínio. A aditividade para eventos disjuntos admite probabilidades nulas; a normalização de perfis distingue o fator zero dos fatores não nulos.

Para informação mútua e divergência, a derivação trata separadamente suporte e massas nulas, deriva a desigualdade logarítmica e verifica as identidades de entropia e de canal. Para vetores, médias, ordenação de candidatos e redes, há provas para dimensões e sequências finitas arbitrárias, incluindo invariância de CBOW sob permutações, condições da correlação, ordem lexicográfica e médias de avaliação.

As áreas e somas da densidade lognormal combinam a mudança de variável demonstrada, continuidade e convergência com intervalos racionais exatos. Os limites de erro vêm de séries com resto limitado, integração de polinômios e desigualdades integrais. O arredondamento apresentado só é aceito quando todo o intervalo certificado fica dentro da faixa correspondente. A concordância de duas aproximações em ponto flutuante não é usada como prova de precisão.

Cada interface entre uma prova analítica e um cálculo confere o enunciado e as hipóteses esperados. As verificações adversariais rejeitam alterações de fórmulas, hipóteses, objetos ou dependências. A conferência dos resultados numéricos é acompanhada da revisão da ligação entre a fórmula geral e sua aplicação.

## Conteúdo por capítulo

| Pasta | Principais objetos verificados |
|---|---|
| `capitulo_01` | Contagens, frequências, proporções, denominadores, razões e comparações de associações. |
| `capitulo_02` | Funções, escalas, logaritmos, monotonicidade, derivadas, regra da cadeia, integrais, somas de Riemann e probabilidades de eventos disjuntos. |
| `capitulo_03` | Conjuntos, relações, cardinalidade, sobreposição, lógica e consequências de definições formais. |
| `capitulo_04` | Árvores e grafos, percursos e matrizes de adjacência, vetores, cosseno, decomposição em valores singulares, aproximação matricial e alinhamento de espaços. |
| `capitulo_05` | Médias, variância, dispersão, normalização, padronização, tabelas de contingência e estatísticas de associação. |
| `capitulo_06` | Probabilidade condicional, Bayes, binomial, entropia, informação mútua, densidade lognormal e equivalência entre distorção e informação em um canal bayesiano. |
| `capitulo_07` | Reamostragem, incerteza, momentos, regressão, covariância, correlação e suas condições de definição. |
| `capitulo_08` | Autômatos e transdutores, segmentação, distância de edição, OT e gramática harmônica, redes neurais, perdas, gradientes, SGNS, CBOW, atenção, projeções e valores de Shapley. |
| `capitulo_09` | Precisão, revocação, F1, médias de avaliação, regiões de conjuntos e limites de identificação de resultados. |

Dentro de cada pasta há arquivos `.lean`, `.py` e `.wl`. Os dados e certificados são incorporados ao código. Não há comentários nem docstrings nos programas. Os enunciados Lean e seus parâmetros são a especificação formal inspecionável; os identificadores dos controles facilitam a localização das verificações correspondentes.

## Preparar os ambientes

Use Python 3 e crie um ambiente com as dependências fixadas:

```sh
python3 -m venv .venv
. .venv/bin/activate
python -m pip install -r requirements.txt
```

As versões utilizadas foram Python 3.12.3, SymPy 1.14.0 e mpmath 1.3.0. Mantenha as asserções habilitadas: o executor recusa `python -O` e `PYTHONOPTIMIZE`.

Para Lean, instale Elan, com `lean` e `lake` disponíveis. O projeto fixa Lean 4.32.2 e Mathlib `v4.32.2`. Prepare as bibliotecas:

```sh
lake update
lake exe cache get
```

Instale também Wolfram Language com `wolframscript` disponível e licença funcional. As verificações foram executadas no kernel nativo Wolfram 15.0.1. Uma execução em um substituto não é evidência equivalente de execução nesse sistema.

## Inspecionar enunciados e controles

O índice é produzido a partir dos próprios programas:

```sh
python inventario.py --resumo
python inventario.py --capitulo 6 --saida indice_capitulo_06.json
python inventario.py --detalhar Chapter06Closure.ColorModel.expected_KL_equals_information_loss
```

O índice informa arquivos, linhas, dependências locais, assinaturas Lean e contexto lexical das declarações. Também lista identificadores de controles Python e Wolfram. Identificadores construídos em laços são marcados como dinâmicos: sua expansão efetiva aparece nos relatórios de execução. Certificados verificados por comparação seguida de exceção podem aparecer apenas nos relatórios de execução, sem um identificador `check` no índice lexical. O índice facilita a inspeção; não executa provas nem decide por si só a correção de uma tradução matemática.

Ao examinar um resultado, leia primeiro os parâmetros e as hipóteses do enunciado, depois a conclusão. Confira se o domínio é finito ou arbitrário, se a igualdade é exata ou aproximada e se há condições de validade. Em Python e Wolfram, examine também o procedimento usado: uma identidade simbólica, uma prova por certificado e um teste numérico têm alcances diferentes.

## Executar por capítulo ou em conjunto

Execute os comandos na raiz do repositório. Para o capítulo 6:

```sh
python executar.py --sistema python --capitulo 6 --saida .execucoes --jobs 2
python executar.py --sistema wolfram --capitulo 6 --saida .execucoes --jobs 1
python executar.py --sistema lean --capitulo 6 --dependencias-lean .lake/packages --saida .execucoes
```

Para verificar todos os capítulos, omita `--capitulo`:

```sh
python executar.py --sistema python --saida .execucoes --jobs 2
python executar.py --sistema wolfram --saida .execucoes --jobs 1
python executar.py --sistema lean --dependencias-lean .lake/packages --saida .execucoes
```

Para examinar um programa individual, use `--arquivo`:

```sh
python executar.py --sistema lean --arquivo capitulo_06/Fechamento.lean --dependencias-lean .lake/packages --saida .execucoes
python executar.py --sistema python --arquivo capitulo_06/fechamento.py --saida .execucoes
python executar.py --sistema wolfram --arquivo capitulo_06/fechamento.wl --saida .execucoes
```

O executor compila os módulos Lean em ordem de dependência, incluindo os módulos locais importados, e produz novos objetos compilados em cada chamada. Todos os módulos Lean também são alvos de `lake build`. Uma chamada parcial serve à inspeção ou ao diagnóstico; a verificação do conjunto exige executar todos os programas.

Cada chamada cria um diretório próprio com logs e registros JSON. O executor verifica códigos de saída, relatórios internos, estabilidade dos programas durante a execução e integridade das dependências. Rejeita falhas declaradas mesmo quando o processo retorna código zero. Em Lean, rejeita admissões, axiomas locais e diagnósticos de provas incompletas. As dependências locais devem permanecer dentro do projeto.

O tempo máximo padrão é de 7.200 segundos por programa e pode ser ajustado com `--timeout`. Certificados grandes e provas simbólicas podem exigir tempo e memória consideráveis.

## Validar os registros

Depois das execuções completas:

```sh
python validar_execucoes.py .execucoes --saida .execucoes/validacao.json
python validar_execucoes.py --autoteste
```

Os resultados esperados são `todos_validos: true`, `execucoes_validas: 418` e `compativeis_com_limitacoes: 0`. O validador confronta os registros com os programas atuais, seus imports transitivos, os logs e os objetos Lean produzidos. Um programa alterado precisa de nova execução compatível. Os hashes usados nesse processo identificam exclusivamente código, dependências e produtos de execução.

Os 33 autotestes da infraestrutura incluem rejeição de relatórios vazios, falhas internas, alterações de dependências, objetos Lean ausentes ou indevidos, imports entre capítulos, precedência de caminhos locais e dependências que escapem da raiz do projeto. Validar registros não reexecuta as demonstrações; essas duas operações permanecem distintas.

## Base de confiança

O rigor decorre das provas gerais conferidas, dos cálculos exatos, das aproximações com limites explícitos e da revisão independente dos enunciados e hipóteses. As provas Lean não usam `sorry`, `admit`, axiomas locais ou mecanismos inseguros para substituir demonstrações. Os outros verificadores distinguem as regras e definições de sua base lógica dos teoremas derivados; as conclusões a demonstrar não são admitidas como hipóteses.

Lean e Mathlib, os sistemas simbólicos, os ambientes de execução e os verificadores locais pertencem à base de confiança. Alguns verificadores Python e Wolfram reconstroem certificados de dedução natural ou fragmentos da base Metamath `set.mm`; os certificados, a identificação da fonte e os dados necessários estão incorporados ao código. Não é necessário baixar essa base para executar esses verificadores. As traduções entre as interfaces analíticas e os verificadores tipados também pertencem à base de confiança: suas fórmulas e hipóteses foram conferidas na revisão. Componentes ou certificados compartilhados entre sistemas constituem dependências comuns e devem ser considerados na avaliação da independência das checagens.

A garantia formal de cada teorema é que sua conclusão decorre das hipóteses expressas. Ela não transforma hipóteses empíricas em fatos demonstrados, não decide a adequação de um modelo a um fenômeno linguístico e não constitui uma garantia absoluta de infalibilidade. O projeto oferece evidência matemática reproduzível e examinável, com o alcance de cada procedimento preservado.
