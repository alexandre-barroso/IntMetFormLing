# Verificação matemática em três sistemas

Este repositório reúne os arquivos de verificação matemática de *Introdução a Métodos Formais em Linguística*. As pastas `capitulo_01` a `capitulo_09` estão diretamente na raiz. Python 3, Lean 4 e Wolfram Language examinam cálculos, identidades, hipóteses e demonstrações por procedimentos complementares. O rigor resulta da explicitação dos enunciados e das condições de validade, da possibilidade de executar novamente as verificações e do vínculo auditável entre cada resultado e o material que o sustenta.

**Estado desta publicação:** os arquivos preservam a auditoria registrada em 14 de outubro de 2026 em [`execucoes_gerais.py`](execucoes_gerais.py). Esse registro corresponde a uma versão anterior do manuscrito. Alterações editoriais e novas figuras foram incorporadas posteriormente; os vínculos com essa versão posterior não foram recertificados neste repositório. O campo `cobertura_semantica_total` permanece `False`. Portanto, o material oferece evidência matemática verificável dentro de escopos declarados, sem afirmar ausência absoluta de erros ou cobertura integral da versão atual do livro.

## O papel de cada sistema

| Sistema | Procedimentos presentes nos arquivos | O que a verificação estabelece |
| --- | --- | --- |
| Python 3 | Aritmética racional com `Fraction` e SymPy; simplificação simbólica; enumeração de domínios finitos; limites para arredondamentos; verificadores de certificados e de passos de inferência. | Igualdades e desigualdades exatas, identidades sob hipóteses declaradas, resultados exaustivos nos domínios enumerados e aceitação de certificados pelas regras implementadas. Testes numéricos permanecem identificados como testes. |
| Lean 4 e Mathlib | Definições tipadas e termos de prova, incluindo enunciados quantificados sobre funções, matrizes, medidas e espaços de probabilidade. | A conclusão formal decorre das hipóteses explícitas e das dependências utilizadas, segundo o núcleo de Lean. Os arquivos publicados não contêm `sorry`, `admit`, declarações locais de `axiom`, `unsafe` ou `native_decide`. |
| Wolfram Language | Aritmética exata, transformações simbólicas, simplificação com hipóteses, eliminação de quantificadores em casos apropriados e verificadores de certificados. | Uma segunda implementação de cálculos e derivações, com domínios e condições explicitados nos verificadores. A aceitação pelo sistema simbólico é distinguida da verificação de um termo de prova em Lean. |

Uma comparação decimal, por mais precisa que seja, não demonstra uma afirmação sobre todos os números reais. Analogamente, enumerar todos os casos de um conjunto finito não prova automaticamente um enunciado para conjuntos arbitrários. Os manifestos distinguem cálculos exatos, identidades simbólicas, provas gerais, contraexemplos, definições, menções e apoios parciais. A concordância entre três saídas, isoladamente, não basta para transformar uma dessas categorias em outra.

Algumas demonstrações gerais em Python e Wolfram empregam verificadores locais de dedução e fragmentos de provas de `set.mm`, da biblioteca [Metamath](https://github.com/metamath/set.mm). Os dados necessários estão incorporados aos arquivos; os verificadores reconstroem passos, substituições, hipóteses e condições sobre variáveis. A proveniência declarada da base está em `SOURCE`, em [`capitulo_02/riemann_geral.py`](capitulo_02/riemann_geral.py), incluindo o SHA-256 da fonte utilizada. Esses verificadores locais fazem parte da base de confiança: sua correção também precisa ser examinada. Compartilhar um enunciado, uma fonte ou um certificado entre implementações não equivale a três descobertas matemáticas independentes.

## Do enunciado à evidência

[`cobertura.py`](cobertura.py) inventaria ocorrências matemáticas do LaTeX e as relaciona aos manifestos `capitulo_XX/cobertura.py`. Cada vínculo registra o conteúdo, seu contexto, o arquivo de origem, as hipóteses, o alcance da revisão e as testemunhas nos sistemas pertinentes. [`objetos.py`](objetos.py) identifica objetos verificadores e suas dependências; [`aritmetica.py`](aritmetica.py) trata transcrições aritméticas dentro da linguagem que suporta.

Os hashes SHA-256 detectam mudanças em expressões, contextos, arquivos e dependências. Uma alteração pode invalidar um vínculo mesmo quando um teste antigo ainda passa. O hash atesta a identidade do conteúdo comparado; não demonstra sua verdade matemática e não substitui a revisão de sua interpretação. Para um vínculo ser substantivo, o objeto verificado precisa corresponder ao enunciado do livro, com as mesmas hipóteses e condições de validade.

Os controles adversariais procuram rejeitar, entre outros casos, a remoção de hipóteses, a troca da testemunha por um cálculo diferente, a falta de um dos sistemas, a promoção de amostragem numérica a prova geral, denominadores nulos e componentes ausentes ou circulares em figuras compostas. Há 20 controles registrados em `AUTOTESTES`. Esse número descreve o registro existente; não significa que executá-lo apenas como dado refaça os testes.

Entre as demonstrações gerais explicitamente registradas estão a convergência de somas de Riemann, resultados de decomposição em valores singulares e Procrustes, e identidades probabilísticas para momentos e covariâncias. Por exemplo, a prova de convergência conserva condições de continuidade e de partição; os resultados probabilísticos conservam as hipóteses pertinentes de integrabilidade e independência. Esses enunciados podem ser inspecionados diretamente nos arquivos, sem depender de uma descrição em linguagem natural.

## O que a auditoria registrada cobre

O registro em `execucoes_gerais.py` distingue as seguintes categorias:

| Categoria no manuscrito auditado | Quantidade registrada |
| --- | ---: |
| Ocorrências matemáticas inventariadas | 2.888 |
| Ocorrências de resultados com vínculo tríplice integral | 883 |
| Definições ou hipóteses documentadas, sem certificação tríplice integral | 607 |
| Notações ou menções examinadas, sem proposição autônoma | 1.398 |
| Objetos individuais conferidos | 3.742 |

As três categorias de ocorrências somam o inventário. Elas não são intercambiáveis: uma definição ou uma menção não é um teorema demonstrado. O campo de zero lacunas em resultados refere-se ao conjunto e à versão registrados; não autoriza estender essa conclusão a todas as categorias ou ao manuscrito posteriormente alterado. Os 23 registros em `EXECUCOES` documentam execuções específicas das demonstrações gerais que fecharam seis lacunas daquela revisão, não uma execução nova de todos os arquivos.

O PDF auditado é identificado em `PDF_SHA256`. O repositório publica os scripts, não esse PDF, o LaTeX ou os arquivos bibliográficos. Uma auditoria do vínculo com o livro exige acesso à versão correspondente do manuscrito. Ausência de arquivos, divergência de hashes ou um estado de cobertura incompleto devem ser tratados como resultados da auditoria, sem substituição automática dos hashes para obter aprovação.

## Organização

```text
.
├── capitulo_01/ … capitulo_09/
│   ├── *.py
│   ├── *.lean
│   ├── *.wl
│   └── cobertura.py
├── aritmetica.py
├── objetos.py
├── cobertura.py
├── execucoes_gerais.py
├── lakefile.lean
├── lean-toolchain
├── requirements.txt
└── README.md
```

Os nomes dos arquivos refletem seus objetos de estudo. `verificar.py` e `verificar.wl` são verificadores de cada capítulo, mas não executam automaticamente todos os demais arquivos da pasta. Demonstrações complementares e testes adversariais têm seus próprios pontos de entrada. O alvo padrão de `lakefile.lean` inclui os 79 módulos Lean dos capítulos.

## Reprodução

Execute os comandos abaixo na raiz do repositório. O ambiente Python utilizado na preparação desta publicação foi Python 3.12.3, SymPy 1.14.0 e mpmath 1.3.0. Lean e Mathlib estão fixados em `v4.32.2` por `lean-toolchain` e `lakefile.lean`. A versão de Wolfram utilizada foi 15.0.1; é necessária uma instalação funcional de Wolfram Language com `wolframscript` e a licença correspondente.

### Python

```sh
python3 -m venv .venv
. .venv/bin/activate
python -m pip install -r requirements.txt
python capitulo_01/verificar.py
python capitulo_04/svd_geral.py
python capitulo_07/momentos_afins.py
```

Esses comandos exemplificam a execução de verificadores específicos. Nos relatórios que expõem `passed`, o valor esperado é `true`; examine também resultados individuais e erros. Não confunda importar um módulo ou executar um arquivo que apenas declara dados com executar suas demonstrações. Os testes usam `assert` em vários pontos: não execute Python com `-O` nem com `PYTHONOPTIMIZE` habilitado.

### Lean

Com [Elan](https://github.com/leanprover/elan) instalado e `lake` disponível:

```sh
lake update
lake exe cache get
lake build
```

O primeiro comando resolve as dependências fixadas, e o segundo obtém os artefatos da Mathlib. `lake build` deve terminar sem erros de elaboração ou de prova. Um resultado formal permanece condicionado ao enunciado efetivamente escrito, às hipóteses presentes nele e à base de confiança do sistema e de suas bibliotecas.

### Wolfram Language

```sh
wolframscript -file capitulo_01/verificar.wl
wolframscript -file capitulo_04/svd_geral.wl
wolframscript -file capitulo_07/momentos_afins.wl
```

Verifique os campos de aprovação e o código de saída de cada execução. Os arquivos que reconstroem grandes conjuntos de provas podem exigir mais tempo e memória do que os verificadores aritméticos.

### Vínculo com o manuscrito

Os utilitários de cobertura conservam a organização local da auditoria. Para utilizá-los, o checkout deve chamar-se `scripts` e estar ao lado da pasta `latex` da versão pertinente:

```text
diretorio_de_trabalho/
├── scripts/    ← raiz deste repositório
└── latex/      ← manuscrito correspondente, obtido separadamente
    ├── main.tex
    ├── main.pdf
    ├── capitulos/
    └── figures/
```

Dentro de `scripts`, os comandos disponíveis incluem:

```sh
python cobertura.py --inventario
python cobertura.py --pendencias
python cobertura.py --detalhar c02.e0363
python cobertura.py --autoteste
python execucoes_gerais.py
```

`cobertura.py` usa código de saída `1` quando encontra erros e `2` quando a cobertura semântica total permanece falsa, sem erros estruturais. A geração do inventário, isoladamente, não certifica cobertura. `execucoes_gerais.py` compara hashes com o registro existente; não reexecuta Python, Lean e Wolfram. Em um checkout contendo somente este repositório, a auditoria ligada ao manuscrito não pode ser concluída porque `latex` não está incluída. Com uma versão posterior do livro, divergências dos vínculos registrados são esperadas e exigem uma nova revisão.

## Como interpretar o grau de rigor

A combinação de provas verificadas por núcleo, aritmética exata, reconstrução de certificados, checagens simbólicas e controles adversariais oferece evidência mais forte e inspecionável do que a execução isolada de exemplos. Ela permite examinar a derivação, localizar hipóteses e detectar alterações incompatíveis com uma revisão anterior. Essa é a contribuição concreta da checagem tríplice.

A garantia de cada prova é a implicação entre suas hipóteses e sua conclusão formal. Permanecem fora dessa garantia automática a fidelidade da transcrição de fontes, a adequação do modelo ao fenômeno linguístico, a interpretação empírica dos resultados e a correspondência com trechos que tenham sido modificados depois da auditoria. Avaliar esses pontos requer leitura e revisão humanas. Tornar essas fronteiras explícitas é parte do rigor do repositório.
