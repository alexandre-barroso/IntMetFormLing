# Verificação matemática em três sistemas

Este repositório reúne os arquivos de verificação matemática de *Introdução a Métodos Formais em Linguística*. As pastas `capitulo_01` a `capitulo_09` estão diretamente na raiz. Python 3, Lean 4 e Wolfram Language examinam cálculos, identidades, hipóteses e demonstrações por procedimentos complementares. O rigor resulta da explicitação dos enunciados e das condições de validade, da possibilidade de executar novamente as verificações e do vínculo auditável entre cada resultado e o material que o sustenta.

## O papel de cada sistema

| Sistema | Procedimentos presentes nos arquivos | O que a verificação estabelece |
| --- | --- | --- |
| Python 3 | Aritmética racional com `Fraction` e SymPy; simplificação simbólica; enumeração de domínios finitos; limites para arredondamentos; verificadores de certificados e de passos de inferência. | Igualdades e desigualdades exatas, identidades sob hipóteses declaradas, resultados exaustivos nos domínios enumerados e aceitação de certificados pelas regras implementadas. Testes numéricos permanecem identificados como testes. |
| Lean 4 e Mathlib | Definições tipadas e termos de prova, incluindo enunciados quantificados sobre funções, matrizes, medidas e espaços de probabilidade. | A conclusão formal decorre das hipóteses explícitas e das dependências utilizadas, segundo o núcleo de Lean. Os arquivos publicados não contêm `sorry`, `admit`, declarações locais de `axiom`, `unsafe` ou `native_decide`. |
| Wolfram Language | Aritmética exata, transformações simbólicas, simplificação com hipóteses, eliminação de quantificadores em casos apropriados e verificadores de certificados. | Uma segunda implementação de cálculos e derivações, com domínios e condições explicitados nos verificadores. A aceitação pelo sistema simbólico é distinguida da verificação de um termo de prova em Lean. |

Uma comparação decimal, por mais precisa que seja, não demonstra uma afirmação sobre todos os números reais. Analogamente, enumerar todos os casos de um conjunto finito não prova automaticamente um enunciado para conjuntos arbitrários. Os manifestos distinguem cálculos exatos, identidades simbólicas, provas gerais, contraexemplos, definições, menções e apoios parciais. A concordância entre três saídas, isoladamente, não basta para transformar uma dessas categorias em outra.

Algumas demonstrações gerais em Python e Wolfram empregam verificadores locais de dedução e fragmentos de provas de `set.mm`, da biblioteca [Metamath](https://github.com/metamath/set.mm). Os dados necessários estão incorporados aos arquivos; os verificadores reconstroem passos, substituições, hipóteses e condições sobre variáveis. A proveniência declarada da base está em `SOURCE`, em [`capitulo_02/riemann_geral.py`](capitulo_02/riemann_geral.py), incluindo o SHA-256 da fonte utilizada. Esses verificadores locais fazem parte da base de confiança: sua correção também precisa ser examinada. Compartilhar um enunciado, uma fonte ou um certificado entre implementações não equivale a três descobertas matemáticas independentes.

## O que a auditoria registrada cobre

O registro em `execucoes_gerais.py` distingue as seguintes categorias:

| Categoria no manuscrito auditado | Quantidade registrada |
| --- | ---: |
| Ocorrências matemáticas inventariadas | 2.888 |
| Ocorrências de resultados com vínculo tríplice integral | 883 |
| Definições ou hipóteses documentadas, sem certificação tríplice integral | 607 |
| Notações ou menções examinadas, sem proposição autônoma | 1.398 |
| Objetos individuais conferidos | 3.742 |

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

## Como interpretar o grau de rigor

A combinação de provas verificadas por núcleo, aritmética exata, reconstrução de certificados, checagens simbólicas e controles adversariais oferece evidência mais forte e inspecionável do que a execução isolada de exemplos. Ela permite examinar a derivação, localizar hipóteses e detectar alterações incompatíveis com uma revisão anterior. Essa é a contribuição concreta da checagem tríplice.
