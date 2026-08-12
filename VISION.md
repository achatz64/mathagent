# Math agent

## Context

The purpose of this repo is to provide skills and tools for the analysis of math research by llm agents.

Llm coding tools are very successful in the analysis of code, in particular in finding bugs and improvements. The hope is to transfer these skills in order to check and clarify statements and proofs of math research documents. 

Although by the Curry-Howard correspondence mathematics can be described as a coding challenge, there are practical differences between math and coding llm analysis:    
1. There is no fixed syntax for writing math documents.
2. References management is not industrialized. The coding equivalent would be dependencies management. 

Both points introduce ambiguity, which makes math papers harder to interpret for an llm. In a strict sense the problem of analyzing a math paper is not well-defined since it depends on the choice of an interpretation of the notation.

## Features

Agent skills and tools. 

### Analysis

A normal user can type `\math-analysis mypaper.tex` to obtain a summary of the analysis. Moreover a different version of the paper is generated: `mypaper.ma5`. In contrast to `mypaper.tex` the file `mypaper.ma5` is code: it follows a fixed syntax and dependencies can be uniquely resolved. Note that this does not imply that statements in `mypaper.ma5` are correct. It also does not imply that the ambiguity is gone. For example, we can imagine `import {NaturalNumbers as X, CategorySets as Y} from Basic; X_Y;` to be correct syntax but the meaning of the object `X_Y` is unclear.   

In general, there will be various choices for a language like `ma5` supported, `ma5` was simply the default in the previous example, and `\math-analysis ma6 mypaper.tex` will produce `mypaper.ma6`, which will be code for the language `ma6`.    

On the spectrum of languages, the formal verification languages are on the extreme end: for them, type checking is sufficient to prove correctness of proofs. We start with Lean as `ma1`; it is a well-established, very flexible and llms know it.

### Knowledge base

For each language `ma` the knowledge base (KB) are the dependencies available, meta data, documentation etc. The llm agent needs to find adequate dependencies, tools will help accomplish that:
```
build_X: (KB) -> (tool X)
(agent on analysis) <-> (tool X)
```
Tool X can be a full text or semantic search or anything else we come up with. This will be subject to heavy development to ensure scaling. The start doesn't have to be called, for example Lean has an extensive MathLib library.

Knowledge bases have the following advantage: 
1. New knowledge is available without retraining of llm.
2. Single source of truth, so that different llms can be used. 

Longterm KBs should be used in model training in order to improve analysis capabilities. 

We need a formalism of inclusion of (trusted) analysis outputs into the knowledge base:
```
inclusion: (paper x metadata) -> (KB update).
```

Building the knowledge base is not a one time effort, but must be essentially reproducible. We need the infrastructure to build knowledge bases from a paper pipeline (format and architecture to be determined) in order to try out different agents, models, tools, and `ma` languages. 

See [KB.md](KB.md) for the current Lean-first knowledge-base plan.
