This is an explorative first investigation. It has a goal and a primary objective. The primary objective is the valuable output and reaching the goal is simply a disposable but neccessary end step.

Goal: Formalize the mathematical constructions (objects, examples) and statements from `test/GT/GT.tex` in Lean by using as much content from Mathlib as possible. 

Primary objectives: 

1. Learn to use lean-explorer and lean-repl efficiently. There are new tools, but we don't expect bugs. However, there efficient use is not tested. 
2. Efficient means: 
    - you use as few tokens as possible, be lazy, don't think too much
    - you reach your goal fast and with minimal effort
    - you keep your own proofs and constructions (where you need brain power to a minimum)

Permissions: 
1. In drafts you may use gap constructions like sorry or `gap` from `lean/test.lean`
2. You are encouraged to research how other tools and framework handle the task. For example https://github.com/cameronfreer/lean4-skills/ claims to implement skills for formalization, there will be other tools out there. 
3. In general you are allowed to introduce axioms in the following case. Mathematical facts referenced by the paper you attempt to formalize can be stated as axioms if not found in the current formalized corpus (Mathlib currently). In other words, if the paper is using a mathematical fact as dependency, then you are allowed to infer a minimal axiom such that the claimed properties hold.    


## QA

### First round
• I have four questions before starting:

  1. Does /test/GT/GT.tex mean the repository-relative test/GT/GT.tex?
  2. Where should the resulting Lean file(s) live, and should their structure follow the TeX sections?
  3. Is the desired endpoint a compiling draft that may retain sorry/minimal axioms, or should I close every gap that Mathlib can reasonably handle?
  4. Since tool efficiency is the primary objective, do you also want a brief report of search strategy, useful declarations, timings, failures, and lessons
     learned?

──────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────


› 1. yes, come one. 2. in the lean folder of course, i don't care about structure, i need a proof that you formalized everything (we don't have the
  provenance system figure yet and it's not part of this task) 3. every gap closed at end 4. the report should be extensive and very innovative, explore
  methods and pipelines, you may formalize many times to test and benchmark different ideas

  please more questions


### Second round

• I inspected the source: it is 10,254 lines and includes seven main mathematical chapters, exercises, solutions, and an examination. These are the
     build status? This would be a task-local audit artifact, not the future provenance system.

  6. Should alternative experimental formalizations remain under lean/ for reproducibility, or should only the best canonical version remain while
     alternatives are described in the report?
     on the current project?

  8. Should translations preserve the book’s exact hypotheses and notation, or may they use stronger/generalized Mathlib formulations when the book’s
     statement follows immediately?

  9. For algorithms, multiplication tables, and computational examples, do you want executable definitions with verified outputs, or only propositions
     characterizing their mathematical results?

  10. For efficiency benchmarking, should I optimize and report primarily wall-clock time and tool-call counts? Exact internal token accounting may not be
     exposed, so I would use measurable proxies such as prompt/result size and number of retrieved declarations.

──────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────


› 1. let's not do the exercises for now, this follows primary objectives, exercises don't give significant insights for tool usage
  2. only things you can cite, informal claims are not referenceable
  3. yes, results get a wrapper, constructions you may choose, probably opt out first
  4. new axioms allowed because they are audible, i bet you don't need anything for this paper though
  5. do as you like
  6. yes, as many as you like
  7. current tools are limited to mathlib or at least test coverage is limited, so we stick to mathlib by primary objective
  8. the statements must be a faithful translation in terms of generality, the proofs will then involve the more general statements. feel  free to generalize
  and use the more general statements in the proofs.
  9. leave these out for now until we understand the examples better, not clear how rigorous and referanceable these are
  10. efficiency will only increase through experimentation. i want you to find low effort way, high tool call counts is not necessarily bad if this takes
  load of you

  more questions