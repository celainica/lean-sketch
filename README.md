# lean-sketch

A tool that analyze the logic structure of lean codes to extract crucial proof steps. Then it prompts LLMs to generate proof sketches in natural language.

### Current status
- Using *jixia* to build a ELAB tree      
- Using *Paperproof* to build a GOAL tree  

Extracting informations from these two trees.

---

### Example: Extracting Elab Tree for Lagrange Theorem in Group Theory
Level 0 Dependency:
![level-0](./ELAB/elab_examples/lagrange_1.png)

Level 1 Dependency:
![level-1](./ELAB/elab_examples/lagrange_2.png)

Level 2 Dependency:
![level-2](./ELAB/elab_examples/lagrange_3.png)
