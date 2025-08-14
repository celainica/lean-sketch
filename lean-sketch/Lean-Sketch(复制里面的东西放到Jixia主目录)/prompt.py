import os
from openai import OpenAI


messages = []

API_KEY = ""

text_input = ""

def get_response(messages):
    client = OpenAI(
        api_key="sk-49bbdcadc76e42dd8b3b47fffb45c7b6",
        base_url="https://dashscope.aliyuncs.com/compatible-mode/v1",
    )
    completion = client.chat.completions.create(
        model="qwen-plus-latest", 
        extra_body={"enable_thinking": True}, 
        messages=messages,
        stream=True)
    
    reasoning_content = ""  
    answer_content = ""  
    is_answering = False  
    print("\n" + "=" * 20 + "llm thinking..." + "=" * 20 + "\n")

    for chunk in completion: 
        if not chunk.choices:
            print("\nUsage:")
            print(chunk.usage)
            continue

        delta = chunk.choices[0].delta

        if hasattr(delta, "reasoning_content") and delta.reasoning_content is not None:
            if not is_answering:
                print(delta.reasoning_content, end="", flush=True)
            reasoning_content += delta.reasoning_content

        if hasattr(delta, "content") and delta.content:
            if not is_answering:
                is_answering = True
            answer_content += delta.content
    return answer_content



#-----------------------------Lemma Selector-----------------------------

def init_lemma_selector():
    global API_KEY
    with open('./config', 'r', encoding = 'utf-8') as f:
        p = f.read()  
    parameters = p.splitlines()
    API_KEY = parameters[0][8:]
    
    global messages
    messages = [
    {
        "role": "system",
        "content": """
        **Instruction**

Suppose you are both an expert mathematician and an expert in Lean and Mathlib.

1. I will provide you with:

   * A **main theorem** written in Lean.
   * A **common knowledge base** related to the main theorem, consisting of constants in Lean extracted from it.

   Your task is to select *only* the **crucial** theorems and lemmas (no definitions) from the common knowledge base that are essential for **translating** the formal proof structure of the main theorem into natural language.

   * **Main theorem:** written in Lean.
   * **Common knowledge base:** …

2. Output a list of these crucial theorems and lemmas **exactly as they appear** in the common knowledge base, without any edits or rewording. Only show their constant names, with no explanations.

---

**Selection Principles**

1. Select only those theorems or lemmas from the common knowledge base that play a **central role** in proving the main theorem.

2. The selected theorems or lemmas will be restated and proved in detail in the final natural-language translation, so each must be highly relevant and indispensable to the main theorem’s proof. In other words, a chosen theorem or lemma should require a nontrivial mathematical proof — if it is too short, trivial, or merely states a simple property or axiom, it should not be selected. Moreover, before selecting any theorem or lemma, ask yourself: “Does this need to be explicitly explained in the natural-language proof?” If the answer is no, exclude it.

   **Example (Do Not Select):**
   ❌ `mul_comm`:

   ```lean
   @[to_additive] 
   theorem mul_comm : ∀ a b : G, a * b = b * a := CommMagma.mul_comm
   ```

3. Keep the selection concise — typically, a theorem will require **no more than 10 key lemmas/theorems**.

---

**Demonstration**

**Input Format:**

````plaintext
```main theorem
<lean4 code>
```

```common knowledge base
<constants>
```
````

        """,
    }
]
    
def init_definition_selector():
    global messages
    messages = [
    {
        "role": "system",
        "content": """
**Instruction**

Suppose you are both an expert mathematician and an expert in Lean4 (not Lean3!) and Mathlib.

---

1. I will provide you with:

   * A **main theorem** written in Lean.
   * A **common knowledge base** related to the main theorem, consisting of constants in Lean extracted from it.
   * A **lemma base**containing some lemmas of the main theorem.

   Your task is to select definitions from the common knowledge base that are essential for **translating** the formal proof structure of the main theorem into natural language and you must follow the principles below.

---

**Selection Principles for Definitions**

1. Select only **nontrivial or unfamiliar definitions** — do not include basic mathematical concepts that are widely known. e.g. `Nat`, `Int`, `ZMod p`
2. Each selected definition should be necessary for understanding the proof in natural language. If it can be omitted without affecting understanding, exclude it.

---

**Decision Checklist** ✅

When evaluating each constant in the common knowledge base, ask:

* **Step 1:** Is this a definition?
* **Step 2:** If definition —

  * Is it nontrivial or unfamiliar?
  * Is it essential for understanding the proof in NL form?
* **Step 3:** If all answers point to “not essential,” **exclude it**.

---

**Demonstration**

**Input Format:**

````plaintext
```main theorem
<main theorem name>: 
<lean4 code>
```

```common knowledge base
<constant1 name>:
<lean4 code>
<constant2 name>:
<lean4 code>
...
````

```lemmas
<lemma1 name>: 
<lean4 code>
<lemma2 name>: 
<lean4 code>
...
```


**Output Format**
(If there is no crucial definitions, just output "none".)
```text
<constant_name_1>
<constant_name_2>
... ...
```
(These constants are the name of the definitions chosen.)

        """,
    }
] 
    
    

def choose_lemmas_definitions(constant_definitions,main_constant):
    
    init_lemma_selector()
    
    text_input = """
main theorem:
'"""+main_constant+"""':\n'"""+constant_definitions[main_constant]+"""'

common knowledge base:
"""

    for constant in constant_definitions:
        if constant == main_constant : continue
        text_input = text_input + "'" + constant + "':\n'" + constant_definitions[constant]+"'\n\n"
         
    messages.append({"role": "user", "content": text_input})
    assistant_output = get_response(messages)
    messages.append({"role": "assistant", "content": assistant_output})
    print("____________LEMMAS_______________\n"+assistant_output)
    lemmas = assistant_output.splitlines()
    
    
    
    
    init_definition_selector()
    
    new_constant_definitions = {}
    for const in constant_definitions:
        if const not in lemmas:
            new_constant_definitions[const] = constant_definitions[const]
    
    text_input = """
main theorem:
'"""+main_constant+"""':\n'"""+constant_definitions[main_constant]+"""'

common knowledge base:
"""
    for const in new_constant_definitions:
        text_input = text_input + "'" + const + "':\n'" + new_constant_definitions[const] + "'\n\n"
    text_input = text_input + """
    
lemmas:    
"""
    for const in lemmas:
        text_input = text_input + "'" + const + "':\n'" + constant_definitions[const] + "'\n\n"
    
    messages.append({"role": "user", "content": text_input})
    assistant_output = get_response(messages)
    messages.append({"role": "assistant", "content": assistant_output})
    
    print("\n_________DEFINITIONS____________\n",assistant_output)
    definitions = assistant_output.splitlines()
    
    return lemmas, definitions

   

#-----------------------------End of Selector-----------------------------

def init_translate():
    global messages
    messages = [
    {
        "role": "system",
        "content": """
**Instruction**

Suppose you are an expert mathematician and an expert in Lean4 (NOT Lean3!) and Mathlib4.

1. I will provide you with Lean4 code as follows:

   * **Main Theorem**, which is the goal of the entire proof, written in Lean4.
   * **Lemmas**, which are used to prove the main theorem, written in Lean4.
   * **Definitions**, which help in understanding the formal theorem, written in Lean4.

Your task is to translate each line of the formal proof in Lean into its corresponding step in an informal proof. The informal proof steps should clearly express the logical reasoning of the formal proof, written entirely in the language of mathematics without Lean code, using LaTeX, and following the principles outlined below.

2. Then, generate the whole informal proof, including the main theorem, lemmas, and definitions. Use the steps from the previous task, reorganizing the proof structure as necessary, without altering the logical flow, and adhering to the principles outlined below.

3. Although you are completing the two tasks, **only show the whole informal proof** in the final output.

---

**Principles of Informal Proof for Both Tasks**

1. The informal proof should be written in commonly used mathematical notations and formulas in LaTeX as much as possible. Provide detailed setups only if the definition is not commonly accepted.

2. **Avoid backticks** when quoting anything in the natural language translation; **use LaTeX-style** and `$...$` for quotations.

   **Example:**
   ❌ DO NOT use: `Real.log`
   ✅ Use: \$\log\$

3. **Logical Structure:**
   Restate the proof in the natural order of human language, rather than in the order of the formal proof. Do not distort the logic of the proof.

   **Example:**

   > "To prove A, using Lemma 1, it suffices to show B, which is exactly the result of Lemma 2."
   > Should be reformulated as:
   > "From Lemma 2, we get B. Using Lemma 1 and B, we get A."
   > The logic of "B + Theorem 2 implies A; Theorem 1 implies B" remains intact, but the sentence is more natural.

---

**Principles of Informal Proof for Whole Informal Proof**

1. Please focus on the proof steps you translated above:

   * For informal **lemmas**, include only those that are crucial for the main theorem proof (i.e., as dependent lemmas in the natural language proof) and provide their informal proof accroding to informal prood steps. If a lemma is not essential as a dependent part, simply incorporate it into the proof of the main theorem.
   * For informal **definitions**, explain any unfamiliar or specific definitions within the whole informal proof. Definitions should not appear as dependent parts like lemmas; they are simply part of the main theorem proof.
   * For informal **main theorem**, integrate the relevant lemmas and definitions directly into the proof of the main theorem.


2. Follow the textbook-style proof structure outlined below. Number each lemma and do not use any additional headings or subtitles.

**Example**:

> **Theorem:** [State the main theorem.]
>
> ---
>
> **Lemma 1:** [State the first lemma.]
>
> *Proof.* [Provide the proof for Lemma 1.]
>
> ---
>
> **Lemma 2:** [State the second lemma.]
>
> *Proof.* [Provide the proof for Lemma 2.]
>
> ... *(continue with additional lemmas as needed)*
>
> ---
>
> **Proof of Theorem:**
>
> [Begin with any necessary definitions or explanations. Then, present the main proof, referencing the lemmas above as needed to establish the argument.]



**Demonstrations**

**Input Format:**

````plaintext
***main theorem***:
<main theorem>
***lemmas***:
<lemmas>
***definitions***:
<definitions>
````

```

**Output Format:**
<the whole informal proof>

        """,
    }
] 

def fewshot():
    global text_input    
    with open('./fewshot/Cauchy_input.md', 'r', encoding = 'utf-8') as f:
        cauchy_input = f.read()  
    with open('./fewshot/Cauchy_output.md', 'r', encoding = 'utf-8') as f:
        cauchy_output = f.read() 
    with open('./fewshot/CRT_input.md', 'r', encoding = 'utf-8') as f:
        CRT_input = f.read()  
    with open('./fewshot/CRT_output.md', 'r', encoding = 'utf-8') as f:
        CRT_output = f.read() 
    with open('./fewshot/FermatLittle_input.md', 'r', encoding = 'utf-8') as f:
        FermatLittle_input = f.read()  
    with open('./fewshot/FermatLittle_output.md', 'r', encoding = 'utf-8') as f:
        FermatLittle_output = f.read() 
    with open('./fewshot/quadratic_input.md', 'r', encoding = 'utf-8') as f:
        quadratic_input = f.read()  
    with open('./fewshot/quadratic_output.md', 'r', encoding = 'utf-8') as f:
        quadratic_output = f.read() 
    text_input = f"""
Please study the examples below.
[Example 1]
[Input]
{cauchy_input}
[Output]
{cauchy_output}

[Example 2]
[Input]
{CRT_input}
[Output]
{CRT_output}

[Example 3]
[Input]
{FermatLittle_input}
[Output]
{FermatLittle_output}

[Example 4]
[Input]
{quadratic_input}
[Output]
{quadratic_output}

"""



def translate(constant_definitions,main_theorem,lemmas,definitions):
    text_input = ""
    global API_KEY
    with open('./config', 'r', encoding = 'utf-8') as f:
        p = f.read()  
    parameters = p.splitlines()
    API_KEY = parameters[4][8:]
    init_translate()
    fewshot()
    text_input = text_input + """
--------------------------------    
***Please Translate the Following Code According to the Instruction and the Examples:***


***main theorem***:
"""+main_theorem+""":\n\n"""+constant_definitions[main_theorem]+"""
    
***lemmas***:    
"""
    for const in lemmas:
        text_input = text_input + const + ":\n\n" + constant_definitions[const] + "\n\n"    
    text_input = text_input + """

***definitions***:

""" 
    if definitions[0]=="none":
        text_input = text_input + "none"
    else:
        for const in definitions:
            text_input = text_input + const + ":\n\n" + constant_definitions[const] + "\n\n"
    
    messages.append({"role": "user", "content": text_input})
    assistant_output = get_response(messages)
    messages.append({"role": "assistant", "content": assistant_output})
    return assistant_output