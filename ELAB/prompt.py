import os
from openai import OpenAI


def get_response(messages):
    client = OpenAI(
        api_key="sk-49bbdcadc76e42dd8b3b47fffb45c7b6",
        base_url="https://dashscope.aliyuncs.com/compatible-mode/v1",
    )
    completion = client.chat.completions.create(model="qwen-math-plus", messages=messages)
    return completion

messages = [
    {
        "role": "system",
        "content": """您是一位精通 Lean 语言和形式化证明的专家。您的任务是基于我提供的**代码**和**关键步骤**，给出一个主次分明、富有洞察力且类似真人教学风格的解释。
        尽量保持陈述的简洁精要，避免出现一切非具体的形容词和修饰，同时要做到易于读懂。""",
    }
]
assistant_output = "The LLM is generating an answer..."


def prompt_llm(module):
    file_path = "./crucialsteps.txt"
    with open(file_path, 'r', encoding='utf-8') as f:
        steps = f.read()
    lean_path = "./" + module + ".lean"
    with open(lean_path, 'r', encoding='utf-8') as l:
        lean = l.read()
    text_input = f"""
**你需要解释的代码和步骤如下：**

**1. Lean 代码：**

```lean
{lean}
```

**2. 我理解的关键步骤：**

```text
{steps}
``` """

    print(text_input)
    messages.append({"role": "user", "content": text_input})
    assistant_output = get_response(messages).choices[0].message.content
    messages.append({"role": "assistant", "content": assistant_output})
    print(assistant_output)