from http import HTTPStatus
import dashscope


def call_with_messages():
    messages = [{"role":"system","content":"# ProofSketch Prompt for Mathlib4 Proofs\n\n## Instruction\n\nSuppose you are an expert mathematician and an expert in Lean and Mathlib.\n\n1. Your task is to translate each line of the formal proof in Lean, provided below, into a corresponding step of informal proof. The informal proof must express the precise logic of the formal proof, written entirely in the language of mathematicians, and must use LaTeX. You will be provided with auxiliary information to improve the translation.\n\n   * The formal theorem, which is the goal of the entire proof. It is written in Lean.\n   `<...>`\n\n2. Then, generate the complete informal proof of the theorem. Utilize the steps of informal proof written in the first task and reorganize the structure of the proof without altering the logic. Ensure that you follow the principles of whole informal proofs when generating the complete informal proof of the theorem.\n\n\n---\n\n## Principles of Informal Proof Steps\n\n1. The informal proof should be written in commonly used mathematical notations and formulas in LaTeX as much as possible. Explain more detailed mathematical setups only if the definition appearing in the statement is not commonly accepted.\n\n2. **Avoid backticks** to quote anything in the natural language translation; **use LaTeX style** and `$...$` for quotations.\n\n   **Example:**\n\n   ❌ DO NOT use: ``Real.log``  \n   ✅ Use: `$\\log$`\n\n`<...>`\n\n---\n\n## Principles of Whole Informal Proofs\n\n1. Restate the proof in the natural order of human language, rather than in the order of the formal proof. Do not distort the logic of the proof.\n\n   **Example:**\n\n   > \"To prove A, using theorem 1, it suffices to show B, which is exactly the result of theorem 2.\"  \n   > should be reformulated as:  \n   > \"From theorem 2, we get B. Using theorem 1 and B, we get A.\"\n\n   The logic of \"B + theorem 2 implies A; theorem 1 implies B\" remains intact, and the sentence is more natural.\n\n2. Focus on key steps that I provided to demonstrate the informal proofs. You should bold those key steps in informal proofs. Can sketch those that are not key steps but still keep the complete logic for all proof.\n\n\n`<...>`\n\n---\n\n## Demonstrations\n\n**Input Format:**\n\n```plaintext\n```lean4\n<lean4 code>\n```\n```key steps\n<text>\n```\n"},
                {"role":"user","content":""}]

    responses = dashscope.Generation.call(
        model="qwen-plus",
        api_key="**************************",
        messages=messages,
        stream=True,
        result_format='message',  # 将返回结果格式设置为 message
        top_p=0.8,
        temperature=0.7,
        enable_search=False,
        enable_thinking=False,
        thinking_budget=4000
    )

    for response in responses:
        if response.status_code == HTTPStatus.OK:
            print(response)
        else:
            print('Request id: %s, Status code: %s, error code: %s, error message: %s' % (
                response.request_id, response.status_code,
                response.code, response.message
            ))


if __name__ == '__main__':
    call_with_messages()