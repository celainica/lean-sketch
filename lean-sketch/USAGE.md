# **Usage Guide**

## **1. Environment Setup**

### 1.1 Configure Lean4 and Jixia

1. Install **Lean4** by following the official instructions: [https://lean-lang.org/install/](https://lean-lang.org/install/).

2. Configure the modified **Jixia** included in our repository:
   [https://github.com/pelicanhere/jixia/tree/symbol](https://github.com/pelicanhere/jixia/tree/symbol)

3. **Mathlib dependency:** Lean-Sketch requires **Mathlib**. Before building the modified Jixia, add the following to `lakefile.lean` in the Jixia root directory:

   ```lean
   require mathlib from git "https://github.com/leanprover-community/mathlib4.git" @ s!"v{Lean.versionStringCore}"
   ```

   Then run the following in the Jixia root directory to update the configuration:

   ```bash
   lake update Mathlib
   ```

---

## **2. Using Lean-Sketch**

1. Copy all files from the `Lean-Sketch` folder (included in this package) into the **root directory of Jixia** (the directory containing `lakefile.lean`).

2. Install the **Pyvis** library in your Python environment:

   ```bash
   pip install pyvis
   ```

3. Configure the necessary files:

   * `config` – contains tool settings
   * `whitelist` – specifies allowed files or dependencies

4. Run Lean-Sketch from the Jixia root directory:

   ```bash
   python leansketch.py
   ```

---

## **3. Additional Notes**

* The `level` parameter in the `config` file specifies how many layers of dependencies the tool will retrieve.
* The default value for `level` is **2**.


