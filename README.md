# CoEndoYoneda and its Relationship to Purity (`coEndoYoneda-and-purity`)

Formal verification in Lean 4 of **Basic Functional Categories**, **Functional Categories**, the **CoEndoYoneda Isomorphism Theorem**, and its exact equivalence with **computational purity (monad idempotency)** for Kleisli categories, synchronized in terminology and structure with the author's Cubical Agda formalization (`CoEndoYoneda.lagda.md`).

## Provenance & Attribution

- **The CoEndoYoneda Lemma and its proof proper** (the categorical definitions of Basic/Functional Categories and the pointfree equational proof of the CoEndoYoneda isomorphism) were originally conceived and proved by **Luc Duponcheel**.
- **The Lean 4 formalization and the relationship with computational purity** (that a Kleisli category $\mathbf{Kl}(M)$ with canonical identity-on-objects embedding $\mathrm{KFF}$ is a Basic Functional Category if and only if $M$ is an idempotent/pure monad, together with the terminal subsingleton theorem and effect classifications) were proved using **Gemini** (Google DeepMind Antigravity) based upon prompts from the author.

## Main Results

1. **`CoEndoYonedaAndPurity.η_eq_T`**: Derives the terminal unit law $\eta_{\mathrm{FF}(T)} = g(g(\mathrm{tt}^*))$ as a special case of the general parametric law `η_eq`.
2. **`CoEndoYonedaAndPurity.fz_to_τz_commute`**, **`to_from_proof_hom`**, **`from_to_proof'`** (bundled as **`coEndoYonedaIso`**): For any Functional Category $(\mathcal{C}, \mathrm{FF})$, object $Z \in \mathcal{C}$, and endofunctor $\mathrm{EF} : \mathcal{C} \to \mathcal{C}$, establishes the CoEndoYoneda isomorphism
   $$\bigl(\mathrm{CYEF}(\mathrm{FF}, Z) \longrightarrow (\mathrm{EF} \ggg G(\mathrm{FF}))\bigr) \;\simeq\; \bigl(\mathrm{FF}(T) \longrightarrow G(\mathrm{FF})(\mathrm{EF}(Z))\bigr).$$
3. **`CoEndoYonedaAndPurity.ηFFT_is_η_at_FFT`**: Evaluating the forward isomorphism at $\mathrm{EF} = \mathbf{1}_{\mathcal{C}}$ and $Z = \mathrm{FF}(T)$ on $\mathrm{id}_G$ recovers $\eta_{\mathrm{FF}(T)}$.
4. **`CoEndoYonedaAndPurity.set_is_functional_category`**: Proves that `Type u` (`SET`) with $\mathrm{FF} = \mathbf{1}_{\mathrm{Type}\,u}$ is a Functional Category where `η_eq`, `η_eq_T`, and `id_left` hold definitionally by `rfl`.
5. **`CoEndoYonedaAndPurity.idempotent_iff_isPure`**: Equivalence between `Idempotent M` ($\mathrm{mMap}\;\mathrm{mPure} = \mathrm{mPure}$) and `IsPure M` ($\mathrm{mApply}\;(\mathrm{mPure} \circ \mathrm{mPure}) = \mathrm{mPure}$).
6. **`CoEndoYonedaAndPurity.kleisliBasicFunctionalCategory_iff_idempotent`**: For any lawful monad $M$, $(\mathbf{Kl}(M), \mathrm{KFF}(M))$ is a `BasicFunctionalCategory` if and only if $M$ is `Idempotent`.
7. **`CoEndoYonedaAndPurity.isPure_implies_monadicTerminalTypeSubSingleton`**: The Borceux / Lawvere–Manes equational proof that `IsPure M` implies every $mt : M(T)$ equals $\mathrm{pure}(\mathrm{tt}^*)$ (and hence `Subsingleton (M T)`).
8. **Concrete Effect Classifications**:
   - `maybe_not_pure` ($\neg\,\mathrm{IsPure}\;\mathrm{Option}$)
   - `list_not_pure` ($\neg\,\mathrm{IsPure}\;\mathrm{List}$)
   - `read_purity_implies` ($\mathrm{IsPure}(\mathrm{Read}\;R) \to \mathrm{Subsingleton}\;R$)
   - `write_purity_implies` ($\mathrm{IsPure}(\mathrm{Write}\;W) \to \mathrm{Subsingleton}\;W$)
   - `state_purity_implies` ($\mathrm{IsPure}(\mathrm{State}\;S) \to \mathrm{Subsingleton}\;S$)
   - `cont_purity_implies` ($\mathrm{IsPure}(\mathrm{Cont}\;R) \to \mathrm{Subsingleton}\;R$)
   - `io_not_pure` ($\neg\,\mathrm{IsPure}(\mathrm{ErrorState}\;E\;S)$)

## Repository Structure

- `Challenge.lean` — Core definitions and main theorem statements.
- `Solution.lean` — Exports the verified proofs of all challenge theorems.
- `CoEndoYonedaAndPurity/Basic.lean` — Core definitions synchronized with `CoEndoYoneda.lagda.md`.
- `CoEndoYonedaAndPurity.lean` — Complete proofs of all lemmas, theorems, and examples.
- `tex/paper.tex` & `tex/paper.pdf` — Accompanying aiXiv-ready LaTeX paper based on `CoEndoYoneda.lagda.md`.
- `comparator.json` — Configuration for `lake comparator`.
- `formalization.yaml` — Palomar Registry metadata.

## Verification & Submission

```bash
python3 scripts/check-lean-sources.py
ruby scripts/validate-formalization.rb
lake exe cache get
lake build
./scripts/verify-comparator.sh
```
