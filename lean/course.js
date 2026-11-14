const course = {
  "es": {
    "levels": [
      {
        "title": "Usa una hipótesis",
        "statement": "(P : Prop) (h : P) : P",
        "hint": "Ya tienes una prueba de P en h. Entrégala con exact."
      },
      {
        "title": "Introduce una hipótesis",
        "statement": "(P : Prop) : P → P",
        "hint": "Usa intro h para convertir la premisa en una hipótesis."
      },
      {
        "title": "Separa una conjunción",
        "statement": "(P Q : Prop) : P ∧ Q → P",
        "hint": "Tras intro h, h.1 es la prueba de P que contiene la conjunción."
      },
      {
        "title": "Construye una conjunción",
        "statement": "(P Q : Prop) : P → Q → P ∧ Q",
        "hint": "Usa intro hp hq. Luego constructor crea dos metas, una por cada componente."
      },
      {
        "title": "Invierte la conjunción",
        "statement": "(P Q : Prop) : (P ∧ Q) ↔ (Q ∧ P)",
        "hint": "Empieza con constructor para separar las dos implicaciones. En cada dirección, introduce h y construye la conjunción en orden inverso."
      },
      {
        "title": "Elige la izquierda",
        "statement": "(P Q : Prop) : P → P ∨ Q",
        "hint": "Introduce hp. Usa left para elegir P y exact hp para cerrar."
      },
      {
        "title": "Elige la derecha",
        "statement": "(P Q : Prop) : Q → P ∨ Q",
        "hint": "Introduce hq y usa right para dejar Q como meta."
      },
      {
        "title": "Razona por casos",
        "statement": "(P : Prop) : P ∨ P → P",
        "hint": "Usa cases h para abrir dos casos. En cada uno, rename_i hp nombra la hipótesis de P."
      },
      {
        "title": "Invierte la disyunción",
        "statement": "(P Q : Prop) : P ∨ Q → Q ∨ P",
        "hint": "Abre los dos casos. Si tienes P, elige la derecha. Si tienes Q, elige la izquierda."
      }
    ]
  },
  "en": {
    "levels": [
      {
        "title": "Use a hypothesis",
        "statement": "(P : Prop) (h : P) : P",
        "hint": "Use exact h to close the goal."
      },
      {
        "title": "Introduce a hypothesis",
        "statement": "(P : Prop) : P → P",
        "hint": "Use intro h to bring the premise into the context."
      },
      {
        "title": "Unpack a conjunction",
        "statement": "(P Q : Prop) : P ∧ Q → P",
        "hint": "After intro h, h.1 provides a proof of P."
      },
      {
        "title": "Build a conjunction",
        "statement": "(P Q : Prop) : P → Q → P ∧ Q",
        "hint": "Use intro hp hq, then constructor to create one goal per component."
      },
      {
        "title": "Swap a conjunction",
        "statement": "(P Q : Prop) : (P ∧ Q) ↔ (Q ∧ P)",
        "hint": "Start with constructor to split the equivalence into two implications. Build the conjunction in reverse order in each direction."
      },
      {
        "title": "Choose the left side",
        "statement": "(P Q : Prop) : P → P ∨ Q",
        "hint": "Introduce hp, choose left, then use exact hp."
      },
      {
        "title": "Choose the right side",
        "statement": "(P Q : Prop) : Q → P ∨ Q",
        "hint": "Introduce hq, choose right, then use exact hq."
      },
      {
        "title": "Reason by cases",
        "statement": "(P : Prop) : P ∨ P → P",
        "hint": "Use cases h. In each case use rename_i hp to name the proof of P."
      },
      {
        "title": "Swap a disjunction",
        "statement": "(P Q : Prop) : P ∨ Q → Q ∨ P",
        "hint": "Split the disjunction. Choose right when you have P and left when you have Q."
      }
    ]
  }
};
