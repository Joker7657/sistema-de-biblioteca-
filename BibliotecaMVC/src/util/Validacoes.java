package util;

// ---------------------------------------------------------------------------
// Lógica Proposicional aplicada:
//   textoPreenchido(t)  ⟺  (t ≠ null) ∧ (t.trim() ≠ "")
//   emailValido(e)      ⟺  (e ≠ null) ∧ (e satisfaz padrão ^[...]+@[...]+$)
//   textoVazio(t)       ⟺  textoPreenchido(t) → false
//
// As especificações JML usam:
//   &&  →  conjunção (∧)
//   ||  →  disjunção (∨)
//   !   →  negação   (¬)
//   ==> →  implicação (→)
//   <==>→  bicondicional (↔)
// ---------------------------------------------------------------------------
public final class Validacoes {

    private Validacoes() {
    }

    /*@
      @ // Proposições:
      @ //   P : texto != null
      @ //   Q : !texto.trim().isEmpty()
      @ // Resultado: \result ↔ (P ∧ Q)
      @ // Equivalente em JML: \result <==> (P && Q)
      @ public normal_behavior
      @ ensures \result <==> (texto != null && !texto.trim().isEmpty());
      @ // Contrapositivo: ¬\result → (texto == null ∨ texto.trim().isEmpty())
      @ ensures !\result ==> (texto == null || texto.trim().isEmpty());
      @ // Casos atômicos via implicação:
      @ ensures (texto == null) ==> !\result;
      @ ensures (texto != null && texto.trim().isEmpty()) ==> !\result;
      @ ensures (texto != null && !texto.trim().isEmpty()) ==> \result;
      @ pure
      @*/
    public static boolean textoPreenchido(String texto) {
        return texto != null && !texto.trim().isEmpty();
    }

    /*@
      @ // Proposições:
      @ //   P : email != null
      @ //   Q : email satisfaz a expressão regular RFC simplificada
      @ // Resultado: \result ↔ (P ∧ Q)
      @ public normal_behavior
      @ ensures \result <==> (email != null && email.matches("^[A-Za-z0-9+_.-]+@[A-Za-z0-9.-]+$"));
      @ // Casos via implicação directa:
      @ ensures (email == null) ==> !\result;
      @ ensures (email != null && !email.matches("^[A-Za-z0-9+_.-]+@[A-Za-z0-9.-]+$")) ==> !\result;
      @ ensures (email != null && email.matches("^[A-Za-z0-9+_.-]+@[A-Za-z0-9.-]+$")) ==> \result;
      @ pure
      @*/
    public static boolean emailValido(String email) {
        return email != null && email.matches("^[A-Za-z0-9+_.-]+@[A-Za-z0-9.-]+$");
    }

    /*@
      @ // textoVazio ↔ ¬textoPreenchido  (para texto ≠ null)
      @ public normal_behavior
      @ requires texto != null;
      @ ensures \result <==> texto.trim().isEmpty();
      @ // Relação de complementaridade: textoVazio(t) ↔ ¬textoPreenchido(t)
      @ ensures \result <==> !textoPreenchido(texto);
      @ pure
      @*/
    public static boolean textoVazio(String texto) {
        return texto.trim().isEmpty();
    }
}
