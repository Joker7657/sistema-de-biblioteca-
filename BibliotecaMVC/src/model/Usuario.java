package model;

import util.Validacoes;

// ---------------------------------------------------------------------------
// USUARIO - Logica Aplicada a Engenharia de Software
//
// Invariante de classe (I_Usuario):
//   I_Usuario = id > 0
//             /\ textoPreenchido(nome)
//             /\ textoPreenchido(matricula)
//             /\ emailValido(email)
//
// Toda operacao de escrita preserva I_Usuario ou lanca excecao.
// ---------------------------------------------------------------------------
public class Usuario {

    // Invariante como conjuncao de predicados atomicos (I_Usuario):
    //@ public invariant id > 0;
    //@ public invariant Validacoes.textoPreenchido(nome);
    //@ public invariant Validacoes.textoPreenchido(matricula);
    //@ public invariant Validacoes.emailValido(email);
    // Forma combinada: I_Usuario = P1 /\ P2 /\ P3 /\ P4
    //@ public invariant id > 0
    //@         && Validacoes.textoPreenchido(nome)
    //@         && Validacoes.textoPreenchido(matricula)
    //@         && Validacoes.emailValido(email);

    private int id;
    private String nome;
    private String matricula;
    private String email;

    /*@
      @ // Tripla de Hoare:
      @ // {id>0 /\ textoPreenchido(nome) /\ textoPreenchido(matricula) /\ emailValido(email)}
      @ //   Usuario(id, nome, matricula, email)
      @ // {I_Usuario /\ this.id==id /\ this.nome==nome.trim() /\ ...}
      @ public normal_behavior
      @ requires id > 0;
      @ requires Validacoes.textoPreenchido(nome);
      @ requires Validacoes.textoPreenchido(matricula);
      @ requires Validacoes.emailValido(email);
      @ assignable this.id, this.nome, this.matricula, this.email;
      @ // Pos-condicao como conjuncao:
      @ ensures this.id == id
      @      && this.nome.equals(nome.trim())
      @      && this.matricula.equals(matricula.trim())
      @      && this.email.equals(email.trim());
      @ // Implicacao: pre satisfeita ==> invariante garantida
      @ ensures Validacoes.textoPreenchido(this.nome) && Validacoes.emailValido(this.email);
      @ signals (IllegalArgumentException e) false;
      @*/
    public Usuario(int id, String nome, String matricula, String email) {
        if (id <= 0) {
            throw new IllegalArgumentException("Id do usuario deve ser maior que zero.");
        }
        if (!Validacoes.textoPreenchido(nome)) {
            throw new IllegalArgumentException("Nome do usuario e obrigatorio.");
        }
        if (!Validacoes.textoPreenchido(matricula)) {
            throw new IllegalArgumentException("Matricula do usuario e obrigatoria.");
        }
        if (!Validacoes.emailValido(email)) {
            throw new IllegalArgumentException("Email do usuario e invalido.");
        }

        this.id = id;
        this.nome = nome.trim();
        this.matricula = matricula.trim();
        this.email = email.trim();
    }

    /*@
      @ public normal_behavior
      @ ensures \result == id;
      @ pure
      @*/
    public int getId() {
        return id;
    }

    /*@
      @ public normal_behavior
      @ ensures \result != null && \result.equals(nome);
      @ pure
      @*/
    public String getNome() {
        return nome;
    }

    /*@
      @ public normal_behavior
      @ ensures \result != null && \result.equals(matricula);
      @ pure
      @*/
    public String getMatricula() {
        return matricula;
    }

    /*@
      @ public normal_behavior
      @ ensures \result != null && \result.equals(email);
      @ pure
      @*/
    public String getEmail() {
        return email;
    }

    /*@
      @ public normal_behavior
      @ requires id > 0;
      @ assignable this.id;
      @ ensures this.id == id;
      @ ensures this.nome.equals(\old(this.nome))
      @      && this.matricula.equals(\old(this.matricula))
      @      && this.email.equals(\old(this.email));
      @*/
    public void setId(int id) {
        if (id <= 0) {
            throw new IllegalArgumentException("Id do usuario deve ser maior que zero.");
        }
        this.id = id;
    }

    /*@
      @ // P: textoPreenchido(nome)
      @ // Q: this.nome.equals(nome.trim())
      @ // Contrato: P ==> Q  (implicacao direta)
      @ // Contrapositivo: !Q ==> !P
      @ public normal_behavior
      @ requires Validacoes.textoPreenchido(nome);
      @ assignable this.nome;
      @ ensures this.nome.equals(nome.trim());
      @ ensures Validacoes.textoPreenchido(this.nome); // invariante preservada
      @ ensures this.id == \old(this.id)
      @      && this.matricula.equals(\old(this.matricula))
      @      && this.email.equals(\old(this.email));
      @ also
      @ public exceptional_behavior
      @ requires !Validacoes.textoPreenchido(nome);
      @ assignable \nothing;
      @ signals (IllegalArgumentException e) !Validacoes.textoPreenchido(nome);
      @*/
    public void setNome(String nome) {
        if (!Validacoes.textoPreenchido(nome)) {
            throw new IllegalArgumentException("Nome do usuario e obrigatorio.");
        }
        this.nome = nome.trim();
    }

    /*@
      @ public normal_behavior
      @ requires Validacoes.textoPreenchido(matricula);
      @ assignable this.matricula;
      @ ensures this.matricula.equals(matricula.trim());
      @ ensures Validacoes.textoPreenchido(this.matricula);
      @ ensures this.id == \old(this.id)
      @      && this.nome.equals(\old(this.nome))
      @      && this.email.equals(\old(this.email));
      @ also
      @ public exceptional_behavior
      @ requires !Validacoes.textoPreenchido(matricula);
      @ assignable \nothing;
      @ signals (IllegalArgumentException e) !Validacoes.textoPreenchido(matricula);
      @*/
    public void setMatricula(String matricula) {
        if (!Validacoes.textoPreenchido(matricula)) {
            throw new IllegalArgumentException("Matricula do usuario e obrigatoria.");
        }
        this.matricula = matricula.trim();
    }

    /*@
      @ // P: emailValido(email)
      @ // Q: this.email.equals(email.trim())
      @ // Contrato: P ==> Q
      @ public normal_behavior
      @ requires Validacoes.emailValido(email);
      @ assignable this.email;
      @ ensures this.email.equals(email.trim());
      @ ensures Validacoes.emailValido(this.email); // invariante preservada
      @ ensures this.id == \old(this.id)
      @      && this.nome.equals(\old(this.nome))
      @      && this.matricula.equals(\old(this.matricula));
      @ also
      @ public exceptional_behavior
      @ requires !Validacoes.emailValido(email);
      @ assignable \nothing;
      @ signals (IllegalArgumentException e) !Validacoes.emailValido(email);
      @*/
    public void setEmail(String email) {
        if (!Validacoes.emailValido(email)) {
            throw new IllegalArgumentException("Email do usuario e invalido.");
        }
        this.email = email.trim();
    }

    @Override
    /*@
      @ public normal_behavior
      @ ensures \result != null && !\result.isEmpty();
      @ pure
      @*/
    public String toString() {
        return "Usuario{id=" + id + ", nome='" + nome + "', matricula='" + matricula
                + "', email='" + email + "'}";
    }
}
