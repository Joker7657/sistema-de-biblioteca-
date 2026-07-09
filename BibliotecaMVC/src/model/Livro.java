package model;

import util.Validacoes;

// ---------------------------------------------------------------------------
// LIVRO - Logica Aplicada a Engenharia de Software
//
// Invariante de classe (conjuncao de predicados atomicos):
//   I_Livro = id > 0
//           /\ textoPreenchido(titulo)
//           /\ textoPreenchido(autor)
//           /\ textoPreenchido(isbn)
//
// Estados de disponibilidade:
//   disponivel = true  -> livro pode ser emprestado
//   disponivel = false -> livro esta emprestado
//
// Automato de dois estados:
//   Livre --emprestar()--> Emprestado
//   Emprestado --devolver()--> Livre
// ---------------------------------------------------------------------------
public class Livro {

    // Invariante como conjuncao (/\) de predicados individuais:
    //@ public invariant id > 0;
    //@ public invariant Validacoes.textoPreenchido(titulo);
    //@ public invariant Validacoes.textoPreenchido(autor);
    //@ public invariant Validacoes.textoPreenchido(isbn);
    // Invariante combinada: I_Livro = P1 /\ P2 /\ P3 /\ P4
    //@ public invariant id > 0
    //@         && Validacoes.textoPreenchido(titulo)
    //@         && Validacoes.textoPreenchido(autor)
    //@         && Validacoes.textoPreenchido(isbn);

    private int id;
    private String titulo;
    private String autor;
    private String isbn;
    private boolean disponivel;

    /*@
      @ // Tripla de Hoare:
      @ // {id>0 /\ textoPreenchido(titulo) /\ textoPreenchido(autor) /\ textoPreenchido(isbn)}
      @ //   Livro(id, titulo, autor, isbn)
      @ // {this.id==id /\ this.disponivel==true /\ I_Livro}
      @ public normal_behavior
      @ requires id > 0;
      @ requires Validacoes.textoPreenchido(titulo);
      @ requires Validacoes.textoPreenchido(autor);
      @ requires Validacoes.textoPreenchido(isbn);
      @ assignable this.id, this.titulo, this.autor, this.isbn, this.disponivel;
      @ // Pos-condicao como conjuncao: todos os campos inicializados corretamente
      @ ensures this.id == id
      @      && this.titulo.equals(titulo.trim())
      @      && this.autor.equals(autor.trim())
      @      && this.isbn.equals(isbn.trim())
      @      && this.disponivel;              // todo livro nasce disponivel
      @ // Implicacao: pre satisfeita ==> invariante garantida
      @ ensures (id > 0 && Validacoes.textoPreenchido(titulo)) ==> this.id > 0;
      @ signals (IllegalArgumentException e) false;
      @*/
    public Livro(int id, String titulo, String autor, String isbn) {
        if (id <= 0) {
            throw new IllegalArgumentException("Id do livro deve ser maior que zero.");
        }
        if (!Validacoes.textoPreenchido(titulo)) {
            throw new IllegalArgumentException("Titulo do livro e obrigatorio.");
        }
        if (!Validacoes.textoPreenchido(autor)) {
            throw new IllegalArgumentException("Autor do livro e obrigatorio.");
        }
        if (!Validacoes.textoPreenchido(isbn)) {
            throw new IllegalArgumentException("ISBN do livro e obrigatorio.");
        }

        this.id = id;
        this.titulo = titulo.trim();
        this.autor = autor.trim();
        this.isbn = isbn.trim();
        this.disponivel = true;

        assert this.disponivel : "Livro novo deve iniciar disponivel.";
    }

    /*@
      @ // Proposicao: \result == id  (funcao identidade no campo)
      @ public normal_behavior
      @ ensures \result == id;
      @ pure
      @*/
    public int getId() {
        return id;
    }

    /*@
      @ public normal_behavior
      @ ensures \result != null && \result.equals(titulo);
      @ pure
      @*/
    public String getTitulo() {
        return titulo;
    }

    /*@
      @ public normal_behavior
      @ ensures \result != null && \result.equals(autor);
      @ pure
      @*/
    public String getAutor() {
        return autor;
    }

    /*@
      @ public normal_behavior
      @ ensures \result != null && \result.equals(isbn);
      @ pure
      @*/
    public String getIsbn() {
        return isbn;
    }

    /*@
      @ // Bicondicional: \result <=> disponivel
      @ public normal_behavior
      @ ensures \result <==> disponivel;
      @ pure
      @*/
    public boolean isDisponivel() {
        return disponivel;
    }

    /*@
      @ public normal_behavior
      @ requires id > 0;
      @ assignable this.id;
      @ ensures this.id == id;
      @ // Preservacao dos demais campos:
      @ ensures this.titulo.equals(\old(this.titulo))
      @      && this.autor.equals(\old(this.autor))
      @      && this.isbn.equals(\old(this.isbn))
      @      && this.disponivel == \old(this.disponivel);
      @*/
    public void setId(int id) {
        if (id <= 0) {
            throw new IllegalArgumentException("Id do livro deve ser maior que zero.");
        }
        this.id = id;
    }

    /*@
      @ // -----------------------------------------------------------------
      @ // REGRA DE ATRIBUICAO (Assignment Axiom):
      @ //   {P[x/E]}  x := E  {P}
      @ //
      @ // Queremos Q = (this.titulo.equals(titulo.trim()))
      @ // Seja x = this.titulo,  E = titulo.trim()
      @ // Pre_atribuicao = Q[this.titulo / titulo.trim()]
      @ //                = titulo.trim().equals(titulo.trim())  => true (tautologia)
      @ //
      @ // Logo a atribuicao per se nao exige pre-condicao propria.
      @ // A pre-condicao real vem da REGRA DA CONSEQUENCIA (veja abaixo).
      @ // -----------------------------------------------------------------
      @ // REGRA DA CONSEQUENCIA (Implication/Consequence Rule):
      @ //   P' => P    {P} S {Q}    Q => Q'
      @ //   ------------------------------------
      @ //           {P'} S {Q'}
      @ //
      @ // P  (fraca, da atribuicao): true
      @ // P' (forte, do metodo)    : Validacoes.textoPreenchido(titulo)
      @ // Como P' => P  (qualquer coisa implica true), a regra permite
      @ // fortalecer a pre-condicao para garantir I_Livro apos execucao.
      @ // -----------------------------------------------------------------
      @ public normal_behavior
      @ requires Validacoes.textoPreenchido(titulo); // pre-condicao fortalecida (Consequencia)
      @ assignable this.titulo;
      @ ensures this.titulo.equals(titulo.trim());   // Q da Regra de Atribuicao
      @ ensures Validacoes.textoPreenchido(this.titulo); // invariante preservada
      @ ensures this.id == \old(this.id)
      @      && this.autor.equals(\old(this.autor))
      @      && this.isbn.equals(\old(this.isbn))
      @      && this.disponivel == \old(this.disponivel);
      @*/
    public void setTitulo(String titulo) {
        if (!Validacoes.textoPreenchido(titulo)) {
            throw new IllegalArgumentException("Titulo do livro e obrigatorio.");
        }
        this.titulo = titulo.trim();
    }

    /*@
      @ public normal_behavior
      @ requires Validacoes.textoPreenchido(autor);
      @ assignable this.autor;
      @ ensures this.autor.equals(autor.trim());
      @ ensures this.id == \old(this.id)
      @      && this.titulo.equals(\old(this.titulo))
      @      && this.isbn.equals(\old(this.isbn))
      @      && this.disponivel == \old(this.disponivel);
      @*/
    public void setAutor(String autor) {
        if (!Validacoes.textoPreenchido(autor)) {
            throw new IllegalArgumentException("Autor do livro e obrigatorio.");
        }
        this.autor = autor.trim();
    }

    /*@
      @ // REGRA DE ATRIBUICAO aplicada:
      @ //   Queremos Q = (this.isbn.equals(isbn.trim()))
      @ //   Pre_atrib = Q[this.isbn / isbn.trim()] = isbn.trim().equals(isbn.trim()) = true
      @ //
      @ // REGRA DA CONSEQUENCIA para fortalecer pre:
      @ //   true => Validacoes.textoPreenchido(isbn)  [nao implica, por isso exigimos]
      @ //   Validacoes.textoPreenchido(isbn) => true  [implica, validando o fortalecimento]
      @ //   Usamos pre P' = Validacoes.textoPreenchido(isbn) para garantir I_Livro.
      @ public normal_behavior
      @ requires Validacoes.textoPreenchido(isbn); // pre fortalecida via Consequencia
      @ assignable this.isbn;
      @ ensures this.isbn.equals(isbn.trim());     // Q da Atribuicao
      @ ensures Validacoes.textoPreenchido(this.isbn);
      @ ensures this.id == \old(this.id)
      @      && this.titulo.equals(\old(this.titulo))
      @      && this.autor.equals(\old(this.autor))
      @      && this.disponivel == \old(this.disponivel);
      @*/
    public void setIsbn(String isbn) {
        if (!Validacoes.textoPreenchido(isbn)) {
            throw new IllegalArgumentException("ISBN do livro e obrigatorio.");
        }
        this.isbn = isbn.trim();
    }

    /*@
      @ // ================================================================
      @ // REGRA DO CONDICIONAL:
      @ //   {P /\ B}  S1  {Q}     {P /\ !B}  S2  {Q}
      @ //   ──────────────────────────────────────────────
      @ //      {P}  if B then S1 else S2  {Q}
      @ //
      @ // Seja:
      @ //   P  = disponivel           (pre-condicao do metodo)
      @ //   B  = !disponivel          (condicao do if-guard)
      @ //   S1 = throw exception      (ramo then)
      @ //   S2 = disponivel = false   (ramo else implicito, apos guard)
      @ //   Q  = !disponivel          (pos-condicao)
      @ //
      @ // Ramo then  {P /\ B} = {disponivel /\ !disponivel} = {false}:
      @ //   {false} throw exception {Q}  -- vacuamente verdadeiro (ex falso quodlibet)
      @ //
      @ // Ramo else  {P /\ !B} = {disponivel /\ disponivel} = {disponivel}:
      @ //   {disponivel}  disponivel = false  {!disponivel}
      @ //   Provado pela REGRA DE ATRIBUICAO:
      @ //     Q = (!disponivel),  x = disponivel,  E = false
      @ //     Q[disponivel/false] = (!false) = true
      @ //     Como disponivel => true, pela CONSEQUENCIA: {disponivel} S2 {!disponivel}
      @ // ================================================================
      @ public normal_behavior
      @ requires disponivel;                     // P
      @ assignable this.disponivel;
      @ ensures !this.disponivel;                // Q
      @ ensures \old(disponivel) ==> !disponivel; // implicacao temporal P -> Q
      @ ensures !disponivel <==> \old(disponivel); // bicondicional de transicao
      @ ensures this.id == \old(this.id)
      @      && this.titulo.equals(\old(this.titulo))
      @      && this.isbn.equals(\old(this.isbn));
      @ also
      @ // Ramo then do CONDICIONAL: {P /\ B} = {false} => excecao garantida
      @ public exceptional_behavior
      @ requires !disponivel;                    // !P (B satisfeito)
      @ assignable \nothing;
      @ signals (IllegalStateException e) !\old(disponivel);
      @*/
    public void emprestar() {
        // CONDICIONAL: B = !disponivel
        // {disponivel /\ !disponivel} = {false} => throw (ramo then)
        if (!disponivel) {
            throw new IllegalStateException("Livro nao esta disponivel para emprestimo.");
        }
        // Aqui: {disponivel /\ disponivel} = {disponivel} (ramo else do CONDICIONAL)
        // ATRIBUICAO: {!false} disponivel = false {!disponivel}
        disponivel = false;
        // {!disponivel}  -- pos-condicao satisfeita
        assert !disponivel : "Livro emprestado deve ficar indisponivel.";
    }

    /*@
      @ // ================================================================
      @ // REGRA DO CONDICIONAL (inverso simetrico de emprestar):
      @ //   P  = !disponivel          (pre-condicao)
      @ //   B  = disponivel           (condicao do if-guard)
      @ //   S1 = throw exception      (ramo then)
      @ //   S2 = disponivel = true    (ramo else implicito)
      @ //   Q  = disponivel           (pos-condicao)
      @ //
      @ // Ramo then  {P /\ B} = {!disponivel /\ disponivel} = {false}:
      @ //   vacuamente verdadeiro
      @ //
      @ // Ramo else  {P /\ !B} = {!disponivel /\ !disponivel} = {!disponivel}:
      @ //   REGRA DE ATRIBUICAO:
      @ //     Q = (disponivel),  x = disponivel,  E = true
      @ //     Q[disponivel/true] = (true) = true
      @ //     Como !disponivel => true, pela CONSEQUENCIA: {!disponivel} S2 {disponivel}
      @ // ================================================================
      @ public normal_behavior
      @ requires !disponivel;                    // P
      @ assignable this.disponivel;
      @ ensures this.disponivel;                 // Q
      @ ensures \old(!disponivel) ==> disponivel; // implicacao temporal P -> Q
      @ ensures disponivel <==> !\old(disponivel); // bicondicional de transicao
      @ ensures this.id == \old(this.id)
      @      && this.titulo.equals(\old(this.titulo))
      @      && this.isbn.equals(\old(this.isbn));
      @ also
      @ // Ramo then do CONDICIONAL: {P /\ B} = {false} => excecao garantida
      @ public exceptional_behavior
      @ requires disponivel;                     // !P (B satisfeito)
      @ assignable \nothing;
      @ signals (IllegalStateException e) \old(disponivel);
      @*/
    public void devolver() {
        // CONDICIONAL: B = disponivel
        // {!disponivel /\ disponivel} = {false} => throw (ramo then)
        if (disponivel) {
            throw new IllegalStateException("Livro ja esta disponivel.");
        }
        // Aqui: {!disponivel /\ !disponivel} = {!disponivel} (ramo else do CONDICIONAL)
        // ATRIBUICAO: {true} disponivel = true {disponivel}
        disponivel = true;
        // {disponivel}  -- pos-condicao satisfeita
        assert disponivel : "Livro devolvido deve ficar disponivel.";
    }

    @Override
    /*@
      @ public normal_behavior
      @ ensures \result != null && !\result.isEmpty();
      @ pure
      @*/
    public String toString() {
        return "Livro{id=" + id + ", titulo='" + titulo + "', autor='" + autor
                + "', isbn='" + isbn + "', disponivel=" + disponivel + "}";
    }
}
