package model;

import java.time.LocalDate;

// ---------------------------------------------------------------------------
// EMPRESTIMO - Logica Aplicada a Engenharia de Software
//
// Invariante de classe (I_Emprestimo):
//   I = livro != null /\ usuario != null /\ dataEmprestimo != null
//     /\ (dataDevolucao != null -> !dataDevolucao.isBefore(dataEmprestimo))
//     /\ isAtivo() <=> (dataDevolucao == null)
//     /\ !livro.isDisponivel() <=> isAtivo()
//
// Automato de estados:
//   ATIVO:     dataDevolucao == null  /\ !livro.isDisponivel()
//   ENCERRADO: dataDevolucao != null  /\ livro.isDisponivel()
//
// Transicao unica permitida: ATIVO --registrarDevolucao()--> ENCERRADO
// ---------------------------------------------------------------------------
public class Emprestimo {

    // Invariante como conjuncao de predicados:
    //@ public invariant livro != null && usuario != null && dataEmprestimo != null;
    // Implicacao temporal para data de devolucao:
    //@ public invariant (dataDevolucao != null) ==> !dataDevolucao.isBefore(dataEmprestimo);
    // Bicondicional de estado: isAtivo <=> devolucao ainda nao registrada
    //@ public invariant isAtivo() <==> (dataDevolucao == null);
    // Bicondicional de disponibilidade: livro indisponivel <=> emprestimo ativo
    //@ public invariant isAtivo() <==> !livro.isDisponivel();

    private final Livro livro;
    private final Usuario usuario;
    private final LocalDate dataEmprestimo;
    private LocalDate dataDevolucao;

    /*@
      @ // ================================================================
      @ // REGRA DA COMPOSICAO (Sequencing Rule):
      @ //   {P} S1 {Q}    {Q} S2 {R}
      @ //   ─────────────────────────
      @ //      {P} S1 ; S2 {R}
      @ //
      @ // Sequencia de atribuicoes no construtor:
      @ //
      @ //  P0 = livro!=null /\ usuario!=null /\ data!=null /\ livro.isDisponivel()
      @ //
      @ //  {P0}  S1: this.livro = livro  {P1}
      @ //    Por ATRIBUICAO: P1 = (this.livro == livro /\ usuario!=null /\ data!=null /\ livro.isDisponivel())
      @ //
      @ //  {P1}  S2: this.usuario = usuario  {P2}
      @ //    Por ATRIBUICAO: P2 = P1 /\ (this.usuario == usuario)
      @ //
      @ //  {P2}  S3: this.dataEmprestimo = dataEmprestimo  {P3}
      @ //    Por ATRIBUICAO: P3 = P2 /\ (this.dataEmprestimo.equals(dataEmprestimo))
      @ //
      @ //  {P3}  S4: this.dataDevolucao = null  {P4}
      @ //    Por ATRIBUICAO: P4 = P3 /\ (this.dataDevolucao == null)
      @ //
      @ //  {P4}  S5: this.livro.emprestar()  {P5}
      @ //    Pre de emprestar() = livro.isDisponivel() -- satisfeita por P4
      @ //    P5 = P4 /\ !this.livro.isDisponivel()
      @ //
      @ //  Por COMPOSICAO encadeada: {P0} S1;S2;S3;S4;S5 {P5}
      @ // ================================================================
      @ public normal_behavior
      @ requires livro != null && usuario != null && dataEmprestimo != null;
      @ requires livro.isDisponivel();  // P0: livro livre antes do emprestimo
      @ assignable this.livro, this.usuario, this.dataEmprestimo, this.dataDevolucao, livro.*;
      @ // Pos-condicao P5 (resultado da composicao):
      @ ensures this.livro == livro
      @      && this.usuario == usuario
      @      && this.dataEmprestimo.equals(dataEmprestimo)
      @      && this.dataDevolucao == null;          // estado ATIVO
      @ ensures \old(livro.isDisponivel()) ==> !this.livro.isDisponivel(); // implicacao temporal
      @ ensures isAtivo() <==> (this.dataDevolucao == null); // bicondicional de estado
      @ signals (IllegalArgumentException e) false;
      @*/
    public Emprestimo(Livro livro, Usuario usuario, LocalDate dataEmprestimo) {
        if (livro == null) {
            throw new IllegalArgumentException("Livro nao pode ser nulo.");
        }
        if (usuario == null) {
            throw new IllegalArgumentException("Usuario nao pode ser nulo.");
        }
        if (dataEmprestimo == null) {
            throw new IllegalArgumentException("Data de emprestimo nao pode ser nula.");
        }
        if (!livro.isDisponivel()) {
            throw new IllegalArgumentException("Livro deve estar disponivel para criar emprestimo.");
        }

        // S1: {P0}  this.livro = livro  {P0 /\ this.livro==livro}
        this.livro = livro;
        // S2: {P1}  this.usuario = usuario  {P1 /\ this.usuario==usuario}
        this.usuario = usuario;
        // S3: {P2}  this.dataEmprestimo = dataEmprestimo  {P2 /\ this.dataEmprestimo.equals(data)}
        this.dataEmprestimo = dataEmprestimo;
        // S4: {P3}  this.dataDevolucao = null  {P3 /\ this.dataDevolucao==null}
        this.dataDevolucao = null;
        // S5: {P4 /\ livro.isDisponivel()}  emprestar()  {P4 /\ !livro.isDisponivel()}
        this.livro.emprestar();
        // P5 satisfeito por composicao:
        assert !this.livro.isDisponivel() : "Livro deve ficar indisponivel apos criar emprestimo.";
    }

    /*@
      @ public normal_behavior
      @ ensures \result == livro && \result != null;
      @ pure
      @*/
    public Livro getLivro() {
        return livro;
    }

    /*@
      @ public normal_behavior
      @ ensures \result == usuario && \result != null;
      @ pure
      @*/
    public Usuario getUsuario() {
        return usuario;
    }

    /*@
      @ public normal_behavior
      @ ensures \result != null && \result.equals(dataEmprestimo);
      @ pure
      @*/
    public LocalDate getDataEmprestimo() {
        return dataEmprestimo;
    }

    /*@
      @ public normal_behavior
      @ ensures \result == dataDevolucao;  // pode ser null enquanto ativo
      @ pure
      @*/
    public LocalDate getDataDevolucao() {
        return dataDevolucao;
    }

    /*@
      @ // Bicondicional central do estado do emprestimo:
      @ //   isAtivo() <=> (dataDevolucao == null)
      @ // Equivalentemente: !isAtivo() <=> (dataDevolucao != null)
      @ public normal_behavior
      @ ensures \result <==> (dataDevolucao == null);
      @ ensures !\result <==> (dataDevolucao != null);
      @ pure
      @*/
    public boolean isAtivo() {
        return dataDevolucao == null;
    }

    /*@
      @ // ================================================================
      @ // REGRA DO CONDICIONAL aplicada 3 vezes (guardas em sequencia)
      @ // + REGRA DA COMPOSICAO para a sequencia final de instrucoes
      @ //
      @ // Seja P = (data!=null /\ dataDevolucao==null /\ !data.isBefore(dataEmprestimo))
      @ //
      @ // --- CONDICIONAL 1: guarda data==null ---
      @ //   B1 = (data == null)
      @ //   {P /\ B1}  throw  {Q}    -- {false} throw {Q} vacuamente verdadeiro
      @ //   {P /\ !B1} = {data!=null /\ ...}  continua para CONDICIONAL 2
      @ //
      @ // --- CONDICIONAL 2: guarda dataDevolucao!=null ---
      @ //   B2 = (dataDevolucao != null)
      @ //   {P /\ !B1 /\ B2}  throw  {Q}    -- vacuamente verdadeiro
      @ //   {P /\ !B1 /\ !B2} = {data!=null /\ dataDevolucao==null /\ ...}  continua
      @ //
      @ // --- CONDICIONAL 3: guarda data.isBefore(dataEmprestimo) ---
      @ //   B3 = data.isBefore(dataEmprestimo)
      @ //   {P /\ !B1 /\ !B2 /\ B3}  throw  {Q}  -- vacuamente verdadeiro
      @ //   {P /\ !B1 /\ !B2 /\ !B3}  continua para COMPOSICAO
      @ //
      @ // Apos as 3 guardas temos o estado:
      @ //   Q0 = data!=null /\ dataDevolucao==null /\ !data.isBefore(dataEmprestimo)
      @ //
      @ // --- COMPOSICAO: S1 seguido de S2 ---
      @ //   S1 = this.dataDevolucao = data
      @ //   S2 = this.livro.devolver()
      @ //
      @ //   {Q0}  S1: this.dataDevolucao = data  {Q1}
      @ //     Por ATRIBUICAO:
      @ //       Queremos Q1 = (this.dataDevolucao.equals(data) /\ !\old(livro.isDisponivel()))
      @ //       Q1[this.dataDevolucao / data] = (data.equals(data) /\ ...) = (true /\ ...)
      @ //       Como Q0 => true, pela CONSEQUENCIA: {Q0} S1 {Q1}
      @ //
      @ //   {Q1}  S2: this.livro.devolver()  {Q2}
      @ //     Pre de devolver() = !livro.isDisponivel() -- satisfeita por Q1
      @ //     Q2 = Q1 /\ livro.isDisponivel()
      @ //
      @ //   Por COMPOSICAO: {Q0} S1;S2 {Q2}
      @ // ================================================================
      @ public normal_behavior
      @ requires data != null && dataDevolucao == null;
      @ requires !data.isBefore(dataEmprestimo);
      @ assignable this.dataDevolucao, livro.*;
      @ // Pos-condicao Q2 (resultado da composicao):
      @ ensures this.dataDevolucao != null
      @      && this.dataDevolucao.equals(data)
      @      && livro.isDisponivel();
      @ ensures \old(dataDevolucao == null) ==> (dataDevolucao != null);
      @ ensures \old(!livro.isDisponivel()) ==> livro.isDisponivel();
      @ ensures !isAtivo() <==> (this.dataDevolucao != null);
      @ ensures !this.dataDevolucao.isBefore(this.dataEmprestimo);
      @ also
      @ // CONDICIONAL 2 -- ramo then: {!P /\ dataDevolucao!=null} => IllegalStateException
      @ public exceptional_behavior
      @ requires dataDevolucao != null;
      @ assignable \nothing;
      @ signals (IllegalStateException e) \old(dataDevolucao) != null;
      @ also
      @ // CONDICIONAL 1 e 3 -- ramos then: data==null ou data invalida => IllegalArgumentException
      @ public exceptional_behavior
      @ requires data == null || (data != null && data.isBefore(dataEmprestimo));
      @ assignable \nothing;
      @ signals (IllegalArgumentException e)
      @         (data == null) || (data != null && data.isBefore(dataEmprestimo));
      @*/
    public void registrarDevolucao(LocalDate data) {
        // CONDICIONAL 1: B1 = (data == null)
        // {P /\ B1} = {false} => throw (ramo then, vacuamente verdadeiro)
        if (data == null) {
            throw new IllegalArgumentException("Data de devolucao nao pode ser nula.");
        }
        // Aqui: {data != null /\ ...} -- ramo else do CONDICIONAL 1
        // CONDICIONAL 2: B2 = (dataDevolucao != null)
        // {data!=null /\ dataDevolucao!=null} => throw (ramo then)
        if (dataDevolucao != null) {
            throw new IllegalStateException("Emprestimo ja foi devolvido.");
        }
        // Aqui: {data != null /\ dataDevolucao==null /\ ...} -- ramo else do CONDICIONAL 2
        // CONDICIONAL 3: B3 = data.isBefore(dataEmprestimo)
        if (data.isBefore(dataEmprestimo)) {
            throw new IllegalArgumentException("Data de devolucao nao pode ser anterior ao emprestimo.");
        }
        // Aqui: Q0 = {data!=null /\ dataDevolucao==null /\ !data.isBefore(dataEmprestimo)}
        // Inicio da COMPOSICAO:
        // S1: {Q0}  this.dataDevolucao = data  {Q1: dataDevolucao.equals(data) /\ !livro.isDisponivel()}
        this.dataDevolucao = data;
        // S2: {Q1}  this.livro.devolver()  {Q2: dataDevolucao.equals(data) /\ livro.isDisponivel()}
        this.livro.devolver();
        // Q2 satisfeito por COMPOSICAO:
        assert this.livro.isDisponivel() : "Livro deve ficar disponivel apos devolucao.";
    }

    @Override
    /*@
      @ public normal_behavior
      @ ensures \result != null && !\result.isEmpty();
      @ pure
      @*/
    public String toString() {
        return "Emprestimo{livroId=" + livro.getId() + ", usuarioId=" + usuario.getId()
                + ", dataEmprestimo=" + dataEmprestimo + ", dataDevolucao=" + dataDevolucao + "}";
    }
}
