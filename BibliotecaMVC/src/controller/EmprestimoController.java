package controller;

import java.time.LocalDate;
import java.util.ArrayList;
import java.util.List;
import java.util.stream.Collectors;

import model.Emprestimo;
import model.Livro;
import model.Usuario;

// ---------------------------------------------------------------------------
// EMPRESTIMOCONTROLLER - Logica Aplicada a Engenharia de Software
//
// Propriedades invariantes do repositorio de emprestimos:
//
// (1) Nao-nulidade: forall e in emprestimos: e != null
//
// (2) Exclusao mutua de emprestimos ativos (unicidade por livro):
//     forall i,j in emprestimos, i!=j:
//       (isAtivo(i) /\ isAtivo(j)) -> livro(i).id != livro(j).id
//
// (3) Consistencia de disponibilidade:
//     forall e in emprestimos: e.isAtivo() -> !e.getLivro().isDisponivel()
//
// Regras de transicao:
//   emprestarLivro(l,u): (!isAtivo(l)) -> (isAtivo(l) /\ !livro.isDisponivel())
//   devolverLivro(l):    (isAtivo(l))  -> (!isAtivo(l) /\ livro.isDisponivel())
// ---------------------------------------------------------------------------
public class EmprestimoController {

    // Invariante (1): repositorio nao nulo e sem entradas nulas
    //@ public invariant livroController != null && usuarioController != null && emprestimos != null;
    //@ public invariant (\forall int i; 0 <= i && i < emprestimos.size(); emprestimos.get(i) != null);
    // Invariante (2): exclusao mutua -- nenhum livro pode ter dois emprestimos ativos
    //@ public invariant
    //@     (\forall int i; 0 <= i && i < emprestimos.size();
    //@         (\forall int j; 0 <= j && j < emprestimos.size() && i != j;
    //@             (emprestimos.get(i).isAtivo() && emprestimos.get(j).isAtivo())
    //@             ==> emprestimos.get(j).getLivro().getId() != emprestimos.get(i).getLivro().getId()));
    // Invariante (3): ativo ==> livro indisponivel
    //@ public invariant
    //@     (\forall int i; 0 <= i && i < emprestimos.size();
    //@         emprestimos.get(i).isAtivo() ==> !emprestimos.get(i).getLivro().isDisponivel());

    private final LivroController livroController;
    private final UsuarioController usuarioController;
    private final List<Emprestimo> emprestimos;

    /*@
      @ public normal_behavior
      @ requires livroController != null && usuarioController != null;
      @ assignable this.livroController, this.usuarioController, this.emprestimos;
      @ ensures this.livroController == livroController
      @      && this.usuarioController == usuarioController
      @      && this.emprestimos.isEmpty();
      @*/
    public EmprestimoController(LivroController livroController, UsuarioController usuarioController) {
        if (livroController == null || usuarioController == null) {
            throw new IllegalArgumentException("Controllers nao podem ser nulos.");
        }
        this.livroController = livroController;
        this.usuarioController = usuarioController;
        this.emprestimos = new ArrayList<>();
    }

    /*@
      @ // Tripla de Hoare:
      @ // {livro!=null /\ usuario!=null /\ livro.isDisponivel() /\ !isAtivo(livroId)}
      @ //   emprestarLivro(livroId, usuarioId)
      @ // {\result.isAtivo() /\ !livro.isDisponivel() /\ |emprestimos|==|old|+1}
      @ //
      @ // Pre-condicoes expressas como conjuncao de proposicoes:
      @ //   P1: livroController.buscarLivro(livroId) != null  (livro existe)
      @ //   P2: usuarioController.buscarUsuario(usuarioId) != null  (usuario existe)
      @ //   P3: livro.isDisponivel()  (livro livre)
      @ //   P4: !(exists e in emprestimos: e.isAtivo() /\ e.getLivro().getId()==livroId)
      @ //   Pre total: P1 /\ P2 /\ P3 /\ P4
      @ public normal_behavior
      @ requires livroId > 0 && usuarioId > 0;
      @ requires livroController.buscarLivro(livroId) != null;         // P1
      @ requires usuarioController.buscarUsuario(usuarioId) != null;   // P2
      @ requires livroController.buscarLivro(livroId).isDisponivel();  // P3
      @ requires !(\exists Emprestimo e; emprestimos.contains(e);       // P4 (negacao existencial)
      @            e.isAtivo() && e.getLivro().getId() == livroId);
      @ assignable emprestimos, livroController.*;
      @ // Pos-condicoes: conjuncao das garantias apos emprestimo
      @ ensures \result != null
      @      && emprestimos.contains(\result)
      @      && \result.isAtivo()
      @      && !\result.getLivro().isDisponivel();
      @ // Implicacao temporal: livro disponivel antes ==> indisponivel depois
      @ ensures \old(livroController.buscarLivro(livroId).isDisponivel())
      @         ==> !livroController.buscarLivro(livroId).isDisponivel();
      @ // Implicacao de cardinalidade
      @ ensures emprestimos.size() == \old(emprestimos.size()) + 1;
      @ // Existencial pos-condicao: existe exatamente um emprestimo ativo para o livro
      @ ensures (\exists Emprestimo e; emprestimos.contains(e);
      @          e.isAtivo() && e.getLivro().getId() == livroId);
      @ also
      @ // Caso excepcional: P1 \/ P2 \/ P3 \/ P4 falhou
      @ public exceptional_behavior
      @ requires livroController.buscarLivro(livroId) == null
      @       || usuarioController.buscarUsuario(usuarioId) == null
      @       || !livroController.buscarLivro(livroId).isDisponivel()
      @       || (\exists Emprestimo e; emprestimos.contains(e);
      @           e.isAtivo() && e.getLivro().getId() == livroId);
      @ assignable \nothing;
      @ signals (IllegalArgumentException e) true;
      @*/
    public Emprestimo emprestarLivro(int livroId, int usuarioId) {
        Livro livro = livroController.buscarLivro(livroId);
        if (livro == null) {
            throw new IllegalArgumentException("Livro inexistente.");
        }

        Usuario usuario = usuarioController.buscarUsuario(usuarioId);
        if (usuario == null) {
            throw new IllegalArgumentException("Usuario inexistente.");
        }

        if (!livro.isDisponivel()) {
            throw new IllegalArgumentException("Livro nao esta disponivel.");
        }

        if (possuiEmprestimoAtivo(livroId)) {
            throw new IllegalArgumentException("Livro ja possui emprestimo ativo.");
        }

        Emprestimo emprestimo = new Emprestimo(livro, usuario, LocalDate.now());
        emprestimos.add(emprestimo);

        assert !livro.isDisponivel();
        return emprestimo;
    }

    /*@
      @ // Tripla de Hoare:
      @ // {exists e in emprestimos: e.isAtivo() /\ e.getLivro().getId()==livroId}
      @ //   devolverLivro(livroId)
      @ // {livro.isDisponivel() /\ !(exists e ativo com livroId)}
      @ //
      @ // Pre-condicao: existencial -- ao menos um emprestimo ativo para o livro
      @ public normal_behavior
      @ requires livroId > 0;
      @ requires (\exists Emprestimo e; emprestimos.contains(e);
      @           e.isAtivo() && e.getLivro().getId() == livroId);
      @ assignable emprestimos, livroController.*;
      @ ensures \result != null && !\result.isAtivo();
      @ ensures livroController.buscarLivro(livroId) != null
      @      && livroController.buscarLivro(livroId).isDisponivel();
      @ // Implicacao temporal: havia ativo ==> agora disponivel
      @ ensures \old(\exists Emprestimo e; emprestimos.contains(e);
      @               e.isAtivo() && e.getLivro().getId() == livroId)
      @         ==> livroController.buscarLivro(livroId).isDisponivel();
      @ // Universalmente: nenhum emprestimo ativo para o livroId apos devolucao
      @ ensures (\forall Emprestimo e; emprestimos.contains(e)
      @           && e.getLivro().getId() == livroId; !e.isAtivo());
      @ also
      @ // {!(exists e ativo com livroId)}  devolverLivro(*)  {IllegalArgumentException}
      @ public exceptional_behavior
      @ requires !(\exists Emprestimo e; emprestimos.contains(e);
      @            e.isAtivo() && e.getLivro().getId() == livroId);
      @ assignable \nothing;
      @ signals (IllegalArgumentException e) true;
      @*/
    public Emprestimo devolverLivro(int livroId) {
        Emprestimo emprestimoAtivo = buscarEmprestimoAtivoPorLivro(livroId);
        if (emprestimoAtivo == null) {
            throw new IllegalArgumentException("Nao existe emprestimo ativo para este livro.");
        }

        emprestimoAtivo.registrarDevolucao(LocalDate.now());
        assert emprestimoAtivo.getLivro().isDisponivel();
        return emprestimoAtivo;
    }

    /*@
      @ public normal_behavior
      @ ensures \result != null && \result.size() == emprestimos.size();
      @ ensures (\forall int i; 0 <= i && i < \result.size();
      @         \result.get(i) != null && emprestimos.contains(\result.get(i)));
      @ pure
      @*/
    public List<Emprestimo> listarEmprestimos() {
        return new ArrayList<>(emprestimos);
    }

    /*@
      @ public normal_behavior
      @ ensures \result != null;
      @ // Todo elemento na lista e ativo:
      @ ensures (\forall int i; 0 <= i && i < \result.size(); \result.get(i).isAtivo());
      @ // Completude: todo ativo do repositorio esta na lista
      @ ensures (\forall int i; 0 <= i && i < emprestimos.size();
      @         emprestimos.get(i).isAtivo() ==> \result.contains(emprestimos.get(i)));
      @ pure
      @*/
    public List<Emprestimo> listarEmprestimosAtivos() {
        return emprestimos.stream().filter(Emprestimo::isAtivo).collect(Collectors.toList());
    }

    /*@
      @ public normal_behavior
      @ ensures \result != null;
      @ // Todo elemento retornado e disponivel:
      @ ensures (\forall int i; 0 <= i && i < \result.size(); \result.get(i).isDisponivel());
      @ // Completude: todo livro disponivel esta na lista:
      @ ensures (\forall Livro l; livroController.listarLivros().contains(l);
      @         l.isDisponivel() ==> \result.contains(l));
      @ pure
      @*/
    public List<Livro> listarLivrosDisponiveis() {
        return livroController.listarLivros().stream().filter(Livro::isDisponivel).collect(Collectors.toList());
    }

    /*@
      @ public normal_behavior
      @ ensures \result != null;
      @ // Todo elemento retornado esta indisponivel:
      @ ensures (\forall int i; 0 <= i && i < \result.size(); !\result.get(i).isDisponivel());
      @ pure
      @*/
    public List<Livro> listarLivrosEmprestados() {
        return livroController.listarLivros().stream().filter(l -> !l.isDisponivel()).collect(Collectors.toList());
    }

    /*@
      @ // Bicondicional completo:
      @ // possuiEmprestimoAtivo(id) <=> exists e in emprestimos: e.isAtivo() /\ e.getLivro().getId()==id
      @ public normal_behavior
      @ requires livroId > 0;
      @ ensures \result <==> (\exists Emprestimo e; emprestimos.contains(e);
      @                       e.isAtivo() && e.getLivro().getId() == livroId);
      @ pure
      @*/
    public boolean possuiEmprestimoAtivo(int livroId) {
        return buscarEmprestimoAtivoPorLivro(livroId) != null;
    }

    /*@
      @ // ================================================================
      @ // REGRA DO WHILE (Loop Invariant Rule):
      @ //   {I /\ B}  corpo  {I}
      @ //   ────────────────────────────────────────────────────────────
      @ //   {I}  while B do corpo  {I /\ !B}
      @ //
      @ // O for-each abaixo e equivalente a um while sobre o iterador.
      @ // Seja 'i' o indice do proximo elemento a ser visitado (0-based).
      @ //
      @ // INVARIANTE DE LOOP I(i):
      @ //   I(i) = (resultado == null) ==>
      @ //            !(\exists int k; 0 <= k && k < i;
      @ //                emprestimos.get(k).isAtivo()
      @ //              /\ emprestimos.get(k).getLivro().getId() == livroId)
      @ //
      @ //   Leitura: se ainda nao encontramos (resultado==null),
      @ //            nenhum elemento nos indices 0..i-1 satisfaz a condicao.
      @ //
      @ // Prova de que I e invariante:
      @ //   {I(i) /\ B}  corpo  {I(i+1)}
      @ //   B = (i < emprestimos.size())
      @ //   Corpo:
      @ //     CONDICIONAL: B_c = emprestimos.get(i).isAtivo() /\ getId()==livroId
      @ //     Ramo then (B_c verdadeiro): retorna emprestimo -> sai do loop
      @ //       resultado = emprestimos.get(i) != null -> pos-condicao final satisfeita
      @ //     Ramo else (!B_c): elemento i nao satisfaz condicao
      @ //       I(i+1) = (resultado==null) ==> !(\exists k; 0<=k<i+1; ...)
      @ //       Como !B_c, o elemento i nao satisfaz; por I(i) os anteriores tambem nao.
      @ //       Logo I(i+1) preservado.
      @ //
      @ // POS-CONDICAO DO WHILE: {I /\ !B}
      @ //   !B = (i == emprestimos.size()) -> todos os elementos visitados
      @ //   I /\ !B:
      @ //     (resultado == null) ==> nenhum e em emprestimos satisfaz a condicao
      @ //   Portanto: return null  satisfaz  (resultado==null) <==> !(\exists ...)
      @ // ================================================================
      @ private normal_behavior
      @ requires livroId > 0;
      @ // Invariante de loop como pos-condicao (estado apos o while):
      @ //   I /\ !B  =>  resultado<=>busca
      @ ensures (\result == null) <==> !(\exists Emprestimo e; emprestimos.contains(e);
      @                                  e.isAtivo() && e.getLivro().getId() == livroId);
      @ ensures (\result != null) ==> (\result.isAtivo() && \result.getLivro().getId() == livroId);
      @ pure
      @*/
    private Emprestimo buscarEmprestimoAtivoPorLivro(int livroId) {
        // INVARIANTE de loop I(0): (resultado==null) ==> !(\exists k; 0<=k<0; ...) = true (vacuo)
        for (Emprestimo emprestimo : emprestimos) {
            // {I(i) /\ B}  -- inicio do corpo do loop
            // CONDICIONAL: B_c = isAtivo() /\ getId()==livroId
            if (emprestimo.isAtivo() && emprestimo.getLivro().getId() == livroId) {
                // Ramo then: encontrou -- pos-condicao satisfeita (resultado != null)
                return emprestimo;
            }
            // Ramo else: !B_c -- elemento nao satisfaz, invariante I(i+1) preservada
        }
        // {I(n) /\ !B}  com n = emprestimos.size()
        // Nenhum elemento satisfaz a condicao => return null (resultado==null) <==> !(\exists ...)
        return null;
    }
}
