package controller;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import model.Livro;

// ---------------------------------------------------------------------------
// LIVROCONTROLLER - Logica Aplicada a Engenharia de Software
//
// Propriedades do repositorio de livros:
//
// (1) Consistencia de id:
//     forall k in livrosPorId.keySet():
//       livrosPorId.get(k) != null  /\  livrosPorId.get(k).getId() == k
//
// (2) Bijecao id <-> isbn:
//     forall k in livrosPorId.keySet():
//       livrosPorIsbn.get(livrosPorId.get(k).getIsbn()) == livrosPorId.get(k)
//
// (3) Unicidade de ISBN (sem repeticao entre livros distintos):
//     forall a,b in livrosPorId.keySet(), a!=b:
//       livrosPorId.get(a).getIsbn() != livrosPorId.get(b).getIsbn()
//
// (4) Consistencia de tamanho: |livrosPorId| == |livrosPorIsbn|
// ---------------------------------------------------------------------------
public class LivroController {

    // Invariante (1): repositorio nao nulo e sem entradas nulas
    //@ public invariant livrosPorId != null && livrosPorIsbn != null;
    //@ public invariant (\forall Integer k; livrosPorId.containsKey(k);
    //@         livrosPorId.get(k) != null && livrosPorId.get(k).getId() == k.intValue());
    // Invariante (2): bijecao id <-> isbn
    //@ public invariant (\forall Integer k; livrosPorId.containsKey(k);
    //@         livrosPorIsbn.get(livrosPorId.get(k).getIsbn()) == livrosPorId.get(k));
    // Invariante (3): unicidade de ISBN entre livros distintos
    //@ public invariant
    //@     (\forall Integer a; livrosPorId.containsKey(a);
    //@         (\forall Integer b; livrosPorId.containsKey(b) && !a.equals(b);
    //@             !livrosPorId.get(a).getIsbn().equals(livrosPorId.get(b).getIsbn())));
    // Invariante (4): tamanho consistente
    //@ public invariant livrosPorId.size() == livrosPorIsbn.size();

    private final Map<Integer, Livro> livrosPorId;
    private final Map<String, Livro> livrosPorIsbn;

    /*@
      @ // {true}  LivroController()  {livrosPorId.isEmpty() /\ livrosPorIsbn.isEmpty()}
      @ public normal_behavior
      @ assignable this.livrosPorId, this.livrosPorIsbn;
      @ ensures livrosPorId.isEmpty() && livrosPorIsbn.isEmpty();
      @ ensures livrosPorId.size() == 0 && livrosPorIsbn.size() == 0;
      @*/
    public LivroController() {
        this.livrosPorId = new HashMap<>();
        this.livrosPorIsbn = new HashMap<>();
    }

    /*@
      @ // Tripla de Hoare:
      @ // {livro!=null /\ !contains(id) /\ !contains(isbn)}
      @ //   cadastrarLivro(livro)
      @ // {contains(id) /\ contains(isbn) /\ |livrosPorId|==|old|+1}
      @ public normal_behavior
      @ requires livro != null;
      @ requires !livrosPorId.containsKey(livro.getId());      // unicidade de id
      @ requires !livrosPorIsbn.containsKey(livro.getIsbn()); // unicidade de ISBN
      @ assignable livrosPorId, livrosPorIsbn;
      @ // Pos-condicoes: conjuncao das garantias apos insercao
      @ ensures livrosPorId.get(livro.getId()) == livro
      @      && livrosPorIsbn.get(livro.getIsbn()) == livro;
      @ // Implicacao: pre satisfeita ==> tamanho cresce exatamente 1
      @ ensures livrosPorId.size() == \old(livrosPorId.size()) + 1
      @      && livrosPorIsbn.size() == \old(livrosPorIsbn.size()) + 1;
      @ // Implicacao: todos os demais registros permanecem intactos
      @ ensures (\forall Integer k; \old(livrosPorId.containsKey(k));
      @         livrosPorId.get(k) == \old(livrosPorId.get(k)));
      @ also
      @ // Caso excepcional: livro==null \/ id duplicado \/ ISBN duplicado
      @ public exceptional_behavior
      @ requires livro == null
      @       || livrosPorId.containsKey(livro.getId())
      @       || livrosPorIsbn.containsKey(livro.getIsbn());
      @ assignable \nothing;
      @ signals (IllegalArgumentException e) true;
      @*/
    public void cadastrarLivro(Livro livro) {
        if (livro == null) {
            throw new IllegalArgumentException("Livro nao pode ser nulo.");
        }
        if (livrosPorId.containsKey(livro.getId())) {
            throw new IllegalArgumentException("Ja existe livro com o mesmo id.");
        }
        if (livrosPorIsbn.containsKey(livro.getIsbn())) {
            throw new IllegalArgumentException("Ja existe livro com o mesmo ISBN.");
        }

        livrosPorId.put(livro.getId(), livro);
        livrosPorIsbn.put(livro.getIsbn(), livro);

        assert livrosPorId.containsKey(livro.getId());
        assert livrosPorIsbn.containsKey(livro.getIsbn());
    }

    /*@
      @ // Bicondicional de busca: \result!=null <=> livrosPorId.containsKey(id)
      @ public normal_behavior
      @ requires id > 0;
      @ ensures \result == livrosPorId.get(id);
      @ ensures (\result != null) <==> livrosPorId.containsKey(id);
      @ pure
      @*/
    public Livro buscarLivro(int id) {
        return livrosPorId.get(id);
    }

    /*@
      @ public normal_behavior
      @ ensures \result != null;
      @ ensures \result.size() == livrosPorId.size();
      @ // Todo elemento da lista provem do mapa e nao e nulo:
      @ ensures (\forall int i; 0 <= i && i < \result.size();
      @         \result.get(i) != null && livrosPorId.containsKey(\result.get(i).getId()));
      @ pure
      @*/
    public List<Livro> listarLivros() {
        return new ArrayList<>(livrosPorId.values());
    }

    /*@
      @ // Tripla de Hoare:
      @ // {livroAtualizado!=null /\ contains(id) /\ (isbn unico ou mesmo dono)}
      @ //   atualizarLivro(livroAtualizado)
      @ // {livrosPorId[id]==livroAtualizado /\ |livrosPorId|==|old|}
      @ public normal_behavior
      @ requires livroAtualizado != null;
      @ requires livrosPorId.containsKey(livroAtualizado.getId());
      @ // Unicidade de ISBN pos-atualizacao (disjuncao):
      @ // ISBN novo nao existe \/ (existe mas pertence ao mesmo id)
      @ requires !livrosPorIsbn.containsKey(livroAtualizado.getIsbn())
      @       || livrosPorIsbn.get(livroAtualizado.getIsbn()).getId() == livroAtualizado.getId();
      @ assignable livrosPorId, livrosPorIsbn;
      @ ensures livrosPorId.get(livroAtualizado.getId()) == livroAtualizado;
      @ ensures livrosPorIsbn.get(livroAtualizado.getIsbn()) == livroAtualizado;
      @ // Implicacao: tamanho preservado (atualizacao nao e insercao)
      @ ensures livrosPorId.size() == \old(livrosPorId.size());
      @ also
      @ public exceptional_behavior
      @ requires livroAtualizado == null
      @       || !livrosPorId.containsKey(livroAtualizado.getId())
      @       || (livrosPorIsbn.containsKey(livroAtualizado.getIsbn())
      @          && livrosPorIsbn.get(livroAtualizado.getIsbn()).getId() != livroAtualizado.getId());
      @ assignable \nothing;
      @ signals (IllegalArgumentException e) true;
      @*/
    public void atualizarLivro(Livro livroAtualizado) {
        if (livroAtualizado == null) {
            throw new IllegalArgumentException("Livro atualizado nao pode ser nulo.");
        }
        Livro existente = livrosPorId.get(livroAtualizado.getId());
        if (existente == null) {
            throw new IllegalArgumentException("Livro nao encontrado para atualizacao.");
        }

        Livro conflitoIsbn = livrosPorIsbn.get(livroAtualizado.getIsbn());
        if (conflitoIsbn != null && conflitoIsbn.getId() != livroAtualizado.getId()) {
            throw new IllegalArgumentException("ISBN ja cadastrado para outro livro.");
        }

        livrosPorIsbn.remove(existente.getIsbn());
        livrosPorId.put(livroAtualizado.getId(), livroAtualizado);
        livrosPorIsbn.put(livroAtualizado.getIsbn(), livroAtualizado);

        assert livrosPorId.get(livroAtualizado.getId()) == livroAtualizado;
    }

    /*@
      @ // Tripla de Hoare:
      @ // {contains(id) /\ livro.isDisponivel()}  removerLivro(id)  {!contains(id) /\ \result==true}
      @ public normal_behavior
      @ requires id > 0;
      @ requires livrosPorId.containsKey(id);
      @ requires livrosPorId.get(id).isDisponivel(); // livro disponivel ==> remocao permitida
      @ assignable livrosPorId, livrosPorIsbn;
      @ ensures !livrosPorId.containsKey(id);
      @ // Implicacao universal: nenhum livro restante tem o id removido
      @ ensures (\forall String k; livrosPorIsbn.containsKey(k);
      @         livrosPorIsbn.get(k).getId() != id);
      @ ensures \result;
      @ // Implicacao: tamanho decresce exatamente 1
      @ ensures livrosPorId.size() == \old(livrosPorId.size()) - 1;
      @ also
      @ // Caso excepcional: id nao existe \/ livro esta emprestado
      @ public exceptional_behavior
      @ requires !livrosPorId.containsKey(id)
      @       || (livrosPorId.containsKey(id) && !livrosPorId.get(id).isDisponivel());
      @ assignable \nothing;
      @ signals (IllegalArgumentException e) true;
      @*/
    public boolean removerLivro(int id) {
        Livro livro = livrosPorId.get(id);
        if (livro == null) {
            throw new IllegalArgumentException("Livro nao encontrado para remocao.");
        }
        if (!livro.isDisponivel()) {
            throw new IllegalArgumentException("Nao e permitido remover livro emprestado.");
        }

        livrosPorId.remove(id);
        livrosPorIsbn.remove(livro.getIsbn());

        return true;
    }

    /*@
      @ // Bicondicional: \result!=null <=> livrosPorIsbn.containsKey(isbn)
      @ public normal_behavior
      @ requires isbn != null;
      @ ensures \result == livrosPorIsbn.get(isbn);
      @ ensures (\result != null) <==> livrosPorIsbn.containsKey(isbn);
      @ pure
      @*/
    public Livro buscarLivroPorIsbn(String isbn) {
        return livrosPorIsbn.get(isbn);
    }
}
