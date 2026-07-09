package controller;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import model.Usuario;

// ---------------------------------------------------------------------------
// USUARIOCONTROLLER - Logica Aplicada a Engenharia de Software
//
// Propriedades do repositorio de usuarios:
//
// (1) Consistencia de id:
//     forall k in usuariosPorId.keySet():
//       usuariosPorId.get(k) != null  /\  usuariosPorId.get(k).getId() == k
//
// (2) Bijecao id <-> matricula:
//     forall k in usuariosPorId.keySet():
//       usuariosPorMatricula.get(usuariosPorId.get(k).getMatricula()) == usuariosPorId.get(k)
//
// (3) Unicidade de matricula:
//     forall a,b in usuariosPorId.keySet(), a!=b:
//       usuariosPorId.get(a).getMatricula() != usuariosPorId.get(b).getMatricula()
//
// (4) Tamanho consistente: |usuariosPorId| == |usuariosPorMatricula|
// ---------------------------------------------------------------------------
public class UsuarioController {

    // Invariante (1): repositorio nao nulo e sem entradas nulas
    //@ public invariant usuariosPorId != null && usuariosPorMatricula != null;
    //@ public invariant (\forall Integer k; usuariosPorId.containsKey(k);
    //@         usuariosPorId.get(k) != null && usuariosPorId.get(k).getId() == k.intValue());
    // Invariante (2): bijecao id <-> matricula
    //@ public invariant (\forall Integer k; usuariosPorId.containsKey(k);
    //@         usuariosPorMatricula.get(usuariosPorId.get(k).getMatricula()) == usuariosPorId.get(k));
    // Invariante (3): unicidade de matricula entre usuarios distintos
    //@ public invariant
    //@     (\forall Integer a; usuariosPorId.containsKey(a);
    //@         (\forall Integer b; usuariosPorId.containsKey(b) && !a.equals(b);
    //@             !usuariosPorId.get(a).getMatricula().equals(usuariosPorId.get(b).getMatricula())));
    // Invariante (4): tamanho consistente
    //@ public invariant usuariosPorId.size() == usuariosPorMatricula.size();

    private final Map<Integer, Usuario> usuariosPorId;
    private final Map<String, Usuario> usuariosPorMatricula;

    /*@
      @ // {true}  UsuarioController()  {usuariosPorId.isEmpty() /\ usuariosPorMatricula.isEmpty()}
      @ public normal_behavior
      @ assignable this.usuariosPorId, this.usuariosPorMatricula;
      @ ensures usuariosPorId.isEmpty() && usuariosPorMatricula.isEmpty();
      @*/
    public UsuarioController() {
        this.usuariosPorId = new HashMap<>();
        this.usuariosPorMatricula = new HashMap<>();
    }

    /*@
      @ // Tripla de Hoare:
      @ // {usuario!=null /\ !contains(id) /\ !contains(matricula)}
      @ //   cadastrarUsuario(usuario)
      @ // {contains(id) /\ contains(matricula) /\ |usuariosPorId|==|old|+1}
      @ public normal_behavior
      @ requires usuario != null;
      @ requires !usuariosPorId.containsKey(usuario.getId());              // unicidade de id
      @ requires !usuariosPorMatricula.containsKey(usuario.getMatricula()); // unicidade de matricula
      @ assignable usuariosPorId, usuariosPorMatricula;
      @ ensures usuariosPorId.get(usuario.getId()) == usuario
      @      && usuariosPorMatricula.get(usuario.getMatricula()) == usuario;
      @ // Implicacao: pre satisfeita ==> tamanho cresce exatamente 1
      @ ensures usuariosPorId.size() == \old(usuariosPorId.size()) + 1;
      @ // Implicacao: demais registros preservados
      @ ensures (\forall Integer k; \old(usuariosPorId.containsKey(k));
      @         usuariosPorId.get(k) == \old(usuariosPorId.get(k)));
      @ also
      @ // Caso excepcional: usuario==null \/ id duplicado \/ matricula duplicada
      @ public exceptional_behavior
      @ requires usuario == null
      @       || usuariosPorId.containsKey(usuario.getId())
      @       || usuariosPorMatricula.containsKey(usuario.getMatricula());
      @ assignable \nothing;
      @ signals (IllegalArgumentException e) true;
      @*/
    public void cadastrarUsuario(Usuario usuario) {
        if (usuario == null) {
            throw new IllegalArgumentException("Usuario nao pode ser nulo.");
        }
        if (usuariosPorId.containsKey(usuario.getId())) {
            throw new IllegalArgumentException("Ja existe usuario com o mesmo id.");
        }
        if (usuariosPorMatricula.containsKey(usuario.getMatricula())) {
            throw new IllegalArgumentException("Ja existe usuario com a mesma matricula.");
        }

        usuariosPorId.put(usuario.getId(), usuario);
        usuariosPorMatricula.put(usuario.getMatricula(), usuario);

        assert usuariosPorId.containsKey(usuario.getId());
        assert usuariosPorMatricula.containsKey(usuario.getMatricula());
    }

    /*@
      @ // Bicondicional: \result!=null <=> usuariosPorId.containsKey(id)
      @ public normal_behavior
      @ requires id > 0;
      @ ensures \result == usuariosPorId.get(id);
      @ ensures (\result != null) <==> usuariosPorId.containsKey(id);
      @ pure
      @*/
    public Usuario buscarUsuario(int id) {
        return usuariosPorId.get(id);
    }

    /*@
      @ // Bicondicional: \result!=null <=> usuariosPorMatricula.containsKey(matricula)
      @ public normal_behavior
      @ requires matricula != null;
      @ ensures \result == usuariosPorMatricula.get(matricula);
      @ ensures (\result != null) <==> usuariosPorMatricula.containsKey(matricula);
      @ pure
      @*/
    public Usuario buscarUsuarioPorMatricula(String matricula) {
        return usuariosPorMatricula.get(matricula);
    }

    /*@
      @ public normal_behavior
      @ ensures \result != null;
      @ ensures \result.size() == usuariosPorId.size();
      @ ensures (\forall int i; 0 <= i && i < \result.size();
      @         \result.get(i) != null && usuariosPorId.containsKey(\result.get(i).getId()));
      @ pure
      @*/
    public List<Usuario> listarUsuarios() {
        return new ArrayList<>(usuariosPorId.values());
    }

    /*@
      @ // Tripla de Hoare:
      @ // {usuarioAtualizado!=null /\ contains(id) /\ (matricula unica ou mesmo dono)}
      @ //   atualizarUsuario(usuarioAtualizado)
      @ // {usuariosPorId[id]==usuarioAtualizado /\ |usuariosPorId|==|old|}
      @ public normal_behavior
      @ requires usuarioAtualizado != null;
      @ requires usuariosPorId.containsKey(usuarioAtualizado.getId());
      @ // Disjuncao de unicidade: matricula nova nao existe \/ pertence ao mesmo usuario
      @ requires !usuariosPorMatricula.containsKey(usuarioAtualizado.getMatricula())
      @       || usuariosPorMatricula.get(usuarioAtualizado.getMatricula()).getId() == usuarioAtualizado.getId();
      @ assignable usuariosPorId, usuariosPorMatricula;
      @ ensures usuariosPorId.get(usuarioAtualizado.getId()) == usuarioAtualizado;
      @ ensures usuariosPorMatricula.get(usuarioAtualizado.getMatricula()) == usuarioAtualizado;
      @ ensures usuariosPorId.size() == \old(usuariosPorId.size());
      @ also
      @ public exceptional_behavior
      @ requires usuarioAtualizado == null
      @       || !usuariosPorId.containsKey(usuarioAtualizado.getId())
      @       || (usuariosPorMatricula.containsKey(usuarioAtualizado.getMatricula())
      @          && usuariosPorMatricula.get(usuarioAtualizado.getMatricula()).getId() != usuarioAtualizado.getId());
      @ assignable \nothing;
      @ signals (IllegalArgumentException e) true;
      @*/
    public void atualizarUsuario(Usuario usuarioAtualizado) {
        if (usuarioAtualizado == null) {
            throw new IllegalArgumentException("Usuario atualizado nao pode ser nulo.");
        }
        Usuario existente = usuariosPorId.get(usuarioAtualizado.getId());
        if (existente == null) {
            throw new IllegalArgumentException("Usuario nao encontrado para atualizacao.");
        }

        Usuario conflito = usuariosPorMatricula.get(usuarioAtualizado.getMatricula());
        if (conflito != null && conflito.getId() != usuarioAtualizado.getId()) {
            throw new IllegalArgumentException("Matricula ja cadastrada para outro usuario.");
        }

        usuariosPorMatricula.remove(existente.getMatricula());
        usuariosPorId.put(usuarioAtualizado.getId(), usuarioAtualizado);
        usuariosPorMatricula.put(usuarioAtualizado.getMatricula(), usuarioAtualizado);

        assert usuariosPorId.get(usuarioAtualizado.getId()) == usuarioAtualizado;
    }

    /*@
      @ // Tripla de Hoare:
      @ // {contains(id)}  removerUsuario(id)  {!contains(id) /\ \result==true}
      @ public normal_behavior
      @ requires id > 0;
      @ requires usuariosPorId.containsKey(id);
      @ assignable usuariosPorId, usuariosPorMatricula;
      @ ensures !usuariosPorId.containsKey(id);
      @ ensures (\forall String m; usuariosPorMatricula.containsKey(m);
      @         usuariosPorMatricula.get(m).getId() != id);
      @ ensures \result;
      @ ensures usuariosPorId.size() == \old(usuariosPorId.size()) - 1;
      @ also
      @ public exceptional_behavior
      @ requires !usuariosPorId.containsKey(id);
      @ assignable \nothing;
      @ signals (IllegalArgumentException e) true;
      @*/
    public boolean removerUsuario(int id) {
        Usuario usuario = usuariosPorId.get(id);
        if (usuario == null) {
            throw new IllegalArgumentException("Usuario nao encontrado para remocao.");
        }

        usuariosPorId.remove(id);
        usuariosPorMatricula.remove(usuario.getMatricula());

        return true;
    }
}
