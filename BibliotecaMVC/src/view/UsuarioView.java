package view;

import java.util.List;
import java.util.Scanner;

import controller.UsuarioController;
import model.Usuario;

public class UsuarioView {

        //@ public invariant scanner != null;
        //@ public invariant usuarioController != null;

    private final Scanner scanner;
    private final UsuarioController usuarioController;

        /*@
            @ public normal_behavior
            @ requires scanner != null;
            @ requires usuarioController != null;
            @ assignable this.scanner, this.usuarioController;
            @ ensures this.scanner == scanner;
            @ ensures this.usuarioController == usuarioController;
            @*/
    public UsuarioView(Scanner scanner, UsuarioController usuarioController) {
        this.scanner = scanner;
        this.usuarioController = usuarioController;
    }

        /*@
            @ public normal_behavior
            @ assignable \nothing;
            @ ensures true;
            @ signals (Exception e) false;
            @*/
    public void cadastrarUsuario() {
        try {
            System.out.print("Id do usuario: ");
            int id = Integer.parseInt(scanner.nextLine());

            System.out.print("Nome: ");
            String nome = scanner.nextLine();

            System.out.print("Matricula: ");
            String matricula = scanner.nextLine();

            System.out.print("Email: ");
            String email = scanner.nextLine();

            Usuario usuario = new Usuario(id, nome, matricula, email);
            usuarioController.cadastrarUsuario(usuario);
            System.out.println("Usuario cadastrado com sucesso.");
        } catch (Exception e) {
            System.out.println("Erro ao cadastrar usuario: " + e.getMessage());
        }
    }

        /*@
            @ public normal_behavior
            @ assignable \nothing;
            @ ensures true;
            @*/
    public void listarUsuarios() {
        List<Usuario> usuarios = usuarioController.listarUsuarios();
        if (usuarios.isEmpty()) {
            System.out.println("Nenhum usuario cadastrado.");
            return;
        }

        System.out.println("Usuarios cadastrados:");
        for (Usuario usuario : usuarios) {
            System.out.println(usuario);
        }
    }
}
