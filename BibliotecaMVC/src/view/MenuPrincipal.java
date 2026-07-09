package view;

import java.util.Scanner;

public class MenuPrincipal {

        //@ public invariant scanner != null;
        //@ public invariant livroView != null;
        //@ public invariant usuarioView != null;
        //@ public invariant emprestimoView != null;

    private final Scanner scanner;
    private final LivroView livroView;
    private final UsuarioView usuarioView;
    private final EmprestimoView emprestimoView;

        /*@
            @ public normal_behavior
            @ requires scanner != null;
            @ requires livroView != null;
            @ requires usuarioView != null;
            @ requires emprestimoView != null;
            @ assignable this.scanner, this.livroView, this.usuarioView, this.emprestimoView;
            @ ensures this.scanner == scanner;
            @ ensures this.livroView == livroView;
            @ ensures this.usuarioView == usuarioView;
            @ ensures this.emprestimoView == emprestimoView;
            @*/
    public MenuPrincipal(Scanner scanner, LivroView livroView, UsuarioView usuarioView, EmprestimoView emprestimoView) {
        this.scanner = scanner;
        this.livroView = livroView;
        this.usuarioView = usuarioView;
        this.emprestimoView = emprestimoView;
    }

        /*@
            @ public normal_behavior
            @ assignable \nothing;
            @ ensures true;
            @*/
    public void iniciar() {
        int opcao = -1;

        while (opcao != 8) {
            exibirMenu();
            try {
                opcao = Integer.parseInt(scanner.nextLine());
                executarOpcao(opcao);
            } catch (NumberFormatException e) {
                System.out.println("Opcao invalida. Digite um numero de 1 a 8.");
            }
        }
    }

        /*@
            @ private normal_behavior
            @ assignable \nothing;
            @ ensures true;
            @*/
    private void exibirMenu() {
        System.out.println("\n=== Sistema de Gerenciamento de Biblioteca ===");
        System.out.println("1. Cadastrar livro");
        System.out.println("2. Cadastrar usuario");
        System.out.println("3. Emprestar livro");
        System.out.println("4. Devolver livro");
        System.out.println("5. Listar livros");
        System.out.println("6. Listar usuarios");
        System.out.println("7. Listar emprestimos");
        System.out.println("8. Sair");
        System.out.print("Escolha uma opcao: ");
    }

        /*@
            @ private normal_behavior
            @ requires true;
            @ assignable \nothing;
            @ ensures true;
            @*/
    private void executarOpcao(int opcao) {
        switch (opcao) {
            case 1:
                livroView.cadastrarLivro();
                break;
            case 2:
                usuarioView.cadastrarUsuario();
                break;
            case 3:
                emprestimoView.emprestarLivro();
                break;
            case 4:
                emprestimoView.devolverLivro();
                break;
            case 5:
                livroView.listarLivros();
                System.out.println();
                emprestimoView.listarLivrosDisponiveis();
                System.out.println();
                emprestimoView.listarLivrosEmprestados();
                break;
            case 6:
                usuarioView.listarUsuarios();
                break;
            case 7:
                emprestimoView.listarEmprestimos();
                System.out.println();
                emprestimoView.listarEmprestimosAtivos();
                break;
            case 8:
                System.out.println("Encerrando o sistema.");
                break;
            default:
                System.out.println("Opcao invalida. Digite um numero de 1 a 8.");
        }
    }
}
