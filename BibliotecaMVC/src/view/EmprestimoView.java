package view;

import java.util.List;
import java.util.Scanner;

import controller.EmprestimoController;
import model.Emprestimo;

public class EmprestimoView {

        //@ public invariant scanner != null;
        //@ public invariant emprestimoController != null;

    private final Scanner scanner;
    private final EmprestimoController emprestimoController;

        /*@
            @ public normal_behavior
            @ requires scanner != null;
            @ requires emprestimoController != null;
            @ assignable this.scanner, this.emprestimoController;
            @ ensures this.scanner == scanner;
            @ ensures this.emprestimoController == emprestimoController;
            @*/
    public EmprestimoView(Scanner scanner, EmprestimoController emprestimoController) {
        this.scanner = scanner;
        this.emprestimoController = emprestimoController;
    }

        /*@
            @ public normal_behavior
            @ assignable \nothing;
            @ ensures true;
            @ signals (Exception e) false;
            @*/
    public void emprestarLivro() {
        try {
            System.out.print("Id do livro: ");
            int livroId = Integer.parseInt(scanner.nextLine());

            System.out.print("Id do usuario: ");
            int usuarioId = Integer.parseInt(scanner.nextLine());

            emprestimoController.emprestarLivro(livroId, usuarioId);
            System.out.println("Emprestimo realizado com sucesso.");
        } catch (Exception e) {
            System.out.println("Erro ao emprestar livro: " + e.getMessage());
        }
    }

        /*@
            @ public normal_behavior
            @ assignable \nothing;
            @ ensures true;
            @ signals (Exception e) false;
            @*/
    public void devolverLivro() {
        try {
            System.out.print("Id do livro para devolucao: ");
            int livroId = Integer.parseInt(scanner.nextLine());

            emprestimoController.devolverLivro(livroId);
            System.out.println("Devolucao realizada com sucesso.");
        } catch (Exception e) {
            System.out.println("Erro ao devolver livro: " + e.getMessage());
        }
    }

        /*@
            @ public normal_behavior
            @ assignable \nothing;
            @ ensures true;
            @*/
    public void listarEmprestimos() {
        List<Emprestimo> emprestimos = emprestimoController.listarEmprestimos();
        if (emprestimos.isEmpty()) {
            System.out.println("Nenhum emprestimo registrado.");
            return;
        }

        System.out.println("Emprestimos registrados:");
        for (Emprestimo emprestimo : emprestimos) {
            System.out.println(emprestimo);
        }
    }

        /*@
            @ public normal_behavior
            @ assignable \nothing;
            @ ensures true;
            @*/
    public void listarLivrosDisponiveis() {
        if (emprestimoController.listarLivrosDisponiveis().isEmpty()) {
            System.out.println("Nenhum livro disponivel.");
            return;
        }
        System.out.println("Livros disponiveis:");
        emprestimoController.listarLivrosDisponiveis().forEach(System.out::println);
    }

        /*@
            @ public normal_behavior
            @ assignable \nothing;
            @ ensures true;
            @*/
    public void listarLivrosEmprestados() {
        if (emprestimoController.listarLivrosEmprestados().isEmpty()) {
            System.out.println("Nenhum livro emprestado.");
            return;
        }
        System.out.println("Livros emprestados:");
        emprestimoController.listarLivrosEmprestados().forEach(System.out::println);
    }

        /*@
            @ public normal_behavior
            @ assignable \nothing;
            @ ensures true;
            @*/
    public void listarEmprestimosAtivos() {
        if (emprestimoController.listarEmprestimosAtivos().isEmpty()) {
            System.out.println("Nenhum emprestimo ativo.");
            return;
        }
        System.out.println("Emprestimos ativos:");
        emprestimoController.listarEmprestimosAtivos().forEach(System.out::println);
    }
}
