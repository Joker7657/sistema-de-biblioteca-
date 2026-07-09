package view;

import java.util.List;
import java.util.Scanner;

import controller.LivroController;
import model.Livro;

public class LivroView {

        //@ public invariant scanner != null;
        //@ public invariant livroController != null;

    private final Scanner scanner;
    private final LivroController livroController;

        /*@
            @ public normal_behavior
            @ requires scanner != null;
            @ requires livroController != null;
            @ assignable this.scanner, this.livroController;
            @ ensures this.scanner == scanner;
            @ ensures this.livroController == livroController;
            @*/
    public LivroView(Scanner scanner, LivroController livroController) {
        this.scanner = scanner;
        this.livroController = livroController;
    }

        /*@
            @ public normal_behavior
            @ assignable \nothing;
            @ ensures true;
            @ signals (Exception e) false;
            @*/
    public void cadastrarLivro() {
        try {
            System.out.print("Id do livro: ");
            int id = Integer.parseInt(scanner.nextLine());

            System.out.print("Titulo: ");
            String titulo = scanner.nextLine();

            System.out.print("Autor: ");
            String autor = scanner.nextLine();

            System.out.print("ISBN: ");
            String isbn = scanner.nextLine();

            Livro livro = new Livro(id, titulo, autor, isbn);
            livroController.cadastrarLivro(livro);
            System.out.println("Livro cadastrado com sucesso.");
        } catch (Exception e) {
            System.out.println("Erro ao cadastrar livro: " + e.getMessage());
        }
    }

        /*@
            @ public normal_behavior
            @ assignable \nothing;
            @ ensures true;
            @*/
    public void listarLivros() {
        List<Livro> livros = livroController.listarLivros();
        if (livros.isEmpty()) {
            System.out.println("Nenhum livro cadastrado.");
            return;
        }

        System.out.println("Livros cadastrados:");
        for (Livro livro : livros) {
            System.out.println(livro);
        }
    }
}
