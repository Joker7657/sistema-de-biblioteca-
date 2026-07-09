import java.util.Scanner;

import controller.EmprestimoController;
import controller.LivroController;
import controller.UsuarioController;
import view.EmprestimoView;
import view.LivroView;
import view.MenuPrincipal;
import view.UsuarioView;

public class Main {

    /*@
      @ public normal_behavior
      @ requires args != null;
      @ assignable \nothing;
      @ ensures true;
      @ signals (Exception e) false;
      @*/
    public static void main(String[] args) {
        Scanner scanner = new Scanner(System.in);

        LivroController livroController = new LivroController();
        UsuarioController usuarioController = new UsuarioController();
        EmprestimoController emprestimoController = new EmprestimoController(livroController, usuarioController);

        LivroView livroView = new LivroView(scanner, livroController);
        UsuarioView usuarioView = new UsuarioView(scanner, usuarioController);
        EmprestimoView emprestimoView = new EmprestimoView(scanner, emprestimoController);

        MenuPrincipal menuPrincipal = new MenuPrincipal(scanner, livroView, usuarioView, emprestimoView);
        menuPrincipal.iniciar();

        scanner.close();
    }
}
