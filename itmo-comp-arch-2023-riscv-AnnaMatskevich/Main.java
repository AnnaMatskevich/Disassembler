public class Main {
    public static void main(String[] args) {
        ElfParser parser = new ElfParser();
        if (args.length != 2) {
            System.err.println("2 args expected");
        }
        parser.parse(args[0], args[1]);
    }

}
