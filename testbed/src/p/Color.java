package p;

public enum Color {
    RED(1), GREEN(2), BLUE(3);

    private final int code;

    Color(int code) {
        this.code = code;
    }

    public int code() {
        return code;
    }
}
