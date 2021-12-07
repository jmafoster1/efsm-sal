package dottoisabelle;

import java.util.Collections;
import java.util.HashMap;
import java.util.Map;
 /**
  * @author Siobhan
  */
public enum Token {
    AND("&amp;", "gAnd"),
    ASSIGNMENT(":="),

    BACKSLASH("/"),
    BAR("|"), 
    BEGIN, 

    CLOSE,  
    CLOSING_CURLY_BRACKET("}"), 
    CLOSING_DOUBLE_PRIME("''"),
    CLOSING_QUOTE("\""),
    CLOSING_ITALIC_TAG("</i>"), 
    CLOSING_ROUND_BRACKET(")"), 
    CLOSING_SQUARE_BRACKET("]"), 
    CLOSING_SUBSCRIPT_TAG("</sub>"),
    COLON(":"), 
    CLUSTER_NAME("the name of a cluster"),
    COMMA(","), 
    COMMENT,

    DIGRAPH,

    EDGE,
    END,
    END_OF_FILE("the end of the file"), 
    EQUALS("=", "="), 

    FALSE("FALSE","false"),
    FILE_NAME("the name of the file"),

    GE("Ge"),    
    GRAPH,
    GRAPH_NAME("the name of graph"),
    GT("Gt"), 

    INPUT("i"),

    LABEL,
    LE("Le"),
    LT("Lt"), 
    
    MOVE("->"),
    MINUS("-", "Minus"), 

    NEQ("&ne;","Ne"),    
    NEW_WORD("a new identifier"),

    NODE,
    NOT("&not;","gNot"),
    NUMBER("a number"),
    NULL("NULL", "Null"),

    OPENING_CURLY_BRACKET("{"), 
    OPENING_DOUBLE_PRIME("''"),
    OPENING_ITALIC_TAG("<i>"), 
    OPENING_QUOTE("\""),
    OPENING_ROUND_BRACKET("("), 
    OPENING_SQUARE_BRACKET("["),
    OPENING_SUBSCRIPT_TAG("<sub>"),
    OR("&or;", "gOr"),
    OUTPUT("o"),

    PLUS("+", "Plus"),    

    QUOTE("\""),

    REGISTER("r"),

    SEMICOLON(";"), 
    SUBGRAPH,
    STATE_NAME("The name of a state"),

    THEORY,
    TIMES("&times;", "Mul"),
    TRANSITION_NAME("the name of a transition"),
    TRUE("TRUE","true"),

    UNKNOWN("character which does not occur in Dot files");

    //Schema name prefix
    private String fromDot = null;
    private String toIsabelle = null;

    String inWords() {
        if  (  fromDot == null )  return name().toLowerCase();
        return fromDot;
    }

    Token(String w) {
        fromDot = w;
        toIsabelle = w;
    }
    
    Token(String i, String s) {
        fromDot = i;
        toIsabelle = s;
    }
    
    Token() {
        toIsabelle = name().toLowerCase();
    }
    
    //+++++++++++++++++++++++++++++++++  Tokens which are a single non alphanumeric symbol
    private static final Map<Character, Token> TOKENS_FOR_CHARACTERS = allTokenSymbols();

    private static Map<Character, Token> allTokenSymbols() {
        Map<Character, Token> result = new HashMap<>(18);////////

        result.put('/', Token.BACKSLASH);

        result.put(',', Token.COMMA);
        result.put(':', Token.COLON);
        result.put('}', Token.CLOSING_CURLY_BRACKET);
        result.put('"', Token.CLOSING_QUOTE);       
        result.put(')', Token.CLOSING_ROUND_BRACKET);
        result.put(']', Token.CLOSING_SQUARE_BRACKET);

        result.put('=', Token.EQUALS);	

        result.put('>', Token.GT);

        result.put('<', Token.LT);

        result.put('-', Token.MINUS);

        result.put('{', Token.OPENING_CURLY_BRACKET);       
        result.put('"', Token.OPENING_QUOTE);       
        result.put('(', Token.OPENING_ROUND_BRACKET);
        result.put('[', Token.OPENING_SQUARE_BRACKET);

        result.put('+', Token.PLUS);

        result.put('\"', Token.QUOTE);	

        result.put(';', Token.SEMICOLON);

        return Collections.unmodifiableMap(result);
    }

    public static Token forCharacter(char c)  {
        if (TOKENS_FOR_CHARACTERS.containsKey(c)) 
            return TOKENS_FOR_CHARACTERS.get(c);
        else 
            return Token.UNKNOWN;        
    }

    private static final Map<Integer, Token> FOR_HTML_CODE = allTokenCodes();

    private static Map<Integer, Token> allTokenCodes() {
        Map<Integer, Token> result = new HashMap<>(2);//////
        result.put(93, Token.CLOSING_SQUARE_BRACKET);
        result.put(91, Token.OPENING_SQUARE_BRACKET);
        return Collections.unmodifiableMap(result);
    }

    public static Token forHTMLCode(int n)  {
        if (FOR_HTML_CODE.containsKey(n)) 
            return FOR_HTML_CODE.get(n);
        else 
            return Token.UNKNOWN;        
    }

    //+++++++++++++++++++++++++++++++++  Outputting tokens
    
    String inIsabelle() {  
        if  (  toIsabelle != null  )  return toIsabelle;
        if  (  fromDot != null  )  return fromDot;
        return name();
    }
    
    
}
