package salisobelle;

import java.util.Collections;
import java.util.HashMap;
import java.util.Map;
 /**
  * @author Siobhan
  */
public enum Token {
    ALWAYS("alw", "G"), 
    AND("and", "AND"),
    AAND("aand", "AND"), 
    ARITY("Arity"),

    BAR("|"), 
    BOOLEAN_CONSTANT("Bc"),
    BOUNDED_INT,

    CFSTATE("cfstate"),
    CHECK_EXP("check_exp"),
    CHECK_OVER_OR_UNDER_FLOW(),
    CLOSE("\\<close>"),
    CLOSING_CURLY_BRACKET("}"), 
    CLOSING_ROUND_BRACKET(")"), 
    CLOSING_SQUARE_BRACKET("]"), 
    CLOSING_DOUBLE_PRIME("''"),
    CLOSING_QUOTE("\""),
    COLON(":"), 
    COMMA(","), 

    DATATYPE,
    DEFINITION,
    DOT("."),                                   
    DOUBLE_COLON("::"),
    DOUBLE_PRIME("''"),
    
    EFSM_NAME("the name of an efsm"),
    ELSE,
    EMPTY,
    END,
    END_OF_FILE("the end of the file"), 
    EQUALS("="), 
    EQUALS_PREFIX("Eq", "value_eq"), 
    EQUIV("\\<equiv>"),
    EVENTUALLY("ev","F"), 
    EXCLAMATION_MARK(null, "!"),
    EXISTS("\\<exists>", "EXISTS"), 

    FALSE, 
    FILE_NAME("the name of the file"),
    FREE_VARIABLE_NAME("the name of a free variable"),
    FORALL, 
    
    GE("Ge", "value_ge"),    
    GT("Gt", "value_gt"), 
    GUARDS("Guards"),
    GUARDED_BY(null, "-->"),
    GVAL,
 
    IMPLIES("impl","=>"),
    INSERT,
    INPUT_EQ("input_eq"),
    INPUT_SEQUENCE,
    INPUT_VARIABLE("Ip", "i"),
    
    LABEL("Label"),
    LABEL_EQ("label_eq ", "label_eq"),
    LABEL_NAME("the name of a label"),
    LE("Le","value_le"),
    LEMMA,
    LEFT_PARR("\\<lparr>"),
    LITERAL("L"),
    LOCAL,
    LOCAL_VARIABLE("a local variable"),
    LT("Lt", "value_lt"), 
    
    MINUS("Minus","value_minus"), 
    MODULE, 
    
    NEQ("Ne","/="),    
    NEW_WORD("a new identifier"), 
    NEXT("nxt", "X"), 
    NONE("None"),
    NOT("not","NOT"),
    NUM("Num"),
    NUMBER("a number"),
    NULL_STATE,
    
    OPENING_CURLY_BRACKET("{"), 
    OPENING_ROUND_BRACKET("("), 
    OPENING_SQUARE_BRACKET("["), 
    OPENING_DOUBLE_PRIME("''"),
    OPENING_QUOTE("\""),
    OPLUS("\\<lparr>"),
    OR("or", "OR"), 
    OUTPUT_EQ("output_eq"),
    OUTPUT_SEQUENCE,
    OUTPUT_VARIABLE("op", "o"), 
    OUTPUTS("Outputs"),
    
    PLUS("Plus", "value_plus"),    
    PRIME("'"),
    
    QUESTION_MARK("?"),
    
    REGISTER_VARIABLE("Rg", "r__"),  
    RIGHT_PARR("\\<rparr>"),
    
    SEMICOLON(";"), 
    SIDEWAYS_T(null,"|-"),
    SINK_HOLE,
    SIZE,
    SOME("Some"),
    STATE,
    STATE_EQ("state_eq"),
    STATE_NAME,
    STR("Str","STR"),
    STRING, 
    STRING_NAME,
    
    THEOREM,
    TIMES("Mul","value_mul"),
    TRANSITION("\"transition\""),
    TRANSITION_MATRIX("\"transition_matrix\""),
    TRANSITION_NAME(null, "the name of a transition"),
    TRUE, 
    TYPE,
    
    UNKNOWN("character which does not occur in SAL"),
    UNTIL_STRONG("suntil", "U"), 
    UNTIL_WEAK("until", "W"), 
    UPDATES("Updates"),
    
    VALUE("Value"), 
    VARIABLE("V"),
    
    WHERE; 

    
    //Schema name prefix
    private String fromSAL = null;
    private String toIsabelle = null;

    Token(String w) {
        toIsabelle = w;
    }
    
    Token(String i, String s) {
        toIsabelle = i;
        fromSAL = s;
    }
    
    Token() {}
    
    public static boolean thereIsOneCalled(String s)  {
        try { 
            Token t = Token.valueOf(s);
            return true;
        }
        catch (Exception e) {
            return  false; 
        }        
    }
    
    //+++++++++++++++++++++++++++++++++  Tokens which are a single non alphanumeric symbol
    private static final Map<Character, Token> TOKENS_FOR_SYMBOLS = allTokenSymbols();

    private static Map<Character, Token> allTokenSymbols() {
        Map<Character, Token> result = new HashMap<>(14);
        result.put('|', Token.BAR); 
        result.put(',', Token.COMMA);
        result.put(':', Token.COLON);
        result.put('}', Token.CLOSING_CURLY_BRACKET);
        result.put(')', Token.CLOSING_ROUND_BRACKET);
        result.put(']', Token.CLOSING_SQUARE_BRACKET);
        result.put('.', Token.DOT);	
        result.put('=', Token.EQUALS);	
        result.put('!', Token.EXCLAMATION_MARK);
        result.put('>', Token.GT);
        result.put('<', Token.LT);
        result.put('-', Token.MINUS);
        result.put('{', Token.OPENING_CURLY_BRACKET);
        result.put('(', Token.OPENING_ROUND_BRACKET);
        result.put('[', Token.OPENING_SQUARE_BRACKET);
        result.put('\'',Token.PRIME);
        result.put('?', Token.QUESTION_MARK);
        result.put(';', Token.SEMICOLON);
        return Collections.unmodifiableMap(result);
    }

    public static Token symbol(char c)  {
        if (TOKENS_FOR_SYMBOLS.containsKey(c)) 
            return TOKENS_FOR_SYMBOLS.get(c);
        else 
            return Token.UNKNOWN;        
    }

    //+++++++++++++++++++++++++++++++++  Outputting tokens
    
    String inIsabelle() {  
        if  (  toIsabelle != null  )  return toIsabelle;
        if  (  fromSAL != null  )  return fromSAL;
        return name().toLowerCase();
    }
    String fromSAL() {  
        if  (  fromSAL != null  )  return fromSAL;
        if  (  toIsabelle != null  )  return toIsabelle;
        return name().toLowerCase();
    }
    
}
