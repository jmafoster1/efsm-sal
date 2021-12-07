package isabellesal;

import java.util.*;
 /**
  * @author Siobhan
  */
public enum Token {
    ABBREVIATION,
    ADD("+"), //Infix version
    ALIAS_NAME,
    ALWAYS("alw", "G"), 
    AND("gAnd", "AND"), 
    AAND("aand", "AND"), 
    ARITY,

    BAR("|"), 
    BEGIN, 
    BOOLEAN_CONSTANT("Bc"),

    CHECK_EXP("check_exp"),
    CLOSE("\\<close>"),
    CLOSING_CURLY_BRACKET("}"), 
    CLOSING_ROUND_BRACKET(")"), 
    CLOSING_SQUARE_BRACKET("]"), 
    COLON(":"), 
    COMMA(","), 
    COMMENT("\\<comment>"),
    CONSTANT_NAME("the name of a constant"),
    CONTEXT,

    DATATYPE,
    DECLARE("declare"),
    DEFINITION,
    DOT("."),                                   
    DOUBLE_COLON("::"),
    DOUBLE_PRIME("''"),
    
    EFSM("\"efsm\""),
    EFSM_NAME("the name of an efsm"),
    ELIPSE(null, ".."),
    ELSE,
    END,
    END_OF_FILE("the end of the file"), 
    EQUALS("="), 
    EQUALS_PREFIX("Eq", "value_eq"), 
    EQUIV("\\<equiv>"),
    EVENTUALLY("ev","F"), 

    FALSE("False", "FALSE"), 
    FILE_NAME("the name of the file"),
    FORALL, 
    FREE_VARIABLE_NAME,
    
    GE("Ge","value_ge"),    
    GEXP,///might be redundant
    GT("Gt", "value_gt"), 
    GUARDS("Guards", null), 
    GUARDED_BY(null, "-->"),
 
    IMPLIES("impl","=>"),
    IMPORTS,
    IMPORT_NAME,
    INITIALIZATION,
    INPUT("i"),
    INPUT_EQ("input_eq"),
    IP("ip", "I"), 
    OP("op", "O"), 
    RG("rg"),    
    
    IRRELEVANT_OPERATOR,
    ISABELLE_FORMATTING,
    
    LABEL,
    LABEL_EQ("label_eq"),
    LE("Le","value_le"),
    LEMMA,
    LEMMAS,
    LEFT_PARR("\\<lparr>"),
    LITERAL("L"),
    LOCAL,
    LOCAL_VARIABLE("a local variable"),
    LT("<", "value_lt"), 
    
    MAPS_TO("\\<mapsto>"),  
    MINUS("Minus","value_minus"), 
    MODULE, 
    
    N("N"),  //completely different meaning in Isabelle and SAL
    NATURAL("nat"), 
    NEQ("Ne","/="),    
    NEW_WORD("a new identifier"), 
    NEXT("nxt", "X"), 
    NONE("None"),
    NOR("Nor"),
    NOT("gNot","NOT"),
    NUM("Num"),
    NUMBER("a number"),
    NULL("Null", "NULL"),
    
    OPEN("\\<open>"),
    OPENING_CURLY_BRACKET("{"), 
    OPENING_ROUND_BRACKET("("), 
    OPENING_SQUARE_BRACKET("["), 
    OR("gOr", "OR"), 
    OUTPUT_EQ("output_eq"),
    OUTPUTS,
    
    PLUS("Plus", "value_plus"),    
    PRIME("'"),
    
    QUOTE("\""),
    
    RIGHT_PARR("\\<rparr>"),
    REGISTER("r"),
    
    S("S"),
    SAL_RESERVED_WORD("word that is reserved in SAL"), 
    SEMICOLON(";"), 
    SOME("Some"),
    STATE_EQ("state_eq"),
    STR("Str"),
    STRING ("a string"), 
    
    THEOREM,
    THEORY,
    TIMES("Mul","value_mul"),
    TRACE,
    TRANSITION("\"transition\"","TRANSITION"),
    TRANSITION_MATRIX("\"transition_matrix\""),
    TRANSITION_NAME("the name of a transition"),
    TRUE("true", "TRUE"), 
    TYPE,
    TYPE_NAME("word that identifies a Type"), 
    
    UNKNOWN("character which does not occur in Isabelle"),
    UNTIL_STRONG("suntil", "U"), 
    UNTIL_WEAK("until", "W"), 
    UPDATES,
    
    VALUE_EQ("Eq", "value_eq"), 
    VALUE_GT("Gt", "value_gt"),
    VALUE_LT("Lt", "value_lt"),
    VALUE_GE("Ge", "value_ge"),
    VALUE_LE("Le", "value_le"),
    VARIABLE("V"),
    
    WATCH("watch"),
    
    WHERE; 

    
    //Schema name prefix
    private String fromIsabelle = null;
    private String toSAL = null;

    String inWords() {
        if  (  fromIsabelle == null )  return name().toLowerCase();
        return fromIsabelle;
    }

    Token(String w) {
        fromIsabelle = w;
    }
    
    Token(String i, String s) {
        fromIsabelle = i;
        toSAL = s;
    }
    
    Token() {}
    
    //+++++++++++++++++++++++++++++++++  Tokens which are a single non alphanumeric symbol
    private static final Map<Character, Token> TOKENS_FOR_SYMBOLS = allTokenSymbols();

    private static Map<Character, Token> allTokenSymbols() {
        Map<Character, Token> result = new HashMap<>(14);
        result.put('+', Token.ADD);
        result.put('|', Token.BAR); 
        result.put(',', Token.COMMA);
        result.put(':', Token.COLON);
        result.put('}', Token.CLOSING_CURLY_BRACKET);
        result.put(')', Token.CLOSING_ROUND_BRACKET);
        result.put(']', Token.CLOSING_SQUARE_BRACKET);
        result.put('.', Token.DOT);	
        result.put('=', Token.EQUALS);	
        result.put('>', Token.GT);
        result.put('<', Token.LT);
        result.put('-', Token.MINUS);
        result.put('{', Token.OPENING_CURLY_BRACKET);
        result.put('(', Token.OPENING_ROUND_BRACKET);
        result.put('[', Token.OPENING_SQUARE_BRACKET);
        result.put('\'',Token.PRIME);	
        result.put('\"', Token.QUOTE);	
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
    
    String inSAL() {  
        if  (  toSAL != null  )  return toSAL;
        if  (  fromIsabelle != null  )  return fromIsabelle;
        return name();
    }
    
}
