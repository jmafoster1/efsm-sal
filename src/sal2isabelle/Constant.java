package sal2isabelle;

import static sal2isabelle.Parser.*;
import static sal2isabelle.Generator.*;
import java.util.*;

/**
 * Deals with String, numeric, label and state constants
 * @author Siobhan
 */
public abstract class Constant   {
        
    //::::::::::::::::::::::::::: The Internal Representation
    
    static void clearAll() {
        SystemConstant.clear();
    }
    
    //::::::::::::::::::::::::::: Input as SAL
      
    static Constant readOneIn() throws TranslationException {
        nextTokenMustBeOneOf(Token.NUM, Token.STR);
        if  (  nextTokenIs(Token.NUM)  )
            return NumericConstant.acceptIt();
        else 
            return SystemConstant.acceptOneOf(Type.STRING);        
    }
    
    //::::::::::::::::::::::::::: Output to Isobelle 
        
    abstract void outputAsIsabelle() throws TranslationException ;
    
}

class NumericConstant extends Constant  {
        
    //::::::::::::::::::::::::::: The Internal Representation
    
    private Long value;

    private NumericConstant(long c) {
        value = c;
    }
    
    //::::::::::::::::::::::::::: Input as SAL
      
    static NumericConstant acceptNumber() throws TranslationException  {
        //Num has already been accepted but no brackets
        assert nextTokenIs(Token.NUMBER);
        return new NumericConstant(acceptedNumber());
    }
    
    public static NumericConstant acceptIt() throws TranslationException  {
        accept(Token.NUM, Token.OPENING_ROUND_BRACKET);
        nextTokenMustBe(Token.NUMBER);
        long n = acceptedNumber();
        accept(Token.CLOSING_ROUND_BRACKET);
        return new NumericConstant(n);
    }
    
    //::::::::::::::::::::::::::: Output to Isobelle  
            
    @Override void outputAsIsabelle()  throws TranslationException {
        outputIsabelle(Token.NUM, value);
    }        
    
}

class SystemConstant extends Constant {
    
    //::::::::::::::::::::::::::: The Internal Representation
    
    private static Map<String, SystemConstant> allConstants =
            new HashMap<>();
        
    static void clear() {
        allConstants.clear();
    }
    
    private String identifier;
    String getIdentifier() {  return identifier;  }
    
    private Type type;
    
    SystemConstant (String i, Type t)  { 
        identifier = i; 
        type = t;
    }

    //::::::::::::::::::::::::::: Input as SAL
    
    private final static Type [] DECLARATION_ORDER = 
            {Type.LABEL, Type.STRING, Type.STATE};
    
    static void readInDeclarations() throws TranslationException {
        
        //Skip anything before the system constant declarations
        while (  !  nextTokenIs(Token.valueOf(DECLARATION_ORDER[0].toString()))  )  
            acceptToken();
        
        for (Type t : DECLARATION_ORDER) {
            
            accept(
                Token.valueOf(t.name()),
                Token.COLON, 
                Token.TYPE, 
                Token.EQUALS);
            
            Token ender;
            if  (  t == Type.LABEL  )  {
                accept(Token.DATATYPE);
                ender = Token.END;
            }
            else {
                accept(Token.OPENING_CURLY_BRACKET);
                ender = Token.CLOSING_CURLY_BRACKET;
            }
            
            do {
                nextTokenMustBeOneOf(Token.NEW_WORD, Token.NULL_STATE);
                if  (  !  acceptedTokenWas(Token.NULL_STATE)  )  {
                    addToDictionary(nextWord(), Token.valueOf(t.toString()+"_NAME"));
                    allConstants.put(
                            nextWord(),new SystemConstant(acceptedWord(), t));
                }
                nextTokenMustBeOneOf(Token.COMMA, ender);
            }
            while (  acceptedTokenWas(Token.COMMA)  );

            accept(ender, Token.SEMICOLON);

        }            
    }
    
    static SystemConstant acceptString() throws TranslationException {
        //Str has already been read in
        assert nextTokenIs(Token.STRING_NAME);
        return allConstants.get(acceptedWord());
    }
    
    static SystemConstant acceptOneOf(Type t) throws TranslationException {
        if  (  t == Type.STRING  )
            accept(Token.STR, Token.OPENING_ROUND_BRACKET);
        nextTokenMustBe(Token.valueOf(t.toString()+"_NAME"));
        SystemConstant result = allConstants.get(acceptedWord());
        if  (  t == Type.STRING  )
            accept(Token.CLOSING_ROUND_BRACKET);    
        return result;
    } 
    
    static SystemConstant findLabel(String name) throws TranslationException  {
        reportAnErrorUnless(
                allConstants.containsKey(name), "This should be a label");
        reportAnErrorUnless(
                allConstants.get(name).type == Type.LABEL, 
                "This should be a label");
        return allConstants.get(name);
    }
    //::::::::::::::::::::::::::: Output as Isabelle
        
    @Override void outputAsIsabelle() throws TranslationException {
        switch ( type )  {
            case LABEL:  
                outputIsabelle(
                        Token.OPENING_DOUBLE_PRIME, 
                        getIdentifier(), 
                        Token.CLOSING_DOUBLE_PRIME);
                break;
            case STATE :
                //remove STATE__ from the output
                outputIsabelle(getIdentifier().substring(7));   break;
            case STRING:
                if  (  getIdentifier().startsWith("String")  )
                    outputIsabelle(
                            Token.STR, 
                            Token.OPENING_DOUBLE_PRIME, 
                            getIdentifier().substring(8),
                            Token.CLOSING_DOUBLE_PRIME);
                else
                    outputIsabelle(Token.NUM, getIdentifier().substring(4));
        }
    }            
    

}

