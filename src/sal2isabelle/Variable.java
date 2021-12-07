package sal2isabelle;

import static sal2isabelle.Generator.*;
import static sal2isabelle.Parser.*;
import java.util.*;

/**
 * Variables in both sal and isabelle
 * @author sdn
 */
public abstract class Variable   {
    
    //::::::::::::::::::::::::::: The Internal Representation
        
    private String identifier = null;
    String getIdentifier() {  return identifier;  }

    private Type type; 
    Type getType() {  return type;  }
    void setType(Type t)  {  type = t;  }
    
    protected Variable (String i, Type t) {  
        identifier = i;  
        type = t;
    }
              
    //::::::::::::::::::::::::::: Input as SAL
    
    public static Variable readOneIn(boolean fromTransition) throws TranslationException {
        nextTokenMustBeOneOf(
                Token.INPUT_VARIABLE, 
                Token.OUTPUT_VARIABLE, 
                Token.REGISTER_VARIABLE,
                Token.FREE_VARIABLE_NAME);
        switch (nextToken()) {
            case REGISTER_VARIABLE:
                return RegisterVariable.acceptOne(fromTransition);
            case FREE_VARIABLE_NAME:
                return FreeVariable.acceptOne();
            default:
                return IOVariable.acceptOne(fromTransition);
        }
     }
       
    //::::::::::::::::::::::::::: Output to Isobelle  
            
    abstract void outputAsIsabelle() throws TranslationException; 
       
}

class FreeVariable extends Variable {
    
    //::::::::::::::::::::::::::: The Internal Representation
    
    static Map <String, FreeVariable> allThisLemma = new HashMap<>();
           
    FreeVariable (String i, Type t)  {  
        super(i,t);
    }
        
    //::::::::::::::::::::::::::: Input as SAL
    
    static void readInDefinitions() throws TranslationException {
        allThisLemma.clear();
        do  {
            
            nextTokenMustBeOneOf(Token.NEW_WORD, Token.FREE_VARIABLE_NAME);
            String i = nextWord();
            assert ! allThisLemma.containsKey(i):i;
            if  (  nextTokenIs(Token.NEW_WORD)  )
                addToDictionary(nextWord(), Token.FREE_VARIABLE_NAME);
            acceptToken();
            
            accept(Token.COLON);
            
            nextTokenMustBeOneOf(Token.STRING, Token.BOUNDED_INT, Token.VALUE);
            allThisLemma.put(
                    i, 
                    new FreeVariable(i,Type.valueOf(acceptedToken().toString())));
            
            nextTokenMustBeOneOf(Token.NEW_WORD, Token.FREE_VARIABLE_NAME, 
                    Token.CLOSING_ROUND_BRACKET);
        }
        while ( ! nextTokenIs(Token.CLOSING_ROUND_BRACKET)  );
        
    }
    
    static FreeVariable acceptOne() throws TranslationException {
        assert nextTokenIs(Token.FREE_VARIABLE_NAME);
        assert allThisLemma.containsKey(nextWord());
        return allThisLemma.get(acceptedWord());
    }
    
    //::::::::::::::::::::::::::: Output as Isabelle
        
    @Override void outputAsIsabelle() throws TranslationException {
        switch (  getType()  ) { 
            case BOUNDED_INT  :
                outputIsabelle(Token.NUM);  break;
            case STRING :
                outputIsabelle(Token.STR);  break;
        }
        outputIsabelle(getIdentifier()); 
    } 
       
}

class IOVariable extends Variable {
    
    //::::::::::::::::::::::::::: The Internal Representation
    
    private Integer subscript = null;
    
    IOVariable (String i, Integer s) {
        super(i, null);
        subscript = s;
    }
        
    //::::::::::::::::::::::::::: Input as SAL
    
    public static IOVariable acceptOne(boolean fromTransition) throws TranslationException {
        assert nextTokenIsOneOf(Token.INPUT_VARIABLE, Token.OUTPUT_VARIABLE);
        Token d = acceptedToken();
        
        accept(Token.OPENING_ROUND_BRACKET);
        nextTokenMustBe(Token.NUMBER);
        int s = (int)acceptedNumber();
        accept(Token.CLOSING_ROUND_BRACKET);
        
        return new IOVariable(
                (  fromTransition ? d.inIsabelle().substring(0,1) : d.inIsabelle() ), 
                s);
    }

    //::::::::::::::::::::::::::: Output as Isabelle
        
    @Override void outputAsIsabelle() throws TranslationException {
        outputIsabelle(getIdentifier(), subscript);
    }
    
}

class RegisterVariable extends Variable {
    
    //::::::::::::::::::::::::::: The Internal Representation
    
    private int subscript;
    
    private RegisterVariable (boolean fromTransition, int s) {
        super((  fromTransition ? "R" : "Rg" ), null);
        subscript = s;
    }
         
    //::::::::::::::::::::::::::: Input as SAL
    
    public static RegisterVariable acceptOne(boolean fromTransition) throws TranslationException {
        accept(Token.REGISTER_VARIABLE);
        nextTokenMustBe(Token.NUMBER);
        return new RegisterVariable(fromTransition, (int)acceptedNumber());
    }
    
    //::::::::::::::::::::::::::: Output as Isabelle
        
    @Override public void outputAsIsabelle() throws TranslationException {
        outputIsabelle(getIdentifier(), subscript);
    }
    
    public void outputSubscript() throws TranslationException {
        outputIsabelle(subscript);
    }
    
}


