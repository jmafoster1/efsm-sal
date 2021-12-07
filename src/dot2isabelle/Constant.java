package dot2isabelle;

import static dot2isabelle.Generator.*;
import static dot2isabelle.Parser.*;

/**
 * Deals with constants
 * @author Siobhan
 */
public abstract class Constant { 
            
    //::::::::::::::::::::::::::: Creation from Dot 
    
    static Constant readOneIn() throws DotException  {
        nextTokenMustBeOneOf(Token.NUMBER, Token.MINUS, Token.QUOTE, 
                Token.TRUE, Token.FALSE);
        switch(nextToken()) {
            case NUMBER:
            case MINUS :
                return  NumericConstant.readItIn();
            case QUOTE :
                return StringConstant.readItIn();
            case TRUE :                
            case FALSE:
                return BooleanConstant.readItIn();        
        }
        return null;
    }
       
    //::::::::::::::::::::::::::: Output to Isobelle 
    
    abstract void outputInIsabelle();
    
}

class BooleanConstant extends Constant {
      
    //::::::::::::::::::::::::::: The Internal Representation
           
     private Token token;
     
     private BooleanConstant(Token t) {
        token = t;
    }
    
    //::::::::::::::::::::::::::: Creation from Dot 
    
    static BooleanConstant readItIn() throws DotException  {
        return new BooleanConstant(acceptedToken());
    }
    
    //::::::::::::::::::::::::::: Output to Isobelle 
    
    @Override void outputInIsabelle()  {
        output(token);
    }
    
}

class NumericConstant extends Constant  {
        
    //::::::::::::::::::::::::::: The Internal Representation
               
    private Integer value;
    
    private NumericConstant(int c) {
        value = c;
    }
    
    //::::::::::::::::::::::::::: Creation from Dot 
    
    static NumericConstant readItIn() throws DotException  {
        int multiplier = (  acceptedTokenWas(Token.MINUS) ? -1 : 1);
        nextTokenMustBe(Token.NUMBER);
        int n = acceptedNumber() * multiplier;
        return new NumericConstant(n);        
    }
    
    //::::::::::::::::::::::::::: Output to Isobelle 
    
    @Override public void outputInIsabelle()  {
        output(Token.OPENING_ROUND_BRACKET, "Num");
        if  (  value < 0  )  
            output(Token.OPENING_ROUND_BRACKET, value, Token.CLOSING_ROUND_BRACKET);
        else 
            output(value);
        output(Token.CLOSING_ROUND_BRACKET);
    }
    
}

class StringConstant extends Constant {
           
    //::::::::::::::::::::::::::: The Internal Representation
               
    private String value;
     
    private StringConstant(String v) {
        value = v;
    }
    
    //::::::::::::::::::::::::::: Creation from Dot 
    
    static StringConstant readItIn() throws DotException  {
        return new StringConstant(acceptedQuotedText());
    }
    
    //::::::::::::::::::::::::::: Output to Isobelle 
    
    @Override void outputInIsabelle()  {
        output(Token.OPENING_ROUND_BRACKET, "Str", Token.OPENING_DOUBLE_PRIME,
                value, Token.CLOSING_DOUBLE_PRIME, Token.CLOSING_ROUND_BRACKET);
    }
    
}