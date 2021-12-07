package dottoisabelle;

import static dottoisabelle.Parser.*;
import static dottoisabelle.Generator.*;

/**
 * Represents variables in isabelle and dot
 * @author sdn
 */
public abstract class Variable {//extends SyntacticElement {
    
    //::::::::::::::::::::::::::: Creation from Dot 
    
    static Variable readOneIn() throws DotException {
        
        nextTokenMustBeOneOf(
                Token.INPUT,
                Token.OUTPUT,
                Token.REGISTER);
        
        Variable result=null;
        
        Token t = acceptedToken();
        accept(Token.OPENING_SUBSCRIPT_TAG);
        nextTokenMustBe(Token.NUMBER);
        int subscript = acceptedNumber();
        if  (  subscript < 0  )
            reportAnError("The subscript cannot be negative");
        switch  ( t) {
            case INPUT : 
            case OUTPUT :
                result = IOVariable.of(t, subscript); 
                break;
            case REGISTER : result = RegisterVariable.of(subscript); 
            break;
            default :
                reportAnError("This should be a variable name");
        }  
        accept(Token.CLOSING_SUBSCRIPT_TAG);
        
        return result;
    }    
    
    //::::::::::::::::::::::::::: Output to Isobelle 
    
    abstract void outputInIsabelle();
}

class IOVariable extends Variable {
      
    //::::::::::::::::::::::::::: The Internal Representation
           
    private static enum Direction {
        INPUT, OUTPUT;
        
        void inIsabelle() {
            output(name().charAt(0));
        }
              
    }
    
    static IOVariable of(Token t, Integer s) {
        return new IOVariable(t,s);
    }
    
    private Integer subscript = null;
    private Direction direction;
    
    private IOVariable (Token t, Integer s) {
        assert s != null;
        subscript = s;
        assert t == Token.INPUT || t == Token.OUTPUT : t;
        direction = Direction.valueOf(t.name());
    }
    
    //::::::::::::::::::::::::::: Creation from Dot 
    
    static void acceptOutput(int count) throws DotException {        
        accept(Token.OUTPUT);
        accept(Token.OPENING_SUBSCRIPT_TAG);
        nextTokenMustBe(Token.NUMBER);
        int in = acceptedNumber();
        DotException.reportIf(
                in != count, 
                "this should have been "+count+" not "+in);
        accept(Token.CLOSING_SUBSCRIPT_TAG);
    }    
    
    //::::::::::::::::::::::::::: Output to Isobelle 
    
    @Override void outputInIsabelle() {
        direction.inIsabelle(); 
        output(subscript);
    }
    
}

class RegisterVariable extends Variable {
      
    //::::::::::::::::::::::::::: The Internal Representation
    
    static RegisterVariable of(int s) {
        return new RegisterVariable(s);
    }
           
    private int subscript;
    
    boolean isSameAs(RegisterVariable other) {
        return subscript == other.subscript;
    }
    
    private RegisterVariable (int s) {
        assert s > 0;
        subscript = s;
    }
        
    //::::::::::::::::::::::::::: Output to Isobelle 
                  
    void outputsubscript() {
        output(subscript);
    }
    
    @Override void outputInIsabelle() {
        output("R", subscript);
    }
    
}

