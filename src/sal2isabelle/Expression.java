package sal2isabelle;

import static sal2isabelle.Parser.*;
import static sal2isabelle.Generator.*;

/**
 * Expressions in any context
 * @author Siobhan
 */

public abstract class Expression {   
    
    //::::::::::::::::::::::::::: Input as SAL
      
    static Expression acceptOne(boolean fromTransition) throws TranslationException {
        nextTokenMustBeOneOf(
                Token.LITERAL,
                Token.NUM,
                Token.PLUS,
                Token.MINUS,
                Token.REGISTER_VARIABLE, 
                Token.SOME, 
                Token.STR);
        
        Expression result = null;
                
        switch( nextToken() ) {
            case LITERAL : 
                return ConstantExpression.of(Constant.readOneIn());
            case MINUS :
            case PLUS :
                return ArithmeticExpression.acceptIt(fromTransition);
            case REGISTER_VARIABLE :
                return VariableExpression.acceptIt(fromTransition); 
            case SOME : 
                accept(Token.SOME, Token.OPENING_ROUND_BRACKET);
                nextTokenMustBeOneOf(
                    Token.STR, 
                    Token.NUM,
                    Token.INPUT_VARIABLE,
                    Token.FREE_VARIABLE_NAME);
                if  (  nextTokenIsOneOf(Token.INPUT_VARIABLE, Token.FREE_VARIABLE_NAME)  )
                    result = VariableExpression.acceptIt(fromTransition);
                else //STR or NUM
                    result = acceptOne(fromTransition);
                break;
            case STR :
            case NUM :
                boolean isNum = acceptedToken() == Token.NUM;
                accept(Token.OPENING_ROUND_BRACKET);
                if  (  isNum  )
                    nextTokenMustBeOneOf(Token.NUMBER, Token.FREE_VARIABLE_NAME);
                else
                    nextTokenMustBeOneOf(Token.STRING_NAME, Token.FREE_VARIABLE_NAME);
                if  (  nextTokenIs(Token.FREE_VARIABLE_NAME)  )
                    result = VariableExpression.acceptIt(fromTransition);
                else if  ( isNum )
                    result = ConstantExpression.of(NumericConstant.acceptNumber());
                else 
                    result = ConstantExpression.of(SystemConstant.acceptString()); 
        }
        accept(Token.CLOSING_ROUND_BRACKET);
        return result;
    }
    
    //::::::::::::::::::::::::::: Output to Isobelle  
            
    abstract void outputAsIsabelle()  throws TranslationException; 
    
}
class DummyExpression extends Expression {
    static DummyExpression acceptOne() throws TranslationException {
        int bracketCount = 0;
        while ( bracketCount>0 || ! nextTokenIsOneOf(Token.COMMA) ) {
            if  (  nextTokenIs(Token.OPENING_ROUND_BRACKET)  )
                bracketCount++;
            else if  (  nextTokenIs(Token.CLOSING_ROUND_BRACKET)  )
                bracketCount--;
            acceptToken();
        }
        return new DummyExpression();
    }
    @Override
    void outputAsIsabelle() throws TranslationException {
        outputIsabelle("Siobhan hasn't written this bit yet");
    }
    
}

class ArithmeticExpression extends Expression {

    //::::::::::::::::::::::::::: The Internal Representation
    
    private Expression left, right;
    private Token op;
    
    private ArithmeticExpression (Expression l, Token o, Expression r)  {
        left = l;
        op = o;
        right = r;
    }
    
    //::::::::::::::::::::::::::: Creation from SAL
           
    static ArithmeticExpression acceptIt(boolean fromTransition) throws TranslationException   {
        Token t = acceptedToken();  
        assert t==Token.PLUS || t==Token.MINUS || t==Token.TIMES;
        accept(Token.OPENING_ROUND_BRACKET);
        Expression l = Expression.acceptOne(fromTransition);
        accept(Token.COMMA);
        Expression r = Expression.acceptOne(fromTransition);
        accept(Token.CLOSING_ROUND_BRACKET);
        return new ArithmeticExpression(l, t, r);
    }
    
    //::::::::::::::::::::::::::: Output as Isobelle
    
    @Override void outputAsIsabelle() throws TranslationException { 
        outputIsabelle(Token.OPENING_ROUND_BRACKET, op);
        left.outputAsIsabelle();
        right.outputAsIsabelle();
        outputIsabelle(Token.CLOSING_ROUND_BRACKET);      
    }
     
}
class  ConstantExpression extends Expression {
    
    //::::::::::::::::::::::::::: The Internal Representation
    
    static ConstantExpression of(Constant c) {
        return new ConstantExpression(c);
    }
    
    private Constant constant;    
    public Constant getConstant() {  return constant;  }
    
    private ConstantExpression(Constant c)  {
        constant = c;
    }
    
    //::::::::::::::::::::::::::: Output to Isobelle  
                
    @Override
    void outputAsIsabelle() throws TranslationException    {
        outputIsabelle(Token.OPENING_ROUND_BRACKET, 
                Token.LITERAL, Token.OPENING_ROUND_BRACKET);
        constant.outputAsIsabelle();
        outputIsabelle(Token.CLOSING_ROUND_BRACKET,
                Token.CLOSING_ROUND_BRACKET);
    }

} 

class  VariableExpression extends Expression {
    
    //::::::::::::::::::::::::::: The Internal Representation
    
    private Variable variable;
    public Variable getVariable() {   return variable;   }

    private VariableExpression(Variable v)  {
        variable = v;
    }
   
    //::::::::::::::::::::::::::: Input as SAL
      
    static VariableExpression acceptIt(boolean fromTransition)  throws TranslationException  {
        return new VariableExpression(Variable.readOneIn(fromTransition));
    }
    
    //::::::::::::::::::::::::::: Output to Isobelle  
                
    @Override
    void outputAsIsabelle() throws TranslationException {  
        if  (  variable instanceof FreeVariable  )  
            if  (  variable.getType() == Type.VALUE )
                variable.outputAsIsabelle();
            else {
                outputIsabelle(Token.SOME, Token.OPENING_ROUND_BRACKET );
                variable.outputAsIsabelle();
                outputIsabelle(Token.CLOSING_ROUND_BRACKET);
            }
        else {
            outputIsabelle(
                    Token.OPENING_ROUND_BRACKET, 
                    Token.VARIABLE, 
                    Token.OPENING_ROUND_BRACKET);
            variable.outputAsIsabelle();
            outputIsabelle(
                    Token.CLOSING_ROUND_BRACKET, 
                    Token.CLOSING_ROUND_BRACKET);
        }
    }
            
}

