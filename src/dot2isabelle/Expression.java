package dot2isabelle;

import static dot2isabelle.Generator.*;
import static dot2isabelle.Parser.*;

/**
 *  Everything to do with expressions in both languages
 * @author Siobhan
 */

public abstract class Expression {
       
    //::::::::::::::::::::::::::: Creation from Dot 
    
    static Expression readOneIn() throws DotException  {
        boolean bracketed = acceptedTokenWas(Token.OPENING_ROUND_BRACKET);
        nextTokenMustBeOneOf(
                Token.INPUT, Token.MINUS,Token.NULL, Token.NUMBER, 
                Token.QUOTE, Token.REGISTER, Token.TRUE, Token.FALSE
                        );
        Expression result=null;
        switch (nextToken()) {
            case QUOTE :
            case NUMBER :
            case MINUS :
                result = ConstantExpression.of(Constant.readOneIn());  
                break;
            case INPUT :
            case REGISTER : 
              result = VariableExpression.of(Variable.readOneIn());
              break;
            case NULL :
                accept(Token.NULL);
                result = null;  
                break;
            case TRUE :
            case FALSE :
                result = ConstantExpression.of(Constant.readOneIn());
                break;
            default : assert false; 
        }
        if  (  nextTokenIsOneOf(Token.MINUS, Token.PLUS,  Token.TIMES)  )  
            result = InfixExpression.of(result, acceptedToken(), readOneIn());
        
        if  (  bracketed  )  
            accept(Token.CLOSING_ROUND_BRACKET);
        
        return result;
    }
    
    //::::::::::::::::::::::::::: Output to Isobelle 
    
    abstract void outputInIsabelle();
   
}

class  ConstantExpression extends Expression {
      
    //::::::::::::::::::::::::::: The Internal Representation
           
    static ConstantExpression of(Constant c) {
        return new ConstantExpression(c);
    }
           
    private Constant constant;
    Constant getConstant() {   return constant;  }
    
    private ConstantExpression(Constant c)  {
        constant = c;
    }
       
    //::::::::::::::::::::::::::: Output to Isobelle 
    
    @Override void outputInIsabelle() {  
        output(Token.OPENING_ROUND_BRACKET, "L");
        constant.outputInIsabelle();
        output(Token.CLOSING_ROUND_BRACKET);
    }

}  

class InfixExpression extends Expression {                
      
    //::::::::::::::::::::::::::: The Internal Representation
               
    static InfixExpression of(Expression lhs, Token o, Expression rhs) throws DotException  {
        return new InfixExpression(lhs,o,rhs);
    }
        
    private Expression left, right;
    private Token op;
    
    private InfixExpression (Expression l, Token o, Expression r)  {
        left = l;
        op = o;
        right = r;
    }
          
    //::::::::::::::::::::::::::: Output to Isobelle 
    
    @Override void outputInIsabelle() {
        output(Token.OPENING_ROUND_BRACKET);
        output(op);        
        left.outputInIsabelle();
        right.outputInIsabelle();
        output(Token.CLOSING_ROUND_BRACKET);
    }

}

class  VariableExpression extends Expression {
      
    //::::::::::::::::::::::::::: The Internal Representation
    
    static VariableExpression of(Variable v)  {
        return new VariableExpression(v);
    }

    private Variable variable;   
    Variable getVariable()  {  return variable;  }
        
    private VariableExpression(Variable v)  {
        variable = v;
    }
          
    //::::::::::::::::::::::::::: Output to Isobelle 
    
    @Override void outputInIsabelle() {  
        output(Token.OPENING_ROUND_BRACKET, "V", Token.OPENING_ROUND_BRACKET);
        variable.outputInIsabelle();
        output(Token.CLOSING_ROUND_BRACKET,Token.CLOSING_ROUND_BRACKET);
    }

} 

