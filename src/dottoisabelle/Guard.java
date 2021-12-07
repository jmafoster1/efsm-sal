
package dottoisabelle;

import static dottoisabelle.Generator.*;
import static dottoisabelle.Parser.*;

/**
 * Deals with guards in both isabelle and dot
 * @author Siobhan
 */
abstract class Guard {
     
    //::::::::::::::::::::::::::: Creation from Dot 
    
    private static Guard readInSimplePredicate() throws DotException {
        
        if  (  acceptedTokenWas(Token.OPENING_ROUND_BRACKET)  )  {
            Guard result = readOneIn();
            accept(Token.CLOSING_ROUND_BRACKET);
            return result;
        }
        
        Expression start = Expression.readOneIn();
        
        if  (  start instanceof ConstantExpression  && 
                ((ConstantExpression)start).getConstant()instanceof BooleanConstant  )
            return ConstantGuard.of(((ConstantExpression)start));
        
        nextTokenMustBeOneOf(ComparisonGuard.OPERATORS);
        
        return ComparisonGuard.of(
                start, 
                acceptedToken(), 
                Expression.readOneIn());           
        
    }
    
    static Guard readOneIn() throws DotException { 
        Guard start;        
        if  (  acceptedTokenWas(Token.NOT)  )
            start = NegativeGuard.of(readOneIn());
        else start = readInSimplePredicate();
        
        while  (  nextTokenIsOneOf(Token.OR, Token.AND)  )  
            start = LogicalGuard.of(
                    start, 
                    acceptedToken(), 
                    readInSimplePredicate());
        
        return start;
    }
    
    //::::::::::::::::::::::::::: Output to Isobelle 
    
    abstract void outputInIsabelle();
    
}

class ComparisonGuard extends Guard {
      
    //::::::::::::::::::::::::::: The Internal Representation
           
    final static Token[] OPERATORS = {
        Token.EQUALS, Token.GE, Token.GT, 
        Token.LE, Token.LT, Token.NEQ};
    
    static ComparisonGuard of(Expression l, Token o, Expression r) throws DotException {
        return new ComparisonGuard(l, o, r);
    }

    private Expression left, right;
    private Token operator;
    
    ComparisonGuard (Expression l, Token o, Expression r) throws DotException {
        left = l;
        operator = o;
        right = r;
    }
    
    //::::::::::::::::::::::::::: Output to Isobelle 
    
    @Override void outputInIsabelle() {
        output(Token.OPENING_ROUND_BRACKET);
        if  (  right == null  && operator == Token.EQUALS  )  {
            output(Token.NULL);
            left.outputInIsabelle();
        }
        else   {
            if  (  operator == Token.EQUALS  )  
                output("gexp.Eq"); 
            else 
                output(operator);            
            left.outputInIsabelle();
            right.outputInIsabelle();
        }    
        output(Token.CLOSING_ROUND_BRACKET);
    }
        
}

class ConstantGuard extends Guard {
      
    //::::::::::::::::::::::::::: The Internal Representation
           
    static ConstantGuard of(ConstantExpression c)  {
        return new ConstantGuard((BooleanConstant)(c.getConstant()));
    }    
    
    private BooleanConstant constant;
    
    ConstantGuard (BooleanConstant c)  {
        constant = c;
    }    
    
    //::::::::::::::::::::::::::: Output to Isobelle 
    
    @Override void outputInIsabelle() {
        output("Bc ");
        constant.outputInIsabelle();
    }

}

class LogicalGuard extends Guard {
      
    //::::::::::::::::::::::::::: The Internal Representation
    
    static LogicalGuard of(Guard l, Token o, Guard r) {
        return new LogicalGuard(l, o, r);
    }
           
    private Guard left, right;
    private Token operator;
    
    private LogicalGuard (Guard l, Token o, Guard r)  {
        left = l;
        operator = o;
        right = r;
    }   
    
    //::::::::::::::::::::::::::: Output to Isobelle 
    
    @Override void outputInIsabelle() {
        output(Token.OPENING_ROUND_BRACKET);
        output(operator);
        left.outputInIsabelle();
        right.outputInIsabelle();
        output(Token.CLOSING_ROUND_BRACKET);
    }

}

class NegativeGuard extends Guard {
     
    //::::::::::::::::::::::::::: The Internal Representation
     
    static NegativeGuard of(Guard g) {
        return new NegativeGuard(g);
    }
    
    private Guard operand;

    private NegativeGuard (Guard o) {
        operand = o;
    }
    
    //::::::::::::::::::::::::::: Output to Isobelle 
    
    @Override void outputInIsabelle() {
        output(Token.NOT);
        output(Token.OPENING_ROUND_BRACKET);
        operand.outputInIsabelle();
        output(Token.CLOSING_ROUND_BRACKET);
    }
            
}
