package isabelle2sal;

import static isabelle2sal.Generator.*;
import static isabelle2sal.Parser.*;
import java.util.*;

/**
 *
 * @author Siobhan
 */
public abstract class Guard {
    
    //::::::::::::::::::::::::::: Creation from Isobelle Source code
        
    static Guard readItIn(Object context) throws IsabelleException, FileException {
        
        nextTokenMustBeOneOf(
                Token.OPENING_ROUND_BRACKET,
                Token.BOOLEAN_CONSTANT, 
                Token.EQUALS_PREFIX, Token.NEQ, 
                Token.GE, Token.GT, Token.LE, Token.LT, 
                Token.NOT, 
                Token.AND, Token.OR);
        
        switch(nextToken()) {
            case OPENING_ROUND_BRACKET :
                accept(Token.OPENING_ROUND_BRACKET);
                Guard p = readItIn(context);
                accept(Token.CLOSING_ROUND_BRACKET);
                return p;
            case BOOLEAN_CONSTANT :
                return ConstantPredicate.readOneIn();
            case NOT :
                return InvertedPredicate.readOneIn(context);
            case EQUALS_PREFIX:
            case GE :
            case GT :
            case LE : 
            case LT :
            case NEQ :
                return ComparisonPredicate.readOneIn(context);
            case OR :
            case AND :
                return LogicalPredicate.readOneIn(context);
        }
        assert false;
        return null;
    }
       
    //::::::::::::::::::::::::::: Output as SAL
    
    abstract void outputAsSAL() throws IsabelleException, FileException;

    //::::::::::::::::::::::::::: Output as Dot
    
    abstract String toDot();
    
}

class ComparisonPredicate extends Guard {
    
    //::::::::::::::::::::::::::: The Internal Representation
    
    private Expression left, right;
    private Token operator;

    private ComparisonPredicate (Token t, Expression l, Expression r)  {
        operator = t;
        left = l;
        right = r;
    }
    
    //::::::::::::::::::::::::::: Creation from Isobelle Source code
        
    public static ComparisonPredicate readOneIn(Object context) throws IsabelleException, FileException {
        Token t = acceptedToken();
        Expression l = Expression.readItIn(context);
        Expression r = Expression.readItIn(context); 
        if  (  EnumSet.of(Token.GE, Token.GT, Token.LE, Token.LT).contains(t)  )  {
            l.mustBeInteger();
            r.mustBeInteger();
        }
        return new ComparisonPredicate(t, l, r);        
    }
    
    //::::::::::::::::::::::::::: Output as SAL
    
    void outputAsSalWithoutGVAL() throws IsabelleException, FileException  {
        if  (  operator == Token.EQUALS  )  {
            left.outputAsSAL(true);  //without Some
            outputSAL(operator);
            right.outputAsSAL(true);  //with Some if true      
        }
        else {
            outputSAL(operator, Token.OPENING_ROUND_BRACKET);
            left.outputAsSAL(true);  //without Some
            outputSAL(Token.COMMA);
            right.outputAsSAL(true);  //with Some if true 
            outputSAL(Token.CLOSING_ROUND_BRACKET);
        }
    }
    
    @Override void outputAsSAL() throws IsabelleException, FileException {  
        assert operator != null;
        switch (operator) {
            case EQUALS:
            case NEQ:
                if  (  left instanceof VariableExpression &&
                        (((VariableExpression)left).getVariable() instanceof IOVariable)   )  {
                    outputSAL("gval", Token.OPENING_ROUND_BRACKET);
                    outputSAL(Token.EQUALS_PREFIX, Token.OPENING_ROUND_BRACKET);
                    left.outputAsSAL(true);  //with Some
                    outputSAL(Token.COMMA);
                    right.outputAsSAL(true);  //with Some
                    outputSAL(Token.CLOSING_ROUND_BRACKET);
                    outputSAL(Token.CLOSING_ROUND_BRACKET);
                }
                else 
                    outputAsSalWithoutGVAL();
                break;
            default:
                outputSAL("gval", Token.OPENING_ROUND_BRACKET);
                outputSAL(operator, Token.OPENING_ROUND_BRACKET);
                left.outputAsSAL(true );  //with Some if true
                outputSAL(Token.COMMA);
                right.outputAsSAL(true);  //without Some
                outputSAL(Token.CLOSING_ROUND_BRACKET);
                outputSAL(Token.CLOSING_ROUND_BRACKET);
        }
    }
        
    //::::::::::::::::::::::::::: Output as Dot
    
    @Override String toDot() {
       switch (  operator  )  {
            case EQUALS_PREFIX :
            case EQUALS :
                return left.toDot() + " = " + right.toDot();
            case NEQ :
                return left.toDot() + " &ne; " + right.toDot();
            case GE : 
                return left.toDot() + " &ge; " + right.toDot();
            case GT : 
                return left.toDot() + " &gt; "  + right.toDot(); 
            case LE :
                return left.toDot() + " &le; "  + right.toDot();
            case LT : 
                return left.toDot() + " &lt; "  + right.toDot();
        }
        assert false:operator;
        return null;
    }

}

class ConstantPredicate extends Guard {
    
    //::::::::::::::::::::::::::: The Internal Representation
    
    private BooleanConstant value;
    
    private ConstantPredicate (BooleanConstant c) {
        value = c;
    }
    
    //::::::::::::::::::::::::::: Creation from Isobelle Source code
        
    public static ConstantPredicate readOneIn() throws IsabelleException, FileException {
        accept(Token.BOOLEAN_CONSTANT);
        return new ConstantPredicate(BooleanConstant.readItIn());
    }
        
    //::::::::::::::::::::::::::: Output as SAL
    
    @Override public void outputAsSAL() throws IsabelleException, FileException {  
        outputSAL(value.useAsSAL());
    }
        
    //::::::::::::::::::::::::::: Output as Dot
       
    @Override public String toDot() {
        return value.toDot();  
    }
    
}

class InvertedPredicate extends Guard {
    
    //::::::::::::::::::::::::::: The Internal Representation
    
    private Guard predicate;
    
    private InvertedPredicate(Guard p) {
        predicate = p;
    }
    
    //::::::::::::::::::::::::::: Creation from Isobelle Source code
        
    public static InvertedPredicate readOneIn(Object context) throws IsabelleException, FileException  {
        accept(Token.NOT);   
        accept(Token.OPENING_ROUND_BRACKET);
        Guard p = readItIn(context);
        accept(Token.CLOSING_ROUND_BRACKET);
        return new InvertedPredicate(p);
    }
    
    //::::::::::::::::::::::::::: Output as SAL
    
    @Override public void outputAsSAL() throws IsabelleException, FileException {  
        outputSAL(Token.NOT, Token.OPENING_ROUND_BRACKET);
        predicate.outputAsSAL();
        outputSAL(Token.CLOSING_ROUND_BRACKET);
    }
        
    //::::::::::::::::::::::::::: Output as Dot
       
    @Override public String toDot() {
        return "&not; " + predicate.toDot();
    }

}

class LogicalPredicate extends Guard {
    
    //::::::::::::::::::::::::::: The Internal Representation
    
    private Guard left, right;
    private Token operator;
    public boolean getIsAnd()  {  return operator == Token.AND;  }

    private LogicalPredicate (Token t, Guard l, Guard r)  {
        operator = t;
        left = l;
        right = r;
    } 
        
    //::::::::::::::::::::::::::: Creation from Isobelle Source code
        
    public static LogicalPredicate readOneIn(Object context) throws IsabelleException, FileException {
        Token t = acceptedToken();
        Guard l = Guard.readItIn(context);
        Guard r = Guard.readItIn(context);
        return new LogicalPredicate(t, l, r);
    }

    //::::::::::::::::::::::::::: Output as SAL
    
    @Override public void outputAsSAL() throws IsabelleException, FileException {  
        outputSAL(Token.OPENING_ROUND_BRACKET);
        left.outputAsSAL();  
        outputSAL(operator);
        right.outputAsSAL();
        outputSAL(Token.CLOSING_ROUND_BRACKET);
    }
                          
    //::::::::::::::::::::::::::: Output as Dot
       
    @Override public String toDot() {
        String middle = "";
        switch(operator) {
            case AND :  
                middle = "&amp;";
                break;
            case NOR :
            case OR :  
                middle = "&or;";
                break;
            case IMPLIES :  
                middle = "=&gt;";
                break;
            default : assert false;
        }
        middle = left.toDot() + " " + middle + " " + right.toDot();
        if  (  operator == Token.NOR  )
            return "&not; ("+middle+")";
        else
            return middle;
    }

}

