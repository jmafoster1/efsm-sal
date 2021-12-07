package isabelle2sal;

import static isabelle2sal.Parser.*;
import static isabelle2sal.Generator.*;
import java.util.*;

/**
 * The internal representation of expressions (but not predicate expressions)
 * @author Siobhan
 */

public abstract class Expression {
        
            
    //::::::::::::::::::::::::::: The Internal Representation
    
    private Type type;
    
    Expression (Type t) {
        type = t;
    }
   
    //::::::::::::::::::::::::::: Creation from Isobelle Source code
            
    static Expression readItIn(Object context) throws IsabelleException, FileException {
        
        nextTokenMustBeOneOf(
                Token.OPENING_ROUND_BRACKET,
                Token.LITERAL, 
                Token.MINUS, 
                Token.NULL,
                Token.PLUS, 
                Token.TIMES,
                Token.VARIABLE);
        
        switch (nextToken()) {
            case OPENING_ROUND_BRACKET :
                accept(Token.OPENING_ROUND_BRACKET);
                Expression result = readItIn(context);      
                accept(Token.CLOSING_ROUND_BRACKET);
                return result;
             case LITERAL :
                return ConstantExpression.readOneIn();
            case MINUS :
            case PLUS :
            case TIMES :
                return ArithmeticExpression.readOneIn(context);
            case VARIABLE :
                accept(Token.VARIABLE);
                return VariableExpression.readOneIn(context); 
            default : assert false; 
        }
        
        return null;
    }
        
    //::::::::::::::::::::::::::: Translating from isablle to sal

    abstract void mustBeInteger() throws IsabelleException, FileException;
    
    //::::::::::::::::::::::::::: Output as SAL
    
    abstract void outputAsSAL(boolean withSome)throws IsabelleException, FileException ;

    //::::::::::::::::::::::::::: Output as Dot
    
    abstract String toDot();

}//Expression

class ArithmeticExpression extends Expression {    
            
    //::::::::::::::::::::::::::: The Internal Representation
    
    private Expression left, right;
    private Token op;
    
    private ArithmeticExpression (Expression l, Token o, Expression r)  {
        super(Type.ISABELLE_INTEGER_AS_INTEGER);
        left = l;
        op = o;
        right = r;
    }
    
    //::::::::::::::::::::::::::: Creation from Isobelle Source code
           
    static ArithmeticExpression readOneIn(Object context) throws IsabelleException, FileException  {
        Token t = acceptedToken();  
        assert t==Token.PLUS || t==Token.MINUS || t==Token.TIMES;
        nextTokenMustBe(Token.OPENING_ROUND_BRACKET);
        Expression l = Expression.readItIn(context);
        l.mustBeInteger();
        nextTokenMustBe(Token.OPENING_ROUND_BRACKET);
        Expression r = Expression.readItIn(context);
        r.mustBeInteger();
        return new ArithmeticExpression(l, t, r);
    }
    
    //::::::::::::::::::::::::::: Translating from isablle to sal

    @Override public void mustBeInteger()  { }
    
    //::::::::::::::::::::::::::: Output as SAL
    
    @Override void outputAsSAL(boolean withSome)throws IsabelleException, FileException  {  
        outputSAL(op, Token.OPENING_ROUND_BRACKET);
        left.outputAsSAL(withSome || left instanceof VariableExpression);  
        outputSAL(Token.COMMA);
        right.outputAsSAL(withSome || right instanceof VariableExpression );  
        outputSAL(Token.CLOSING_ROUND_BRACKET);      
    }
    
    //::::::::::::::::::::::::::: Output as Dot
    
    @Override String toDot() {
       switch (  op  )  {
            case PLUS:
                return left.toDot() + " + " + right.toDot();
            case MINUS :
                return left.toDot() + " - " + right.toDot();
            case TIMES :
                return left.toDot() + " &times; " + right.toDot();
        }
        assert false:op;
        return null;
    }

}

class  ConstantExpression extends Expression {
    
    //::::::::::::::::::::::::::: The Internal Representation
    
    private Constant constant;
    
    static ConstantExpression of(Constant c) {
        return new ConstantExpression(c);
    }
    
    private ConstantExpression(Constant c)  {
        super(c.getType());      
        constant = c;
    }
    
    SystemConstant getState() {
        assert constant instanceof SystemConstant;
        assert constant.getType()==Type.STATE;
        return (SystemConstant)constant;
    }

    //::::::::::::::::::::::::::: Creation from Isobelle Source code
        
    public static ConstantExpression readOneIn()  throws IsabelleException, FileException {        
        accept(Token.LITERAL, Token.OPENING_ROUND_BRACKET);
        Constant c = Constant.readOneIn();
        accept(Token.CLOSING_ROUND_BRACKET); 
        return new ConstantExpression(c);
    }

    //::::::::::::::::::::::::::: Translating from isablle to sal

    @Override public void mustBeInteger() throws FileException, IsabelleException  {
        if  (  constant instanceof NumericConstant  )
            ((NumericConstant)constant).hasBeenUsedInArithmetic();
        else
            reportAnError("that should have been an integer");
    } 
        
    //::::::::::::::::::::::::::: Output as SAL
    
    @Override void outputAsSAL(boolean withSome)throws IsabelleException, FileException  {
        outputSALWithSomeIfNecessary(constant.useAsSAL(), withSome); 
    }
    
    //::::::::::::::::::::::::::: Output as Dot
    
    @Override String toDot() {
        return constant.toDot();  
    }
    
} //end of constant


final class OutputExpression extends Expression {
    
    //::::::::::::::::::::::::::: The Internal Representation
        
    List<Expression> outputs;
    
    void add(Expression e) {
        outputs.add(e);
    } 
    
    int size()  {  return outputs.size();  }

    OutputExpression ()  {
        super(null); 
        outputs = new ArrayList<>();     
    }
    
    //::::::::::::::::::::::::::: Translating from isablle to sal

    @Override public void mustBeInteger() throws IsabelleException  { 
        assert false;
    } 
        
    //::::::::::::::::::::::::::: Output as SAL
    
    @Override void outputAsSAL(boolean withSome)throws IsabelleException, FileException   {  
        for (Expression e : outputs) {
            IOVariable.THE_OUTPUT_VARIABLE.startExplicitSequence();
            assert e != null;
            e.outputAsSAL(withSome ||  e instanceof VariableExpression  );  
            outputSAL(Token.COMMA);
        } 
        IOVariable.THE_OUTPUT_VARIABLE.finishExplicitSequence(outputs.size());
    }    

    //::::::::::::::::::::::::::: Output as Dot
    
    @Override String toDot() {
       String result = "";
       for(int i=0; i<outputs.size(); i++) {
           result += (
                   IOVariable.THE_OUTPUT_VARIABLE.getIdentifier().toLowerCase()+
                   "<sub>" + (i+1) + 
                   "</sub> := "+outputs.get(i).toDot());
           if  (  i < outputs.size()-1 )
               result +=", ";
       }
       return result;
    }
    
}

final class OverflowExpression extends Expression {
    
    //::::::::::::::::::::::::::: The Internal Representation
    
    Expression operand;
    
    OverflowExpression(Expression e) {
        super(null);
        operand = e;
    }
    
    //::::::::::::::::::::::::::: Translating from isablle to sal

    @Override public void mustBeInteger() throws IsabelleException  { 
        assert false;
    } 
            
    //::::::::::::::::::::::::::: Output as SAL
    
    @Override void outputAsSAL(boolean withSome) throws IsabelleException, FileException   {
        outputSAL("check_overflow", Token.OPENING_ROUND_BRACKET);
        operand.outputAsSAL(true);
        outputSAL(Token.CLOSING_ROUND_BRACKET, Token.AND,
                "check_underflow", Token.OPENING_ROUND_BRACKET);
        operand.outputAsSAL(true);
        outputSAL(Token.CLOSING_ROUND_BRACKET);
    }
    
    //::::::::::::::::::::::::::: Output as Dot
    
    @Override String toDot() {
          return operand.toDot() + " &le;  n"+SAL.SYSTEM_MARKER +
                  " &amp; " +
                  operand.toDot() + " &ge; -n"+SAL.SYSTEM_MARKER;
    }
    
}

final class  VariableExpression extends Expression {
    
    //::::::::::::::::::::::::::: The Internal Representation
    
    static VariableExpression of(Variable v)  {
        return new VariableExpression(v);
    }
        
    private Variable variable;
    Variable getVariable() {   return variable;   }
    
    private VariableExpression(Variable v)  {
        super(v.getType());
        variable = v;
    }

    //::::::::::::::::::::::::::: Creation from Isobelle Source code
           
    public static VariableExpression readOneIn(Object context)  throws IsabelleException, FileException {
        return new VariableExpression(Variable.readInName(context));
    }
    
    //::::::::::::::::::::::::::: Translating from isablle to sal

    @Override public void mustBeInteger() throws IsabelleException, FileException  {
        variable.makeInteger();
    }
            
    //::::::::::::::::::::::::::: Output as SAL
    
    @Override void outputAsSAL(boolean withSome) throws IsabelleException, FileException{  
        variable.outputAsSAL(withSome);
    }

    //::::::::::::::::::::::::::: Output as Dot
    
    @Override String toDot() {
        return variable.toDot();
    }
    
} //end of variable

