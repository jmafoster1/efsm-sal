package isabelle2sal;

import static isabelle2sal.Generator.*;

/**
 * Deals with assignments in various contexts
 * @author Siobhan
 */
public class Assignment {
    
    //::::::::::::::::::::::::::: The Internal Representation
    
    public static Assignment newOne(Variable v, SystemConstant c)  {   
        return new Assignment(v, ConstantExpression.of(c));
    }
       
    public static Assignment newOne(Variable v, Expression e)  { 
        assert v != null;
        return new Assignment(v, e);        
    }
    
    public static Assignment newOne(IOVariable v)  {   
        return new Assignment(v, null);        
    }
    
    private Variable variable;
    private Expression value;
    Expression getValue() {  return value;  }
    
    private Assignment(Variable l, Expression r) {
        variable = l;
        value = r;
    }    
            
    //::::::::::::::::::::::::::: Output as SAL
    
    void outputAsSAL() throws IsabelleException, FileException {  
        if  (  variable instanceof IOVariable   )  {
            outputSAL(
                    "gval", 
                    Token.OPENING_ROUND_BRACKET,
                    Token.EQUALS_PREFIX, 
                    Token.OPENING_ROUND_BRACKET);
            outputSALWithSome(variable);  
            outputSAL(Token.COMMA);                   
            value.outputAsSAL(false);
            outputSAL(Token.CLOSING_ROUND_BRACKET,
                    Token.CLOSING_ROUND_BRACKET);
        }
        else {
            variable.outputAsSAL(false);  
            outputSAL(Token.EQUALS);
            value.outputAsSAL(false);
        }   
    }
        
    public void updateOutputAsSAL(boolean last) throws IsabelleException, FileException {
        variable.outputAsSAL(false);//So with no Some
        outputSAL(Token.PRIME, Token.EQUALS);
        if  (  value == null  )
            outputSAL(((IOVariable)variable).nullValueInSAL());  //Output for the sink hole
        else
            value.outputAsSAL( ! ( variable instanceof SystemVariable )  );
        if  (  ! last  )
            outputSAL(Token.SEMICOLON);
        outputNewLineInSAL();
    }
            
    //::::::::::::::::::::::::::: Output as Dot
    
    public String outputOutputsAsDot()  {
        if  (  variable==IOVariable.THE_OUTPUT_VARIABLE && value != null  ) 
            return value.toDot()+ ", ";
        else return "";                
    }
    
    public String outputRegistersAsDot()  {
        if  (  variable instanceof RegisterVariable  )               
            return variable.toDot() + " := " + value.toDot() + ", ";                    
        else 
            return "";
    }
    
}
