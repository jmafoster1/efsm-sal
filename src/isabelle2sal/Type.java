package isabelle2sal;
import static isabelle2sal.Generator.*;
import java.util.List;

/**
 * All sorts of types
 * @author Siobhan
 */

public enum Type  {
    //Internal type representations
    BOOLEAN, //for completeness like nipples on a man
    LABEL,
    STATE,
    STRING,
    BOUNDED_INT,
    VALUE,  //Undefined free variables
    
    //Original type representations from Isabelle
    ISABELLE_INTEGER_AS_INTEGER,  
    ISABELLE_INTEGER_AS_STRING,
    ISABELLE_STRING;
    
    //::::::::::::::::::::::::::: Output as SAL
    
    void outputDefinitionInSALIncluding(List<SystemConstant> values) throws IsabelleException, FileException  {
        outputSAL(
            this.name(),
            Token.COLON, 
            Token.TYPE, 
            Token.EQUALS);
        
        boolean first = true;
        if  (  this == LABEL  )  {
            outputSALLine(
                    Token.DATATYPE);
            increaseMarginOnSALOutput();
                for (SystemConstant c : values) {                  
                    if  (  first )  first = false;
                    else  outputSALLine(Token.COMMA);                    
                    outputSAL(c.useAsSAL());
                }
            outputNewLineInSAL();
            decreaseMarginOnSALOutput();
            outputSAL(Token.END);
        }
        else    {   
            for (SystemConstant c : values) {
                outputSAL( 
                        ( first ? Token.OPENING_CURLY_BRACKET : Token.COMMA),
                        c.getIdentifier());
                first = false;
            } 
            outputSAL(Token.CLOSING_CURLY_BRACKET); 
        }
        
        outputSALLine(Token.SEMICOLON);
        outputNewLineInSAL();
    }
                       
} 

